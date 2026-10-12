import Mettapedia.Languages.C11.EffectiveTypes
import Mettapedia.Languages.C11.IntegerMemory
import Mettapedia.Languages.C11.Sequencing

/-!
# Whole-object integer lvalues connected to byte storage

An object identity retains its allocation lifetime, byte origin and extent.
Changing an access view preserves that identity. The catalog stores the
declared/effective type and object qualifiers independently of each lvalue.
Thus casting away const on a view cannot grant permission to modify a
declared const object. Ending the allocation lifetime prevents byte access.

The pure integer profile checks the source integer type against its admitted
value/representation layout, object extent, alignment, effective type and
qualifiers before using the independently specified byte-memory rules.
Volatile accesses need interaction requests; they are outside this pure
profile. Non-character stores establish allocated-object effective types.

Identities here describe complete admitted objects. Source construction of
nonoverlapping object regions, subobjects, union overlaps, pointer provenance
and character views of part of an object remains separate. The catalog is
not an authentication of a C declaration or committed host memory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ObjectAccessMemory

open AccessTypes ByteRanges ByteStorageData
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra

abbrev Identity := Range

structure Lvalue where
  object : Identity
  view : AccessTypes.View
  deriving DecidableEq, Repr

def Lvalue.cast (location : Lvalue) (view : AccessTypes.View) : Lvalue := ⟨location.object, view⟩

def Lvalue.readEvent (location : Lvalue) : Sequencing.Access Identity := .readValue location.object
def Lvalue.writeEvent (location : Lvalue) : Sequencing.Access Identity := .modify location.object

theorem cast_preserves_identity (location : Lvalue) (view : AccessTypes.View) :
    (location.cast view).object = location.object := rfl

theorem cast_alias_conflict (location : Lvalue) (first second : AccessTypes.View) :
    Sequencing.Conflict (location.cast first).writeEvent (location.cast second).readEvent :=
  .modifyRead location.object

structure Record where
  info : EffectiveTypes.Info
  qualifiers : Qualifiers := {}
  alignment : Nat
  deriving DecidableEq, Repr

def declaredRecord (type : AccessTypes.View) (alignment : Nat) : Record :=
  ⟨⟨some type.type, none⟩, type.qualifiers, alignment⟩

def allocatedRecord (alignment : Nat) : Record := ⟨{}, {}, alignment⟩

abbrev Catalog := List (Identity × Record)

structure Layout where
  parameters : IntegerTypeParameters IntegerExtension
  sourceType : IntegerType IntegerExtension
  representation : IntegerObject.Profile
  format : representation.integer = sourceType.format parameters

structure State (characters : ByteStorageData.Profile) where
  storage : Storage.State (Byte characters)
  catalog : Catalog
  deriving DecidableEq, Repr

structure SemanticState (characters : ByteStorageData.Profile) where
  memory : Heap (Excl (Option (Byte characters)))
  catalog : Catalog

def represent {characters : ByteStorageData.Profile} (state : State characters) : SemanticState characters :=
  ⟨ByteRanges.heap state.storage, state.catalog⟩

def integerView : ObjectType → Option (IntegerType IntegerExtension)
  | .scalar (.integer type) => some type
  | _ => none

theorem integerView_iff (view : ObjectType) (type : IntegerType IntegerExtension) :
    integerView view = some type ↔ view = .scalar (.integer type) := by
  cases view with
  | scalar atom => cases atom <;> simp [integerView]
  | array => simp [integerView]
  | aggregate => simp [integerView]

def PureView (layout : Layout) (record : Record) (location : Lvalue) : Prop :=
  integerView location.view.type = some layout.sourceType ∧
    location.object.extent = layout.representation.byteCount ∧ 0 < record.alignment ∧
    location.object.address.offset % record.alignment = 0 ∧
    location.view.qualifiers.volatile = false ∧ record.qualifiers.volatile = false

instance (layout : Layout) (record : Record) (location : Lvalue) : Decidable (PureView layout record location) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def Writable (record : Record) (location : Lvalue) : Prop :=
  location.view.qualifiers.const = false ∧ record.qualifiers.const = false

instance (record : Record) (location : Lvalue) : Decidable (Writable record location) :=
  inferInstanceAs (Decidable (_ ∧ _))

def read (layout : Layout) (state : State layout.representation.characters) (location : Lvalue) :
    Option IntegerObject.Outcome := do
  let record ← state.catalog.lookup location.object
  if PureView layout record location then
    let _ ← EffectiveTypes.admitRead record.info location.view.type
    IntegerMemory.readInteger layout.representation state.storage location.object.address
  else none

def Reading (layout : Layout) (state : SemanticState layout.representation.characters)
    (location : Lvalue) (outcome : IntegerObject.Outcome) : Prop :=
  ∃ record type, state.catalog.lookup location.object = some record ∧ PureView layout record location ∧
    EffectiveTypes.ReadPermission record.info location.view.type type ∧
    IntegerMemory.Reading layout.representation state.memory location.object.address outcome

theorem read_sound (layout : Layout) (state : State layout.representation.characters)
    (location : Lvalue) (outcome : IntegerObject.Outcome) (executed : read layout state location = some outcome) :
    Reading layout (represent state) location outcome := by
  cases found : state.catalog.lookup location.object with
  | none => simp [read, found] at executed
  | some record =>
      by_cases pure : PureView layout record location
      · cases admitted : EffectiveTypes.admitRead record.info location.view.type with
        | none => simp [read, found, pure, admitted] at executed
        | some type =>
            refine ⟨record, type, found, pure, (EffectiveTypes.admitRead_iff _ _ _).mp admitted, ?_⟩
            exact IntegerMemory.readInteger_sound _ _ _ _ (by simpa [read, found, pure, admitted] using executed)
      · simp [read, found, pure] at executed

theorem read_complete (layout : Layout) (state : State layout.representation.characters)
    (location : Lvalue) (outcome : IntegerObject.Outcome) (reading : Reading layout (represent state) location outcome) :
    read layout state location = some outcome := by
  obtain ⟨record, type, found, pure, permission, observed⟩ := reading
  change state.catalog.lookup location.object = some record at found
  have admitted := (EffectiveTypes.admitRead_iff _ _ _).mpr permission
  have result := IntegerMemory.readInteger_complete _ _ _ _ observed
  simp [read, found, pure, admitted, result]

theorem read_iff (layout : Layout) (state : State layout.representation.characters)
    (location : Lvalue) (outcome : IntegerObject.Outcome) :
    read layout state location = some outcome ↔ Reading layout (represent state) location outcome :=
  ⟨read_sound layout state location outcome, read_complete layout state location outcome⟩

def store (layout : Layout) (state : State layout.representation.characters) (location : Lvalue)
    (value : IntegerValue layout.representation.integer) : Option (State layout.representation.characters) := do
  let record ← state.catalog.lookup location.object
  if PureView layout record location ∧ Writable record location then
    let typed ← EffectiveTypes.admitStore record.info location.view.type
    let storage ← IntegerMemory.storeInteger layout.representation state.storage location.object.address value
    some ⟨storage, (location.object, {record with info := typed.2}) :: state.catalog⟩
  else none

def Writing (layout : Layout) (before after : SemanticState layout.representation.characters)
    (location : Lvalue) (value : IntegerValue layout.representation.integer) : Prop :=
  ∃ record type info, before.catalog.lookup location.object = some record ∧
    PureView layout record location ∧ Writable record location ∧
    EffectiveTypes.StorePermission record.info location.view.type type info ∧
    IntegerMemory.Writing layout.representation before.memory after.memory location.object.address value ∧
    after.catalog = (location.object, {record with info := info}) :: before.catalog

theorem store_sound (layout : Layout) (state saved : State layout.representation.characters)
    (location : Lvalue) (value : IntegerValue layout.representation.integer)
    (executed : store layout state location value = some saved) :
    Writing layout (represent state) (represent saved) location value := by
  cases found : state.catalog.lookup location.object with
  | none => simp [store, found] at executed
  | some record =>
      by_cases valid : PureView layout record location ∧ Writable record location
      · cases admitted : EffectiveTypes.admitStore record.info location.view.type with
        | none => simp [store, found, valid, admitted] at executed
        | some typed =>
            cases written : IntegerMemory.storeInteger layout.representation state.storage location.object.address value with
            | none => simp [store, found, written] at executed
            | some storage =>
                simp [store, found, valid, admitted, written] at executed
                subst saved
                exact ⟨record, typed.1, typed.2, found, valid.1, valid.2,
                  (EffectiveTypes.admitStore_iff _ _ _ _).mp admitted,
                  IntegerMemory.storeInteger_sound _ _ _ _ _ written, rfl⟩
      · simp [store, found, valid] at executed

theorem store_complete (layout : Layout) (state : State layout.representation.characters)
    (after : SemanticState layout.representation.characters) (location : Lvalue)
    (value : IntegerValue layout.representation.integer) (writing : Writing layout (represent state) after location value) :
    ∃ saved, store layout state location value = some saved ∧ represent saved = after := by
  obtain ⟨record, type, info, found, pure, writable, permission, writing, catalog⟩ := writing
  change state.catalog.lookup location.object = some record at found
  obtain ⟨storage, written, memory⟩ := IntegerMemory.storeInteger_complete _ _ _ _ _ writing
  have admitted := (EffectiveTypes.admitStore_iff _ _ _ _).mpr permission
  refine ⟨⟨storage, (location.object, {record with info := info}) :: state.catalog⟩, ?_, ?_⟩
  · simp [store, found, pure, writable, admitted, written]
  · cases after
    simp_all only [represent]

theorem read_after_store (layout : Layout) (state saved : State layout.representation.characters)
    (location : Lvalue) (value : IntegerValue layout.representation.integer)
    (executed : store layout state location value = some saved) :
    read layout saved location = some (.integer (.value value.value false)) := by
  cases found : state.catalog.lookup location.object with
  | none => simp [store, found] at executed
  | some record =>
      by_cases valid : PureView layout record location ∧ Writable record location
      · cases admitted : EffectiveTypes.admitStore record.info location.view.type with
        | none => simp [store, found, valid, admitted] at executed
        | some typed =>
            cases written : IntegerMemory.storeInteger layout.representation state.storage location.object.address value with
            | none => simp [store, found, written] at executed
            | some storage =>
                simp [store, found, valid, admitted, written] at executed
                subst saved
                have permission := (EffectiveTypes.admitStore_iff _ _ _ _).mp admitted
                have readable := (EffectiveTypes.admitRead_iff _ _ _).mpr
                  (EffectiveTypes.store_read_permission permission)
                have result := IntegerMemory.read_after_store _ _ _ _ _ written
                have pure : PureView layout {record with info := typed.2} location := valid.1
                simp [read, List.lookup, pure, readable, result]
      · simp [store, found, valid] at executed

end Mettapedia.Languages.C11.ObjectAccessMemory
