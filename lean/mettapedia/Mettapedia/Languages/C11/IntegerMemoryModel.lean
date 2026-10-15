import Mettapedia.Languages.C11.ObjectStores
import Mettapedia.Languages.C11.IntegerScalar
import Mettapedia.Languages.C11.IntegerStep

/-!
# Heterogeneous integer object layouts over one byte memory

Each canonical integer type selects its own checked object size, byte order
and representation policy. All layouts share the value parameters and the
character representation of the retained memory. Reads inspect the lvalue's
type and preserve that type and the raw representation observation. Stores
require a value already converted to the destination type; they cannot
silently reinterpret an unrelated typed value as an assignment conversion.

The independent judgments join the existing typed access and owned byte-memory
rules. Soundness and constructive completeness cover every layout family,
memory and location admitted by those rules. Source type construction,
subobject/character accesses, volatile interaction and host effect authority
remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerMemoryModel

open ObjectAccessMemory
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

structure ObjectFormat (parameters : IntegerTypeParameters IntegerExtension)
    (characters : ByteStorageData.Profile) (type : IntegerType IntegerExtension) where
  byteCount : Nat
  positiveExtent : 0 < byteCount
  fits : IntegerBits.width (type.format parameters) ≤ characters.charBits * byteCount
  order : BytePacking.Order
  negativeZero : IntegerBits.NegativeZero
  padding : IntegerObject.Padding

abbrev ObjectFormat.representation {parameters : IntegerTypeParameters IntegerExtension}
    {characters : ByteStorageData.Profile} {type : IntegerType IntegerExtension}
    (format : ObjectFormat parameters characters type) : IntegerObject.Profile :=
  ⟨characters, type.format parameters, format.byteCount, format.positiveExtent,
    format.fits, format.order, format.negativeZero, format.padding⟩

structure Model where
  parameters : IntegerTypeParameters IntegerExtension
  characters : ByteStorageData.Profile
  objects : (type : IntegerType IntegerExtension) → ObjectFormat parameters characters type

abbrev Model.layout (model : Model) (type : IntegerType IntegerExtension) : Layout :=
  ⟨model.parameters, type, (model.objects type).representation, rfl⟩

def read (model : Model) (memory : State model.characters) (location : Lvalue) :
    Option (IntegerType IntegerExtension × IntegerObject.Outcome) := do
  let type ← integerView location.view.type
  let outcome ← ObjectAccessMemory.read (model.layout type) memory location
  some (type, outcome)

def Reading (model : Model) (memory : SemanticState model.characters) (location : Lvalue)
    (type : IntegerType IntegerExtension) (outcome : IntegerObject.Outcome) : Prop :=
  location.view.type = .scalar (.integer type) ∧
    ObjectAccessMemory.Reading (model.layout type) memory location outcome

theorem read_sound (model : Model) (memory : State model.characters) (location : Lvalue)
    (type : IntegerType IntegerExtension) (outcome : IntegerObject.Outcome)
    (executed : read model memory location = some (type, outcome)) :
    Reading model (represent memory) location type outcome := by
  simp only [read, bind, Option.bind_eq_some_iff, Option.some.injEq] at executed
  obtain ⟨selected, selectedType, observed, observedRead, same⟩ := executed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨(integerView_iff _ _).mp selectedType, ObjectAccessMemory.read_sound _ _ _ _ observedRead⟩

theorem read_complete (model : Model) (memory : State model.characters) (location : Lvalue)
    (type : IntegerType IntegerExtension) (outcome : IntegerObject.Outcome)
    (reading : Reading model (represent memory) location type outcome) :
    read model memory location = some (type, outcome) := by
  have selected := (integerView_iff _ _).mpr reading.1
  have observed := ObjectAccessMemory.read_complete _ _ _ _ reading.2
  simp only [read, selected, observed, bind, Option.bind_some]

theorem read_iff (model : Model) (memory : State model.characters) (location : Lvalue)
    (type : IntegerType IntegerExtension) (outcome : IntegerObject.Outcome) :
    read model memory location = some (type, outcome) ↔ Reading model (represent memory) location type outcome :=
  ⟨read_sound model memory location type outcome, read_complete model memory location type outcome⟩

theorem Reading.value_range (model : Model) (memory : SemanticState model.characters)
    (location : Lvalue) (type : IntegerType IntegerExtension) (value : Int) (negativeZero : Bool)
    (reading : Reading model memory location type (.integer (.value value negativeZero))) :
    (type.format model.parameters).Represents value := by
  obtain ⟨_, _, _, _, _, bytes, _, interpreted⟩ := reading.2
  cases interpreted with
  | integer _ _ _ _ integer =>
      exact IntegerBits.Reading.value_in_range _ _ _ _ integer value negativeZero rfl

inductive Loaded (model : Model) where
  | value (scalar : IntegerScalar.Value model.parameters) (negativeZero : Bool)
  | trap (type : IntegerType IntegerExtension) (reason : IntegerBits.Trap)
  | paddingTrap (type : IntegerType IntegerExtension)
  deriving DecidableEq, Repr

inductive Interpretation (model : Model) :
    IntegerType IntegerExtension → IntegerObject.Outcome → Loaded model → Prop where
  | value (scalar : IntegerScalar.Value model.parameters) (negativeZero : Bool) :
      Interpretation model scalar.type (.integer (.value scalar.integer.value negativeZero)) (.value scalar negativeZero)
  | trap (type : IntegerType IntegerExtension) (reason : IntegerBits.Trap) :
      Interpretation model type (.integer (.trap reason)) (.trap type reason)
  | paddingTrap (type : IntegerType IntegerExtension) :
      Interpretation model type .paddingTrap (.paddingTrap type)

def interpret (model : Model) (type : IntegerType IntegerExtension) : IntegerObject.Outcome → Option (Loaded model)
  | .integer (.value value negativeZero) =>
      (IntegerStep.decodeValue (type.format model.parameters) value).map (fun integer => .value ⟨type, integer⟩ negativeZero)
  | .integer (.trap reason) => some (.trap type reason)
  | .paddingTrap => some (.paddingTrap type)

theorem interpret_sound (model : Model) (type : IntegerType IntegerExtension)
    (outcome : IntegerObject.Outcome) (loaded : Loaded model)
    (computed : interpret model type outcome = some loaded) : Interpretation model type outcome loaded := by
  cases outcome with
  | paddingTrap => simp [interpret] at computed; subst loaded; exact .paddingTrap type
  | integer outcome =>
      cases outcome with
      | trap reason => simp [interpret] at computed; subst loaded; exact .trap type reason
      | value value negativeZero =>
          obtain ⟨integer, decoded, rfl⟩ := Option.map_eq_some_iff.mp computed
          have same := IntegerStep.value_decode _ value integer decoded
          rw [← same]
          exact .value ⟨type, integer⟩ negativeZero

theorem interpret_complete (model : Model) (type : IntegerType IntegerExtension)
    (outcome : IntegerObject.Outcome) (loaded : Loaded model)
    (interpreted : Interpretation model type outcome loaded) : interpret model type outcome = some loaded := by
  cases interpreted with
  | value scalar negativeZero =>
      cases scalar
      simp only [interpret, IntegerStep.decodeValue_encode, Option.map_some]
  | trap type reason => rfl
  | paddingTrap type => rfl

theorem interpretation_exists (model : Model) (memory : SemanticState model.characters)
    (location : Lvalue) (type : IntegerType IntegerExtension) (outcome : IntegerObject.Outcome)
    (reading : Reading model memory location type outcome) :
    ∃ loaded, Interpretation model type outcome loaded := by
  cases outcome with
  | paddingTrap => exact ⟨_, .paddingTrap type⟩
  | integer outcome =>
      cases outcome with
      | trap reason => exact ⟨_, .trap type reason⟩
      | value value negativeZero =>
          exact ⟨_, .value ⟨type, ⟨value, Reading.value_range _ _ _ _ _ _ reading⟩⟩ negativeZero⟩

def load (model : Model) (memory : State model.characters) (location : Lvalue) : Option (Loaded model) := do
  let observed ← read model memory location
  interpret model observed.1 observed.2

def Loading (model : Model) (memory : SemanticState model.characters) (location : Lvalue)
    (loaded : Loaded model) : Prop :=
  ∃ type outcome, Reading model memory location type outcome ∧ Interpretation model type outcome loaded

theorem load_sound (model : Model) (memory : State model.characters) (location : Lvalue)
    (loaded : Loaded model) (executed : load model memory location = some loaded) :
    Loading model (represent memory) location loaded := by
  obtain ⟨⟨type, outcome⟩, observed, interpreted⟩ := Option.bind_eq_some_iff.mp executed
  exact ⟨type, outcome, read_sound _ _ _ _ _ observed, interpret_sound _ _ _ _ interpreted⟩

theorem load_complete (model : Model) (memory : State model.characters) (location : Lvalue)
    (loaded : Loaded model) (loading : Loading model (represent memory) location loaded) :
    load model memory location = some loaded := by
  obtain ⟨type, outcome, reading, interpreted⟩ := loading
  simp only [load, read_complete _ _ _ _ _ reading, interpret_complete _ _ _ _ interpreted, bind, Option.bind_some]

theorem load_iff (model : Model) (memory : State model.characters) (location : Lvalue) (loaded : Loaded model) :
    load model memory location = some loaded ↔ Loading model (represent memory) location loaded :=
  ⟨load_sound model memory location loaded, load_complete model memory location loaded⟩

theorem reading_loads (model : Model) (memory : State model.characters) (location : Lvalue)
    (type : IntegerType IntegerExtension) (outcome : IntegerObject.Outcome)
    (reading : Reading model (represent memory) location type outcome) :
    ∃ loaded, load model memory location = some loaded := by
  obtain ⟨loaded, interpreted⟩ := interpretation_exists _ _ _ _ _ reading
  exact ⟨loaded, load_complete _ _ _ _ ⟨type, outcome, reading, interpreted⟩⟩

def store (model : Model) (memory : State model.characters) (location : Lvalue)
    (scalar : IntegerScalar.Value model.parameters) : Option (State model.characters) :=
  if location.view.type = .scalar (.integer scalar.type) then
    ObjectStores.store (model.layout scalar.type) memory location scalar.integer
  else none

def Writing (model : Model) (before after : SemanticState model.characters) (location : Lvalue)
    (scalar : IntegerScalar.Value model.parameters) : Prop :=
  location.view.type = .scalar (.integer scalar.type) ∧
    ObjectStores.Writing (model.layout scalar.type) before after location scalar.integer

theorem store_sound (model : Model) (before after : State model.characters) (location : Lvalue)
    (scalar : IntegerScalar.Value model.parameters)
    (written : store model before location scalar = some after) :
    Writing model (represent before) (represent after) location scalar := by
  by_cases same : location.view.type = .scalar (.integer scalar.type)
  · simp only [store, same, ↓reduceIte] at written
    exact ⟨same, ObjectStores.store_sound _ _ _ _ _ written⟩
  · simp only [store, same, ↓reduceIte, reduceCtorEq] at written

theorem store_complete (model : Model) (before : State model.characters)
    (after : SemanticState model.characters) (location : Lvalue) (scalar : IntegerScalar.Value model.parameters)
    (writing : Writing model (represent before) after location scalar) :
    ∃ saved, store model before location scalar = some saved ∧ represent saved = after := by
  obtain ⟨saved, written, represented⟩ := ObjectStores.store_complete _ _ _ _ _ writing.2
  exact ⟨saved, by rw [store, if_pos writing.1]; exact written, represented⟩

theorem store_wrong_type (model : Model) (memory : State model.characters) (location : Lvalue)
    (scalar : IntegerScalar.Value model.parameters)
    (different : location.view.type ≠ .scalar (.integer scalar.type)) : store model memory location scalar = none := by
  simp only [store, different, ↓reduceIte]

theorem read_after_store (model : Model) (before after : State model.characters) (location : Lvalue)
    (scalar : IntegerScalar.Value model.parameters) (written : store model before location scalar = some after) :
    read model after location = some (scalar.type, .integer (.value scalar.integer.value false)) := by
  have same := (store_sound _ _ _ _ _ written).1
  have stored : ObjectStores.store (model.layout scalar.type) before location scalar.integer = some after := by
    simpa only [store, same, ↓reduceIte] using written
  have observed := ObjectStores.read_after_store _ _ _ _ _ stored
  simp only [read, (integerView_iff _ _).mpr same, observed, bind, Option.bind_some]

theorem load_after_store (model : Model) (before after : State model.characters) (location : Lvalue)
    (scalar : IntegerScalar.Value model.parameters) (written : store model before location scalar = some after) :
    load model after location = some (.value scalar false) := by
  simp only [load, read_after_store _ _ _ _ _ written, bind, Option.bind_some]
  exact interpret_complete _ _ _ _ (.value scalar false)

theorem Reading.frame (model : Model) (memory : SemanticState model.characters)
    (frame : Heap (Excl (Option (ByteStorageData.Byte model.characters)))) (location : Lvalue)
    (type : IntegerType IntegerExtension) (outcome : IntegerObject.Outcome)
    (reading : Reading model memory location type outcome) (separate : memory.memory ## frame) :
    Reading model ⟨memory.memory + frame, memory.catalog⟩ location type outcome := by
  obtain ⟨same, record, selectedType, found, pure, permitted, read⟩ := reading
  exact ⟨same, record, selectedType, found, pure, permitted, IntegerMemory.Reading.frame _ _ _ _ _ read separate⟩

theorem Loading.frame (model : Model) (memory : SemanticState model.characters)
    (frame : Heap (Excl (Option (ByteStorageData.Byte model.characters)))) (location : Lvalue) (loaded : Loaded model)
    (loading : Loading model memory location loaded) (separate : memory.memory ## frame) :
    Loading model ⟨memory.memory + frame, memory.catalog⟩ location loaded := by
  obtain ⟨type, outcome, read, interpreted⟩ := loading
  exact ⟨type, outcome, Reading.frame _ _ _ _ _ _ read separate, interpreted⟩

theorem Writing.frame (model : Model) (before after : SemanticState model.characters)
    (frame : Heap (Excl (Option (ByteStorageData.Byte model.characters)))) (location : Lvalue)
    (scalar : IntegerScalar.Value model.parameters) (writing : Writing model before after location scalar)
    (separate : before.memory ## frame) :
    Writing model ⟨before.memory + frame, before.catalog⟩ ⟨after.memory + frame, after.catalog⟩ location scalar ∧
      after.memory ## frame := by
  obtain ⟨framed, retained⟩ := ObjectStores.Writing.frame _ _ _ _ _ _ writing.2 separate
  exact ⟨⟨writing.1, framed⟩, retained⟩

end Mettapedia.Languages.C11.IntegerMemoryModel
