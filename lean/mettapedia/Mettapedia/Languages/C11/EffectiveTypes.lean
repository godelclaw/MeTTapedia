import Mettapedia.Languages.C11.AccessTypes

/-!
# Effective types for completed object accesses

Declared types take precedence over retained types. A non-character store
into an object without a declared type establishes the store's type for
subsequent nonmodifying accesses. Reading an untyped object selects the
lvalue type for that access without establishing a persistent type.

The copy transition describes complete object representations, using the
source object's retained or declared type. Partial copies, overlapping
object regions, character stores and temporary objects need additional
memory/source rules. A type transfer alone is not a memory-copy judgment.
Access permission and effective-type selection have independent rule
constructors and executable selectors.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.EffectiveTypes

open AccessTypes

structure Info where
  declared : Option ObjectType := none
  retained : Option ObjectType := none
  deriving DecidableEq, Repr

def known (info : Info) : Option ObjectType := info.declared.orElse (fun _ => info.retained)

inductive ReadingType (info : Info) (view : ObjectType) : ObjectType → Prop where
  | declared (type : ObjectType) (present : info.declared = some type) : ReadingType info view type
  | retained (type : ObjectType) (untyped : info.declared = none)
      (present : info.retained = some type) : ReadingType info view type
  | access (untyped : info.declared = none) (fresh : info.retained = none) : ReadingType info view view

def readingType (info : Info) (view : ObjectType) : ObjectType := (known info).getD view

theorem readingType_sound (info : Info) (view : ObjectType) : ReadingType info view (readingType info view) := by
  cases declared : info.declared with
  | some type => simpa [readingType, known, declared] using @ReadingType.declared info view type declared
  | none =>
      cases retained : info.retained with
      | some type =>
          simpa [readingType, known, declared, retained] using @ReadingType.retained info view type declared retained
      | none =>
          simpa [readingType, known, declared, retained] using @ReadingType.access info view declared retained

theorem readingType_complete (info : Info) (view type : ObjectType) (reading : ReadingType info view type) :
    readingType info view = type := by
  cases reading with
  | declared type present => simp [readingType, known, present]
  | retained type untyped present => simp [readingType, known, untyped, present]
  | access untyped fresh => simp [readingType, known, untyped, fresh]

def admitRead (info : Info) (view : ObjectType) : Option ObjectType :=
  let type := readingType info view
  if permits view type then some type else none

def ReadPermission (info : Info) (view type : ObjectType) : Prop :=
  ReadingType info view type ∧ Permitted view type

theorem admitRead_iff (info : Info) (view type : ObjectType) :
    admitRead info view = some type ↔ ReadPermission info view type := by
  unfold admitRead
  by_cases permitted : permits view (readingType info view) = true
  · simp only [permitted, ↓reduceIte, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨readingType_sound info view, (permits_iff _ _).mp permitted⟩
    · rintro ⟨reading, _⟩
      exact readingType_complete info view type reading
  · simp only [permitted, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
    rintro ⟨reading, permission⟩
    exact permitted (by rw [readingType_complete info view type reading]; exact (permits_iff _ _).mpr permission)

inductive StorePermission (info : Info) (view : ObjectType) : ObjectType → Info → Prop where
  | declared (type : ObjectType) (present : info.declared = some type)
      (nonCharacter : character view = false) (permission : Permitted view type) :
      StorePermission info view type info
  | allocated (untyped : info.declared = none) (nonCharacter : character view = false) :
      StorePermission info view view ⟨none, some view⟩

def admitStore (info : Info) (view : ObjectType) : Option (ObjectType × Info) :=
  if character view then none
  else match info.declared with
    | some type => if permits view type then some (type, info) else none
    | none => some (view, ⟨none, some view⟩)

theorem admitStore_sound (info : Info) (view type : ObjectType) (saved : Info)
    (accepted : admitStore info view = some (type, saved)) : StorePermission info view type saved := by
  cases isCharacter : character view with
  | true => simp [admitStore, isCharacter] at accepted
  | false =>
      cases declared : info.declared with
      | none =>
          simp only [admitStore, isCharacter, Bool.false_eq_true, ↓reduceIte, declared, Option.some.injEq,
            Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact .allocated declared isCharacter
      | some actual =>
          cases permission : permits view actual with
          | false => simp [admitStore, isCharacter, declared, permission] at accepted
          | true =>
              simp only [admitStore, isCharacter, Bool.false_eq_true, ↓reduceIte, declared, permission,
                Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact .declared _ declared isCharacter ((permits_iff _ _).mp permission)

theorem admitStore_complete (info : Info) (view type : ObjectType) (saved : Info)
    (permission : StorePermission info view type saved) : admitStore info view = some (type, saved) := by
  cases permission with
  | declared type present nonCharacter permission =>
      simp [admitStore, nonCharacter, present, (permits_iff _ _).mpr permission]
  | allocated untyped nonCharacter => simp [admitStore, nonCharacter, untyped]

theorem admitStore_iff (info : Info) (view type : ObjectType) (saved : Info) :
    admitStore info view = some (type, saved) ↔ StorePermission info view type saved :=
  ⟨admitStore_sound info view type saved, admitStore_complete info view type saved⟩

theorem store_preserves_declared {info saved : Info} {view type : ObjectType}
    (stored : StorePermission info view type saved) : saved.declared = info.declared := by
  cases stored with
  | declared => rfl
  | allocated untyped _ => exact untyped.symm

theorem allocated_store_replaces_retained {info saved : Info} {view type : ObjectType}
    (stored : StorePermission info view type saved) (untyped : info.declared = none) :
    type = view ∧ saved.retained = some view := by
  cases stored with
  | declared _ present _ _ => rw [untyped] at present; cases present
  | allocated => exact ⟨rfl, rfl⟩

theorem store_read_permission {info saved : Info} {view type : ObjectType}
    (stored : StorePermission info view type saved) : ReadPermission saved view type := by
  cases stored with
  | declared type present nonCharacter permission => exact ⟨.declared type present, permission⟩
  | allocated untyped nonCharacter =>
      exact ⟨.retained view rfl rfl, .direct (Or.inl (Compatible.refl view))⟩

inductive CopyType (source target : Info) : Info → Prop where
  | declared (type : ObjectType) (present : target.declared = some type) : CopyType source target target
  | allocated (untyped : target.declared = none) : CopyType source target ⟨none, known source⟩

def copyType (source target : Info) : Info :=
  match target.declared with
  | some _ => target
  | none => ⟨none, known source⟩

theorem copyType_sound (source target : Info) : CopyType source target (copyType source target) := by
  cases declared : target.declared with
  | none => simpa [copyType, declared] using @CopyType.allocated source target declared
  | some type => simpa [copyType, declared] using @CopyType.declared source target type declared

theorem copyType_complete (source target saved : Info) (copied : CopyType source target saved) :
    copyType source target = saved := by
  cases copied with
  | declared type present => simp [copyType, present]
  | allocated untyped => simp [copyType, untyped]

theorem copy_preserves_declared {source target saved : Info} (copied : CopyType source target saved) :
    saved.declared = target.declared := by
  cases copied with
  | declared => rfl
  | allocated untyped => exact untyped.symm

end Mettapedia.Languages.C11.EffectiveTypes
