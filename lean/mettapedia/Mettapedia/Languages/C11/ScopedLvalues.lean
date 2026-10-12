import Mettapedia.Languages.C11.ObjectAccessMemory

/-!
# Scoped identifier lvalues and typed accesses

Frames retain source names, access types, qualifiers and complete object
identities. Resolution selects the first binding in the first applicable
frame. Independent binding and absence judgments account for every skipped
binding and frame. General lookup correspondence covers arbitrary finite
scope depth and shadowing.

Named reads and stores compose that resolution with the whole-object byte
memory judgments. Two names bound to views of the same object therefore
share its effective-type metadata and sequencing identity. This is the
identifier-lvalue connection; expression evaluation, parameter binding,
source declaration elaboration and the Cesta syntax adapter are additional
parts of the full source machine.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ScopedLvalues

open ObjectAccessMemory

abbrev Frame := List (String × Lvalue)
abbrev Environment := List Frame

inductive FrameBinding (name : String) : Frame → Lvalue → Prop where
  | here (location : Lvalue) (tail : Frame) : FrameBinding name ((name, location) :: tail) location
  | there (key : String) (location : Lvalue) (tail : Frame) (result : Lvalue)
      (different : name ≠ key) (bound : FrameBinding name tail result) :
      FrameBinding name ((key, location) :: tail) result

inductive FrameAbsent (name : String) : Frame → Prop where
  | empty : FrameAbsent name []
  | cons (key : String) (location : Lvalue) (tail : Frame) (different : name ≠ key)
      (absent : FrameAbsent name tail) : FrameAbsent name ((key, location) :: tail)

theorem lookup_frame_iff (frame : Frame) (name : String) (location : Lvalue) :
    frame.lookup name = some location ↔ FrameBinding name frame location := by
  induction frame with
  | nil => simp only [List.lookup_nil, reduceCtorEq]; constructor <;> intro h <;> cases h
  | cons head tail ih =>
      obtain ⟨key, value⟩ := head
      by_cases same : name = key
      · subst key
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq]
        constructor
        · rintro rfl; exact .here _ _
        · intro bound; cases bound with
          | here => rfl
          | there _ _ _ _ different _ => exact False.elim (different rfl)
      · have different : (name == key) = false := by simp [same]
        simp only [List.lookup, different, ih]
        constructor
        · exact FrameBinding.there key value tail location same
        · intro bound; cases bound with
          | here => exact False.elim (same rfl)
          | there _ _ _ _ _ bound => exact bound

theorem lookup_absent_iff (frame : Frame) (name : String) : frame.lookup name = none ↔ FrameAbsent name frame := by
  induction frame with
  | nil => exact ⟨fun _ => .empty, fun _ => rfl⟩
  | cons head tail ih =>
      obtain ⟨key, value⟩ := head
      by_cases same : name = key
      · subst key
        simp only [List.lookup, beq_self_eq_true, reduceCtorEq]
        constructor
        · intro impossible; cases impossible
        · intro absent; cases absent with
          | cons _ _ _ different _ => exact different rfl
      · have different : (name == key) = false := by simp [same]
        simp only [List.lookup, different, ih]
        constructor
        · exact FrameAbsent.cons key value tail same
        · intro absent; cases absent with
          | cons _ _ _ _ absent => exact absent

inductive Binding (name : String) : Environment → Lvalue → Prop where
  | here (frame : Frame) (tail : Environment) (location : Lvalue) (bound : FrameBinding name frame location) :
      Binding name (frame :: tail) location
  | there (frame : Frame) (tail : Environment) (location : Lvalue) (absent : FrameAbsent name frame)
      (bound : Binding name tail location) : Binding name (frame :: tail) location

def lookup (environment : Environment) (name : String) : Option Lvalue :=
  match environment with
  | [] => none
  | frame :: tail => (frame.lookup name).orElse (fun _ => lookup tail name)

theorem lookup_sound (environment : Environment) (name : String) (location : Lvalue)
    (found : lookup environment name = some location) : Binding name environment location := by
  induction environment with
  | nil => simp [lookup] at found
  | cons frame tail ih =>
      cases inFrame : frame.lookup name with
      | none =>
          exact .there frame tail location ((lookup_absent_iff _ _).mp inFrame)
            (ih (by simpa [lookup, inFrame] using found))
      | some value =>
          simp only [lookup, inFrame, Option.orElse_some, Option.some.injEq] at found
          subst location
          exact .here frame tail value ((lookup_frame_iff _ _ _).mp inFrame)

theorem lookup_complete (environment : Environment) (name : String) (location : Lvalue)
    (bound : Binding name environment location) : lookup environment name = some location := by
  induction bound with
  | here frame tail location bound => simp [lookup, (lookup_frame_iff _ _ _).mpr bound]
  | there frame tail location absent bound ih => simp [lookup, (lookup_absent_iff _ _).mpr absent, ih]

theorem lookup_iff (environment : Environment) (name : String) (location : Lvalue) :
    lookup environment name = some location ↔ Binding name environment location :=
  ⟨lookup_sound environment name location, lookup_complete environment name location⟩

def read (layout : Layout) (state : State layout.representation.characters)
    (environment : Environment) (name : String) : Option IntegerObject.Outcome := do
  let location ← lookup environment name
  ObjectAccessMemory.read layout state location

def Reading (layout : Layout) (state : SemanticState layout.representation.characters)
    (environment : Environment) (name : String) (outcome : IntegerObject.Outcome) : Prop :=
  ∃ location, Binding name environment location ∧ ObjectAccessMemory.Reading layout state location outcome

theorem read_iff (layout : Layout) (state : State layout.representation.characters)
    (environment : Environment) (name : String) (outcome : IntegerObject.Outcome) :
    read layout state environment name = some outcome ↔ Reading layout (represent state) environment name outcome := by
  cases found : lookup environment name with
  | none =>
      simp only [read, found, bind, Option.bind_none, reduceCtorEq, false_iff]
      rintro ⟨location, bound, _⟩
      rw [(lookup_iff _ _ _).mpr bound] at found
      cases found
  | some location =>
      simp only [read, found, bind, Option.bind_some, ObjectAccessMemory.read_iff]
      constructor
      · exact fun observed => ⟨location, (lookup_iff _ _ _).mp found, observed⟩
      · rintro ⟨other, bound, observed⟩
        have same : location = other := Option.some.inj (found.symm.trans ((lookup_iff _ _ _).mpr bound))
        subst other
        exact observed

def store (layout : Layout) (state : State layout.representation.characters)
    (environment : Environment) (name : String) (value : IntegerValue layout.representation.integer) :
    Option (State layout.representation.characters) := do
  let location ← lookup environment name
  ObjectAccessMemory.store layout state location value

def Writing (layout : Layout) (before after : SemanticState layout.representation.characters)
    (environment : Environment) (name : String) (value : IntegerValue layout.representation.integer) : Prop :=
  ∃ location, Binding name environment location ∧ ObjectAccessMemory.Writing layout before after location value

theorem store_sound (layout : Layout) (state saved : State layout.representation.characters)
    (environment : Environment) (name : String) (value : IntegerValue layout.representation.integer)
    (executed : store layout state environment name value = some saved) :
    Writing layout (represent state) (represent saved) environment name value := by
  cases found : lookup environment name with
  | none => simp [store, found] at executed
  | some location =>
      refine ⟨location, (lookup_iff _ _ _).mp found, ObjectAccessMemory.store_sound _ _ _ _ _ ?_⟩
      simpa [store, found] using executed

theorem store_complete (layout : Layout) (state : State layout.representation.characters)
    (after : SemanticState layout.representation.characters) (environment : Environment) (name : String)
    (value : IntegerValue layout.representation.integer)
    (writing : Writing layout (represent state) after environment name value) :
    ∃ saved, store layout state environment name value = some saved ∧ represent saved = after := by
  obtain ⟨location, bound, written⟩ := writing
  obtain ⟨saved, executed, same⟩ := ObjectAccessMemory.store_complete _ _ _ _ _ written
  exact ⟨saved, by simp [store, (lookup_iff _ _ _).mpr bound, executed], same⟩

theorem resolved_alias_conflict (environment : Environment) (first second : String) (left right : Lvalue)
    (firstResolved : lookup environment first = some left) (secondResolved : lookup environment second = some right)
    (same : left.object = right.object) :
    Binding first environment left ∧ Binding second environment right ∧
      Sequencing.Conflict left.writeEvent right.readEvent := by
  refine ⟨lookup_sound _ _ _ firstResolved, lookup_sound _ _ _ secondResolved, ?_⟩
  unfold Lvalue.writeEvent Lvalue.readEvent
  rw [same]
  exact .modifyRead _

end Mettapedia.Languages.C11.ScopedLvalues
