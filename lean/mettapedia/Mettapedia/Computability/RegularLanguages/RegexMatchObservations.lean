import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Regex observations and selection from an admitted ordered relation

An observation retains a span, capture participation and the branch choices of
its derivation. A finite ordered realization supplies candidates; selection is
specified independently by an earliest eligible occurrence. Full matching
restricts eligibility before selection. This file does not identify the order
of arbitrary nullable paths with a well-order, or establish a source compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexMatchObservations

universe u v

structure Span where
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

def Span.Valid (span : Span) (length : Nat) : Prop :=
  span.start ≤ span.stop ∧ span.stop ≤ length

/-- `none` means nonparticipation, not a successful empty capture. -/
structure Observation where
  span : Span
  captures : List (Option Span)
  priority : List Bool
  deriving DecidableEq, Repr

def Observation.Valid (observation : Observation) (length : Nat) : Prop :=
  observation.span.Valid length ∧
    ∀ capture ∈ observation.captures, ∀ span, capture = some span → span.Valid length

/-- Recognition forgets captures and scheduling choices, but not endpoints. -/
def erase (observation : Observation) : Span := observation.span

def whole (length : Nat) (observation : Observation) : Bool :=
  observation.span.start == 0 && observation.span.stop == length

/-- A relational specification of the first eligible occurrence. Repeated
equal observations remain distinct occurrences in the supplied list. -/
def Selected {α : Type u} (eligible : α → Bool) (candidates : List α) (result : α) : Prop :=
  ∃ before after, candidates = before ++ result :: after ∧
    (∀ earlier ∈ before, eligible earlier = false) ∧ eligible result = true

def select {α : Type u} (eligible : α → Bool) : List α → Option α
  | [] => none
  | candidate :: rest => if eligible candidate then some candidate else select eligible rest

theorem select_eq_some_iff {α : Type u} (eligible : α → Bool) (candidates : List α) (result : α) :
    select eligible candidates = some result ↔ Selected eligible candidates result := by
  induction candidates with
  | nil => simp [select, Selected]
  | cons candidate rest ih =>
      by_cases accepts : eligible candidate = true
      · simp only [select, accepts, ↓reduceIte, Option.some.injEq]
        constructor
        · intro same
          subst result
          exact ⟨[], rest, rfl, by simp, accepts⟩
        · rintro ⟨before, after, equal, rejected, accepted⟩
          cases before with
          | nil => simpa using congrArg List.head? equal
          | cons earlier before =>
              have same : candidate = earlier := by simpa using congrArg List.head? equal
              have reject := rejected earlier (by simp)
              simp [← same, accepts] at reject
      · have rejects : eligible candidate = false := Bool.eq_false_iff.mpr accepts
        simp only [select, rejects, Bool.false_eq_true, ↓reduceIte]
        rw [ih]
        constructor
        · rintro ⟨before, after, equal, rejected, accepted⟩
          refine ⟨candidate :: before, after, by simp [equal], ?_, accepted⟩
          intro earlier member
          rcases List.mem_cons.mp member with same | member
          · simpa [same] using rejects
          · exact rejected earlier member
        · rintro ⟨before, after, equal, rejected, accepted⟩
          cases before with
          | nil =>
              have same : candidate = result := by simpa using congrArg List.head? equal
              simp [same, accepted] at rejects
          | cons earlier before =>
              have tails : rest = before ++ result :: after := by
                simpa using congrArg List.tail equal
              exact ⟨before, after, tails, fun value member => rejected value (by simp [member]), accepted⟩

theorem select_eq_none_iff {α : Type u} (eligible : α → Bool) (candidates : List α) :
    select eligible candidates = none ↔ ∀ candidate ∈ candidates, eligible candidate = false := by
  induction candidates with
  | nil => simp [select]
  | cons candidate rest ih =>
      cases accepts : eligible candidate <;> simp [select, accepts, ih]

theorem selected_unique {α : Type u} (eligible : α → Bool) (candidates : List α)
    {first second : α} (a : Selected eligible candidates first) (b : Selected eligible candidates second) :
    first = second := by
  have := (select_eq_some_iff eligible candidates first).mpr a
  have := (select_eq_some_iff eligible candidates second).mpr b
  simp_all

theorem selected_mem {α : Type u} {eligible : α → Bool} {candidates : List α} {result : α}
    (selected : Selected eligible candidates result) : result ∈ candidates := by
  obtain ⟨before, after, equal, _, _⟩ := selected
  simp [equal]

/-- Adding an eligibility constraint does not delete a later eligible answer
merely because an earlier, ineligible answer exists. -/
theorem select_filter {α : Type u} (eligible : α → Bool) (candidates : List α) :
    select eligible candidates = (candidates.filter eligible).head? := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih => cases accepts : eligible candidate <;> simp [select, accepts, ih]

/-- Selecting before checking full coverage is not full-match selection. -/
theorem fullmatch_must_restrict_before_select :
    let short : Observation := ⟨⟨0, 1⟩, [], [false]⟩
    let complete : Observation := ⟨⟨0, 2⟩, [], [true]⟩
    select (whole 2) [short, complete] = some complete ∧
      ((select (fun _ => true) [short, complete]).filter (whole 2)) = none := by
  decide

theorem nonparticipation_is_not_empty_capture (position : Nat) :
    (none : Option Span) ≠ some ⟨position, position⟩ := by simp

/-- An erasure-respecting eligibility predicate commutes with selection. This
does not claim that captures are reconstructible from erased candidates. -/
theorem select_map {α : Type u} {β : Type v} (f : α → β) (eligible : β → Bool) (candidates : List α) :
    select eligible (candidates.map f) = (select (fun x => eligible (f x)) candidates).map f := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih => cases accepts : eligible (f candidate) <;> simp [select, accepts, ih]

theorem captures_not_recoverable_from_recognition :
    let left : Observation := ⟨⟨0, 1⟩, [some ⟨0, 1⟩, none], [false]⟩
    let right : Observation := ⟨⟨0, 1⟩, [none, some ⟨0, 1⟩], [true]⟩
    erase left = erase right ∧ left ≠ right := by decide

/-- The first branch is higher priority; a common prefix does not alter it.
No shorter-before-longer convention is needed for this counterexample. -/
inductive HigherPriority : List Bool → List Bool → Prop
  | branch (left right : List Bool) : HigherPriority (false :: left) (true :: right)
  | prefix (bit : Bool) {left right : List Bool} :
      HigherPriority left right → HigherPriority (bit :: left) (bit :: right)

def nullablePath (iterations : Nat) : List Bool := List.replicate iterations false ++ [true]

theorem nullablePath_descends (iterations : Nat) :
    HigherPriority (nullablePath (iterations + 1)) (nullablePath iterations) := by
  induction iterations with
  | zero => exact .branch [true] []
  | succ iterations ih =>
      simpa [nullablePath, List.replicate_succ] using HigherPriority.prefix false ih

/-- An unrestricted nullable loop followed by its exit has no highest-priority
finite path. A cycle-admissibility/scheduling policy is essential. -/
theorem nullable_paths_have_no_minimum :
    ¬ ∃ iterations, ∀ other, ¬ HigherPriority (nullablePath other) (nullablePath iterations) := by
  rintro ⟨iterations, least⟩
  exact least (iterations + 1) (nullablePath_descends iterations)

#print axioms select_eq_some_iff
#print axioms select_eq_none_iff
#print axioms selected_unique
#print axioms select_map
#print axioms nullable_paths_have_no_minimum

end Mettapedia.Computability.RegularLanguages.RegexMatchObservations
