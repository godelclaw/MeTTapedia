import Mettapedia.Algorithms.Compression.CostedArtifact

/-!
# Failure guards for finite relational completion families

Relations return ordered answer occurrences. An empty prefix cannot satisfy
a positive example through any chain suffix. A choice suffix cannot remove
a negative answer or a functional mismatch already produced by its prefix.
Neither rule inspects an unfinished suffix or changes a shared assignment.

The enumeration law permits a suffix region depending on the prefix's entire
state. It preserves the accepted list, including order and duplicates, and
therefore every subsequent ordered fold. It counts complete checks separately
from guard work. Purity and finite-answer admission of executable backgrounds
are implementation obligations; the native library restricts these guards to
physically validated closed fact tables and otherwise keeps its authored route.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.RelationalPruning

universe u v w s t

variable {A : Type u} {B : Type v} {C : Type w}

structure Examples (Input : Type u) (Output : Type v) where
  positive : List (Input × Output)
  negative : List (Input × Output)
  functional : Bool

def chain (first : A → List B) (second : B → List C) (input : A) : List C :=
  (first input).flatMap second

def choice (first second : A → List C) (input : A) : List C := first input ++ second input

def Covers (examples : List (A × C)) (run : A → List C) : Prop :=
  ∀ row ∈ examples, row.2 ∈ run row.1

def Avoids (examples : List (A × C)) (run : A → List C) : Prop :=
  ∀ row ∈ examples, row.2 ∉ run row.1

def Agrees (examples : List (A × C)) (run : A → List C) : Prop :=
  ∀ row ∈ examples, ∀ output ∈ run row.1, output = row.2

def Accepts (examples : Examples A C) (run : A → List C) : Prop :=
  Covers examples.positive run ∧ Avoids examples.negative run ∧
    (examples.functional = true → Agrees examples.positive run)

def consistent [DecidableEq C] (examples : Examples A C) (run : A → List C) : Bool :=
  examples.positive.all (fun row => decide (row.2 ∈ run row.1)) &&
    examples.negative.all (fun row => !decide (row.2 ∈ run row.1)) &&
    (if examples.functional then
      examples.positive.all (fun row => (run row.1).all (fun output => decide (output = row.2)))
    else true)

theorem consistent_iff [DecidableEq C] (examples : Examples A C) (run : A → List C) :
    consistent examples run = true ↔ Accepts examples run := by
  cases mode : examples.functional <;>
    simp [consistent, Accepts, Covers, Avoids, Agrees, mode, List.all_eq_true, and_assoc]

def chainGuard (positive : List (A × C)) (first : A → List B) : Bool :=
  positive.all (fun row => !(first row.1).isEmpty)

theorem chainGuard_iff (positive : List (A × C)) (first : A → List B) :
    chainGuard positive first = true ↔ ∀ row ∈ positive, first row.1 ≠ [] := by
  have nonempty (values : List B) : (!values.isEmpty) = true ↔ values ≠ [] := by
    cases values <;> simp
  simp only [chainGuard, List.all_eq_true, nonempty]

theorem chain_guard_necessary (examples : Examples A C) (first : A → List B) (second : B → List C)
    (accepted : Accepts examples (chain first second)) : chainGuard examples.positive first = true := by
  apply (chainGuard_iff _ _).mpr
  intro row present empty
  have found := accepted.1 row present
  simp only [chain, empty, List.flatMap_nil, List.not_mem_nil] at found

def choiceGuard [DecidableEq C] (examples : Examples A C) (first : A → List C) : Bool :=
  examples.negative.all (fun row => !decide (row.2 ∈ first row.1)) &&
    (if examples.functional then
      examples.positive.all (fun row => (first row.1).all (fun output => decide (output = row.2)))
    else true)

theorem choiceGuard_iff [DecidableEq C] (examples : Examples A C) (first : A → List C) :
    choiceGuard examples first = true ↔
      Avoids examples.negative first ∧ (examples.functional = true → Agrees examples.positive first) := by
  cases mode : examples.functional <;>
    simp [choiceGuard, Avoids, Agrees, mode, List.all_eq_true]

theorem choice_guard_necessary [DecidableEq C] (examples : Examples A C) (first second : A → List C)
    (accepted : Accepts examples (choice first second)) : choiceGuard examples first = true := by
  apply (choiceGuard_iff _ _).mpr
  constructor
  · intro row present forbidden
    exact accepted.2.1 row present (List.mem_append.mpr (Or.inl forbidden))
  · intro functional row present output found
    exact accepted.2.2 functional row present output (List.mem_append.mpr (Or.inl found))

theorem empty_chain_prefix_rejects (examples : Examples A C) (first : A → List B)
    (failed : chainGuard examples.positive first = false) (second : B → List C) :
    ¬ Accepts examples (chain first second) := by
  intro accepted
  have needed := chain_guard_necessary examples first second accepted
  simp [failed] at needed

theorem bad_choice_prefix_rejects [DecidableEq C] (examples : Examples A C) (first : A → List C)
    (failed : choiceGuard examples first = false) (second : A → List C) :
    ¬ Accepts examples (choice first second) := by
  intro accepted
  have needed := choice_guard_necessary examples first second accepted
  simp [failed] at needed

section Enumeration

variable {Left : Type s} {Right : Type t}

def reference (prefixes : List Left) (suffixes : Left → List Right)
    (valid : Left → Right → Bool) : List (Left × Right) :=
  prefixes.flatMap fun first => ((suffixes first).filter (valid first)).map (first, ·)

def pruned (prefixes : List Left) (suffixes : Left → List Right)
    (guard : Left → Bool) (valid : Left → Right → Bool) : List (Left × Right) :=
  prefixes.flatMap fun first =>
    if guard first then ((suffixes first).filter (valid first)).map (first, ·) else []

/-- A necessary guard removes entire dependent completion families before
their members are checked, without changing the successful occurrence list. -/
theorem pruned_eq_reference (prefixes : List Left) (suffixes : Left → List Right)
    (guard : Left → Bool) (valid : Left → Right → Bool)
    (necessary : ∀ first second, second ∈ suffixes first → valid first second = true → guard first = true) :
    pruned prefixes suffixes guard valid = reference prefixes suffixes valid := by
  induction prefixes with
  | nil => rfl
  | cons first rest ih =>
      change (if guard first then ((suffixes first).filter (valid first)).map (first, ·) else []) ++
          pruned rest suffixes guard valid =
        ((suffixes first).filter (valid first)).map (first, ·) ++ reference rest suffixes valid
      rw [ih]
      by_cases allowed : guard first = true
      · simp [allowed]
      · have empty : (suffixes first).filter (valid first) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro second present
          cases result : valid first second with
          | false => simp
          | true => exact False.elim (allowed (necessary first second present result))
        simp [allowed, empty]

theorem chain_candidates_preserved [DecidableEq C] (examples : Examples A C)
    (prefixes : List Left) (suffixes : Left → List Right)
    (first : Left → A → List B) (second : Left → Right → B → List C) :
    pruned prefixes suffixes (fun left => chainGuard examples.positive (first left))
        (fun left right => consistent examples (chain (first left) (second left right))) =
      reference prefixes suffixes
        (fun left right => consistent examples (chain (first left) (second left right))) := by
  apply pruned_eq_reference
  intro left right _ accepted
  exact chain_guard_necessary examples (first left) (second left right)
    ((consistent_iff _ _).mp accepted)

theorem choice_candidates_preserved [DecidableEq C] (examples : Examples A C)
    (prefixes : List Left) (suffixes : Left → List Right)
    (first : Left → A → List C) (second : Left → Right → A → List C) :
    pruned prefixes suffixes (fun left => choiceGuard examples (first left))
        (fun left right => consistent examples (choice (first left) (second left right))) =
      reference prefixes suffixes
        (fun left right => consistent examples (choice (first left) (second left right))) := by
  apply pruned_eq_reference
  intro left right _ accepted
  exact choice_guard_necessary examples (first left) (second left right)
    ((consistent_iff _ _).mp accepted)

/-- Every subsequent ordered accumulator, including complete artifact
checking, sees the same candidates. No associativity assumption is needed. -/
theorem fold_pruned_eq_reference {State : Type*} (prefixes : List Left) (suffixes : Left → List Right)
    (guard : Left → Bool) (valid : Left → Right → Bool)
    (necessary : ∀ first second, second ∈ suffixes first → valid first second = true → guard first = true)
    (step : State → Left × Right → State) (initial : State) :
    (pruned prefixes suffixes guard valid).foldl step initial =
      (reference prefixes suffixes valid).foldl step initial := by
  rw [pruned_eq_reference prefixes suffixes guard valid necessary]

theorem complete_cost_selection_preserved {Artifact : Type}
    (prefixes : List Left) (suffixes : Left → List Right)
    (guard : Left → Bool) (valid : Left → Right → Bool)
    (necessary : ∀ first second, second ∈ suffixes first → valid first second = true → guard first = true)
    (materialize : Left × Right → Artifact) (artifactValid : Artifact → Bool) (cost : Artifact → Nat)
    (current : Artifact) :
    CostedArtifact.refine artifactValid cost current ((pruned prefixes suffixes guard valid).map materialize) =
      CostedArtifact.refine artifactValid cost current ((reference prefixes suffixes valid).map materialize) := by
  rw [pruned_eq_reference prefixes suffixes guard valid necessary]

/-- Example guards do not replace reconstruction or complete byte cost.
The common checker still minimizes over its admitted materialized artifacts. -/
theorem complete_cost_minimum_in_preserved_region {Artifact : Type}
    (prefixes : List Left) (suffixes : Left → List Right)
    (guard : Left → Bool) (valid : Left → Right → Bool)
    (necessary : ∀ first second, second ∈ suffixes first → valid first second = true → guard first = true)
    (materialize : Left × Right → Artifact) (artifactValid : Artifact → Bool) (cost : Artifact → Nat)
    (current : Artifact) (initial : artifactValid current = true) (program : Left × Right)
    (present : program ∈ reference prefixes suffixes valid) (checked : artifactValid (materialize program) = true) :
    cost (CostedArtifact.refine artifactValid cost current ((pruned prefixes suffixes guard valid).map materialize)) ≤
      cost (materialize program) := by
  rw [complete_cost_selection_preserved prefixes suffixes guard valid necessary]
  exact CostedArtifact.refine_optimal_in_region artifactValid cost current _ initial (materialize program)
    (List.mem_map.mpr ⟨program, present, rfl⟩) checked

def completeChecks (prefixes : List Left) (suffixes : Left → List Right) : Nat :=
  (prefixes.map fun first => (suffixes first).length).sum

def guardedChecks (prefixes : List Left) (suffixes : Left → List Right) (guard : Left → Bool) : Nat :=
  (prefixes.map fun first => if guard first then (suffixes first).length else 0).sum

theorem guarded_checks_le (prefixes : List Left) (suffixes : Left → List Right) (guard : Left → Bool) :
    guardedChecks prefixes suffixes guard ≤ completeChecks prefixes suffixes := by
  induction prefixes with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
      simp only [guardedChecks, completeChecks, List.map_cons, List.sum_cons] at ih ⊢
      split <;> omega

end Enumeration
end Mettapedia.Algorithms.Compression.RelationalPruning
