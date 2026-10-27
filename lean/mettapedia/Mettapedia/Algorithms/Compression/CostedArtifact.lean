import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Refinement under a fixed observation criterion and complete cost

The criterion is fixed for the task, normally by decoding and comparing with
the original observation. It need not be an equivalence relation: numerical
error bounds can be nontransitive. No step replaces it by comparison with the
previous winner. Domains supply the full encoded cost, not a proposal estimate.
-/

namespace Mettapedia.Algorithms.Compression.CostedArtifact

variable {Artifact : Type}

def accept (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current candidate : Artifact) : Option Artifact :=
  if valid current = true ∧ valid candidate = true ∧ cost candidate < cost current then
    some candidate else none

theorem accept_iff (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current candidate result : Artifact) :
    accept valid cost current candidate = some result ↔
      result = candidate ∧ valid current = true ∧ valid candidate = true ∧ cost candidate < cost current := by
  by_cases good : valid current = true ∧ valid candidate = true ∧ cost candidate < cost current
  · simp [accept, good, eq_comm]
  · simp [accept, good]

def step (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current candidate : Artifact) : Artifact :=
  (accept valid cost current candidate).getD current

theorem step_preserves (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current candidate : Artifact) (admitted : valid current = true) :
    valid (step valid cost current candidate) = true ∧
      cost (step valid cost current candidate) ≤ cost current := by
  cases checked : accept valid cost current candidate with
  | none => simpa [step, checked] using And.intro admitted (Nat.le_refl (cost current))
  | some result =>
      obtain ⟨rfl, _, accepted, smaller⟩ := (accept_iff valid cost current candidate result).mp checked
      exact ⟨by simpa [step, checked] using accepted,
        by simpa [step, checked] using Nat.le_of_lt smaller⟩

theorem step_le_candidate (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current candidate : Artifact) (admitted : valid current = true) (checked : valid candidate = true) :
    cost (step valid cost current candidate) ≤ cost candidate := by
  by_cases smaller : cost candidate < cost current
  · simp [step, accept, admitted, checked, smaller]
  · simp [step, accept, admitted, checked, smaller]
    omega

def refine (valid : Artifact → Bool) (cost : Artifact → Nat) : Artifact → List Artifact → Artifact
  | current, [] => current
  | current, candidate :: rest => refine valid cost (step valid cost current candidate) rest

theorem refine_append (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current : Artifact) (first second : List Artifact) :
    refine valid cost current (first ++ second) =
      refine valid cost (refine valid cost current first) second := by
  induction first generalizing current with
  | nil => rfl
  | cons candidate rest ih => simp only [List.cons_append, refine, ih]

theorem refine_preserves (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current : Artifact) (candidates : List Artifact) (admitted : valid current = true) :
    valid (refine valid cost current candidates) = true ∧
      cost (refine valid cost current candidates) ≤ cost current := by
  induction candidates generalizing current with
  | nil => exact ⟨admitted, Nat.le_refl _⟩
  | cons candidate rest ih =>
      have first := step_preserves valid cost current candidate admitted
      have later := ih _ first.1
      exact ⟨later.1, later.2.trans first.2⟩

theorem refine_optimal_in_region (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current : Artifact) (candidates : List Artifact) (admitted : valid current = true) :
    ∀ candidate ∈ candidates, valid candidate = true →
      cost (refine valid cost current candidates) ≤ cost candidate := by
  induction candidates generalizing current with
  | nil => simp
  | cons first rest ih =>
      have one := step_preserves valid cost current first admitted
      intro candidate member checked
      rcases List.mem_cons.mp member with same | later
      · subst candidate
        have remaining := refine_preserves valid cost (step valid cost current first) rest one.1
        exact remaining.2.trans (step_le_candidate valid cost current first admitted checked)
      · exact ih _ one.1 candidate later checked

theorem invalid_refused (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current candidate : Artifact) (invalid : valid candidate = false) :
    accept valid cost current candidate = none := by simp [accept, invalid]

theorem no_gain_refused (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current candidate : Artifact) (noGain : cost current ≤ cost candidate) :
    accept valid cost current candidate = none := by
  simp [accept, Nat.not_lt.mpr noGain]

/-- Each adjacent observation differs by at most one, but the task's fixed
original bound still rejects the cumulative drift. Costs fall in this control,
so it is the original observation criterion that prevents acceptance. -/
theorem nontransitive_error_does_not_accumulate :
    let original := (0 : Nat)
    let within := fun value : Nat => decide (value ≤ original + 1)
    let cost := fun value : Nat => 3 - value
    step within cost 0 1 = 1 ∧ accept within cost 1 2 = none ∧
      refine within cost 0 [1, 2] = 1 := by decide

end Mettapedia.Algorithms.Compression.CostedArtifact
