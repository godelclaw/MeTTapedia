import Mettapedia.OSLF.NativeTypes.Decision.FiniteFixedPoints

/-!
# Finite fixed-point execution controls

A reachability chain has one unreachable state. A separate safety transformer
has a surviving two-state cycle and a two-state path ending at a dead end.
Both use independently stated set operators and finite executable realizations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.FiniteFixedPoints.Controls

abbrev State := Fin 4

def chainMeaning : Set State →o Set State where
  toFun states := {state | state = 0 ∨ (state = 1 ∧ 0 ∈ states) ∨ (state = 2 ∧ 1 ∈ states)}
  monotone' := by
    intro first second subset state member
    rcases member with zero | ⟨one, earlier⟩ | ⟨two, earlier⟩
    · exact .inl zero
    · exact .inr (.inl ⟨one, subset earlier⟩)
    · exact .inr (.inr ⟨two, subset earlier⟩)

def chain : Strategy chainMeaning where
  step states := Finset.univ.filter fun state =>
    state = 0 ∨ (state = 1 ∧ 0 ∈ states) ∨ (state = 2 ∧ 1 ∈ states)
  step_correct states := by
    ext state
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

def safetyMeaning : Set State →o Set State where
  toFun states := {state | (state = 0 ∧ 1 ∈ states) ∨ (state = 1 ∧ 0 ∈ states) ∨
    (state = 2 ∧ 3 ∈ states)}
  monotone' := by
    intro first second subset state member
    rcases member with ⟨zero, earlier⟩ | ⟨one, earlier⟩ | ⟨two, earlier⟩
    · exact .inl ⟨zero, subset earlier⟩
    · exact .inr (.inl ⟨one, subset earlier⟩)
    · exact .inr (.inr ⟨two, subset earlier⟩)

def safety : Strategy safetyMeaning where
  step states := Finset.univ.filter fun state =>
    (state = 0 ∧ 1 ∈ states) ∨ (state = 1 ∧ 0 ∈ states) ∨ (state = 2 ∧ 3 ∈ states)
  step_correct states := by
    ext state
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

theorem zero_budget_unknown : (chain.least 0 0).answer = none := by decide +kernel
theorem entering_state_proved_early : (chain.least 1 0).answer = some true := by decide +kernel
theorem not_yet_entered_unknown : (chain.least 2 2).answer = none := by decide +kernel
theorem later_entry_proved : (chain.least 3 2).answer = some true := by decide +kernel
theorem absent_is_not_early_refutation : (chain.least 3 3).answer = none := by decide +kernel
theorem absent_refuted_at_bound : (chain.least 4 3).answer = some false := by decide +kernel
theorem least_membership_semantic : (2 : State) ∈ chainMeaning.lfp :=
  Reference.Core.Outcome.positive (chain.least 3 2) later_entry_proved
theorem least_absence_semantic : (3 : State) ∉ chainMeaning.lfp :=
  Reference.Core.Outcome.negative (chain.least 4 3) absent_refuted_at_bound

theorem greatest_zero_unknown : (safety.greatest 0 3).answer = none := by decide +kernel
theorem dead_end_refuted_early : (safety.greatest 1 3).answer = some false := by decide +kernel
theorem predecessor_not_yet_refuted : (safety.greatest 1 2).answer = none := by decide +kernel
theorem predecessor_refuted_early : (safety.greatest 2 2).answer = some false := by decide +kernel
theorem surviving_cycle_not_early_proof : (safety.greatest 3 0).answer = none := by decide +kernel
theorem surviving_cycle_proved_at_bound : (safety.greatest 4 0).answer = some true := by decide +kernel
theorem least_does_not_inherit_a_cycle : (safety.least 4 0).answer = some false := by decide +kernel
theorem excess_budget_preserves_answer : (safety.greatest 7 0).answer = some true := by decide +kernel
theorem cycle_membership_semantic : (0 : State) ∈ safetyMeaning.gfp :=
  Reference.Core.Outcome.positive (safety.greatest 4 0) surviving_cycle_proved_at_bound
theorem dying_path_absence_semantic : (2 : State) ∉ safetyMeaning.gfp :=
  Reference.Core.Outcome.negative (safety.greatest 2 2) predecessor_refuted_early

theorem least_resume_reuses_approximation :
    (((chain.begin ∅).resume 1).resume 2).states = chain.lower 3 := by decide +kernel
theorem resumed_least_answer :
    ((((chain.begin ∅).resume 1).resume 2).least 2).answer = some true := by decide +kernel
theorem resumed_greatest_answer :
    ((((safety.begin Finset.univ).resume 1).resume 1).greatest 2).answer = some false := by decide +kernel

def run : IO Unit := do
  let checks := [
    (chain.least 0 0).answer == none,
    (chain.least 1 0).answer == some true,
    (chain.least 2 2).answer == none,
    (chain.least 3 2).answer == some true,
    (chain.least 3 3).answer == none,
    (chain.least 4 3).answer == some false,
    (safety.greatest 0 3).answer == none,
    (safety.greatest 1 3).answer == some false,
    (safety.greatest 1 2).answer == none,
    (safety.greatest 2 2).answer == some false,
    (safety.greatest 3 0).answer == none,
    (safety.greatest 4 0).answer == some true,
    (safety.least 4 0).answer == some false,
    (safety.greatest 7 0).answer == some true,
    ((((chain.begin ∅).resume 1).resume 2).least 2).answer == some true,
    ((((safety.begin Finset.univ).resume 1).resume 1).greatest 2).answer == some false]
  if !checks.all id then throw (IO.userError "Finite fixed-point strategy control failed")
  IO.println s!"Finite fixed-point strategy controls: {checks.length} passed"

#eval run

end Mettapedia.OSLF.NativeTypes.Decision.FiniteFixedPoints.Controls
