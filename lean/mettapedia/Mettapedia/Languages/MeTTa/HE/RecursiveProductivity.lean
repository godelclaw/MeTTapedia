import Mettapedia.Languages.MeTTa.HE.RecursiveWork

/-!
# Productive advances and finishing budgets for retained HE control

The first-order control machine has a constructed decreasing work account and
no stuck configuration. Its source-fuel profile always completes within a
derived budget, with every answer occurrence drained in order. This concerns
the explicit fuelled evaluator, not termination of unbounded source programs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveProductivity

open RecursiveTasks RecursiveMachine RecursiveCorrectness RecursiveExecution RecursiveWork
open Mettapedia.GSLT.Distinction.ProductiveBlocks

theorem next_remaining (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : next dispatch state = some after) :
    after.remaining dispatch = state.remaining dispatch := by
  have meaning := next_denote dispatch state after advanced
  simp only [Configuration.denote, next_emitted dispatch state after advanced] at meaning
  exact List.append_cancel_left meaning

theorem silent_internal (dispatch : GroundedDispatch) (state after : Configuration)
    (stepped : (machine dispatch).step state = some (.silent after)) :
    next dispatch state = some after := by
  cases advanced : next dispatch state with
  | some found =>
      have same : found = after := by simpa [machine, advanced] using stepped
      simp [same]
  | none =>
      cases control : state.control with
      | work task => simp [next, control] at advanced
      | returning results => cases results <;> simp [machine, advanced, control] at stepped

theorem moves (dispatch : GroundedDispatch) (state : Configuration) :
    (machine dispatch).step state ≠ none := by
  cases advanced : next dispatch state with
  | some after => simp [machine, advanced]
  | none =>
      cases control : state.control with
      | work task => simp [next, control] at advanced
      | returning results => cases results <;> simp [machine, advanced, control]

/-- No externally supplied productivity or correspondence premise is needed. -/
def productive (dispatch : GroundedDispatch) : (machine dispatch).Productive where
  rank := configurationWork dispatch
  silent_decreases := by
    intro state after stepped
    have count := next_work dispatch state after (silent_internal dispatch state after stepped)
    omega
  moves := moves dispatch

/-- Coverage checks add a visible resource request at their boundary; they
cannot introduce an infinite administrative region or a stuck configuration.
This rank concerns the finite approximation, not unbounded source termination. -/
def checkedProductive (dispatch : GroundedDispatch) : (Checked.machine dispatch).Productive where
  rank := configurationWork dispatch
  silent_decreases := by
    intro state after stepped
    have original : (machine dispatch).step state = some (.silent after) := by
      cases blockedHere : Checked.blocked dispatch state with
      | some request => simp [Checked.machine, Checked.guardMachine, blockedHere] at stepped
      | none =>
          cases source : (machine dispatch).step state with
          | none => simp [Checked.machine, Checked.guardMachine, blockedHere, source] at stepped
          | some action =>
              cases action <;> simp [Checked.machine, Checked.guardMachine, blockedHere, source, Transition.relabel] at stepped
              cases stepped
              rfl
    exact (productive dispatch).silent_decreases original
  moves := by
    intro state
    cases blockedHere : Checked.blocked dispatch state with
    | some request => simp [Checked.machine, Checked.guardMachine, blockedHere]
    | none =>
        simpa [Checked.machine, Checked.guardMachine, blockedHere] using moves dispatch state

def finishingBudget (dispatch : GroundedDispatch) (state : Configuration) : Nat :=
  configurationWork dispatch state + (state.remaining dispatch).length + 1

theorem next_budget (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : next dispatch state = some after) :
    finishingBudget dispatch after + 1 = finishingBudget dispatch state := by
  have count := next_work dispatch state after advanced
  simp only [finishingBudget, next_remaining dispatch state after advanced]
  omega

theorem terminal_budget (dispatch : GroundedDispatch) (space : Space)
    (results emitted : ResultSet) :
    finishingBudget dispatch ⟨space, .returning results, [], emitted⟩ = results.length + 1 := by
  simp [finishingBudget, configurationWork, controlWork, stackWork,
    Configuration.remaining, Control.denote]

theorem finishes (dispatch : GroundedDispatch) (state : Configuration) :
    ∃ final, (machine dispatch).run (finishingBudget dispatch state) state =
      (state.remaining dispatch, .finished final) := by
  induction count : finishingBudget dispatch state using Nat.strong_induction_on generalizing state with
  | _ total ih =>
      cases advanced : next dispatch state with
      | some after =>
          have smaller := next_budget dispatch state after advanced
          obtain ⟨final, completed⟩ := ih (finishingBudget dispatch after) (by omega) after rfl
          refine ⟨final, ?_⟩
          rw [← count, ← smaller]
          have stepped : (machine dispatch).step state = some (.silent after) := by
            simp [machine, advanced]
          rw [(machine dispatch).run_succ_silent stepped, completed,
            next_remaining dispatch state after advanced]
      | none =>
          cases control : state.control with
          | work task => simp [next, control] at advanced
          | returning results =>
              have stack : state.stack = [] := by
                cases frames : state.stack with
                | nil => rfl
                | cons frame rest => simp [next, control, frames] at advanced
              cases results with
              | nil =>
                  refine ⟨state, ?_⟩
                  have budget : finishingBudget dispatch state = 1 := by
                    simp [finishingBudget, configurationWork, control, stack, controlWork, stackWork,
                      Configuration.remaining, Control.denote]
                  have pending : state.remaining dispatch = [] := by
                    simp [Configuration.remaining, control, stack, Control.denote]
                  rw [← count, budget, pending]
                  exact (machine dispatch).run_succ_finish (by simp [machine, advanced, control])
              | cons result pending =>
                  let after : Configuration := {state with
                    control := .returning pending, emitted := state.emitted ++ [result]}
                  have countAfter : finishingBudget dispatch after + 1 = finishingBudget dispatch state := by
                    simp [after, finishingBudget, configurationWork, control, stack, controlWork, stackWork,
                      Configuration.remaining, Control.denote]
                  obtain ⟨final, completed⟩ := ih (finishingBudget dispatch after) (by omega) after rfl
                  refine ⟨final, ?_⟩
                  rw [← count, ← countAfter]
                  have stepped : (machine dispatch).step state = some (.publish [result] after) := by
                    simp [machine, advanced, control, after]
                  rw [(machine dispatch).run_succ_publish stepped, completed]
                  simp [after, Configuration.remaining, control, stack, Control.denote]

theorem finishes_with_more_budget (dispatch : GroundedDispatch) (state : Configuration)
    (budget : Nat) (enough : finishingBudget dispatch state ≤ budget) :
    ∃ final, (machine dispatch).run budget state = (state.remaining dispatch, .finished final) := by
  obtain ⟨final, completed⟩ := finishes dispatch state
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  refine ⟨final, ?_⟩
  rw [(machine dispatch).run_add, completed]
  rfl

/-- Complete ordered correspondence, including a constructed sufficient budget. -/
theorem initial_finishes (space : Space) (dispatch : GroundedDispatch) (task : Task) :
    ∃ final, (machine dispatch).run
        (finishingBudget dispatch (Configuration.initial space task)) (Configuration.initial space task) =
      (task.denote space dispatch, .finished final) ∧
      final.emitted = task.denote space dispatch ∧ final.space = space := by
  obtain ⟨final, completed⟩ := finishes dispatch (Configuration.initial space task)
  change (machine dispatch).run _ (Configuration.initial space task) =
    (task.denote space dispatch, .finished final) at completed
  exact ⟨final, completed, (finished_results space dispatch task _ _ final completed).2⟩

end Mettapedia.Languages.MeTTa.HE.RecursiveProductivity
