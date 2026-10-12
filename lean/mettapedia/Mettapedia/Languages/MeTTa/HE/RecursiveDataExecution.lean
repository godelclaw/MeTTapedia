import Mettapedia.Languages.MeTTa.HE.RecursiveEncoding
import Mettapedia.Languages.MeTTa.HE.RecursiveProductivity

/-!
# Executable data stepping and resumption of retained HE evaluation

Incoming configuration data is decoded on every advance. Encoded execution
retains every control field and has exactly the same ordered observations and
saved outcomes as the constructed control machine. The correspondence is
proved for arbitrary configurations and finite budgets. Dispatch remains an
explicit pure parameter; these interfaces do not commit external effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine RecursiveEncoding RecursiveProductivity
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedApplyEncoding (resultsData readResults)

abbrev Action := Transition Configuration ResultPair Configuration Empty

def actionData : Action → Atom
  | .silent state => .expression [.symbol "he-eval-silent-v1", configurationData state]
  | .publish results state =>
      .expression [.symbol "he-eval-publish-v1", resultsData results, configurationData state]
  | .finish state => .expression [.symbol "he-eval-finish-v1", configurationData state]
  | .fail results => .expression [.symbol "he-eval-fail-v1", resultsData results]
  | .call request _ => nomatch request

def readAction : Atom → Option Action
  | .expression [.symbol "he-eval-silent-v1", state] => do return .silent (← readConfiguration state)
  | .expression [.symbol "he-eval-publish-v1", results, state] => do
      return .publish (← readResults results) (← readConfiguration state)
  | .expression [.symbol "he-eval-finish-v1", state] => do return .finish (← readConfiguration state)
  | .expression [.symbol "he-eval-fail-v1", results] => do return .fail (← readResults results)
  | _ => none

@[simp] theorem readAction_actionData (action : Action) : readAction (actionData action) = some action := by
  cases action with
  | call request _ => nomatch request
  | silent state => simp [readAction, actionData]
  | publish results state => simp [readAction, actionData]
  | finish state => simp [readAction, actionData]
  | fail results => simp [readAction, actionData]

def representedAction : Action → Transition Atom ResultPair Atom Empty
  | .silent state => .silent (configurationData state)
  | .publish results state => .publish results (configurationData state)
  | .finish state => .finish (configurationData state)
  | .fail results => .fail results
  | .call request _ => nomatch request

def stepData (dispatch : GroundedDispatch) (input : Atom) : Option Atom := do
  let state ← readConfiguration input
  return actionData (← (machine dispatch).step state)

def dataMachine (dispatch : GroundedDispatch) : Machine Atom ResultPair Atom Empty where
  step input := do
    let output ← stepData dispatch input
    return representedAction (← readAction output)

theorem step_representation (dispatch : GroundedDispatch) (state : Configuration) :
    (dataMachine dispatch).step (configurationData state) =
      representedAction <$> (machine dispatch).step state := by
  cases found : (machine dispatch).step state with
  | none => simp [dataMachine, stepData, found]
  | some action => simp [dataMachine, stepData, found]

theorem step_rejects_malformed (dispatch : GroundedDispatch) (input : Atom)
    (malformed : readConfiguration input = none) : (dataMachine dispatch).step input = none := by
  simp [dataMachine, stepData, malformed]

def representedOutcome : Outcome Configuration Configuration Empty → Outcome Atom Atom Empty
  | .finished state => .finished (configurationData state)
  | .exhausted state => .exhausted (configurationData state)
  | .stuck state => .stuck (configurationData state)
  | .faulted => .faulted
  | .suspended request _ => nomatch request

theorem run_representation (dispatch : GroundedDispatch) (budget : Nat) (state : Configuration) :
    (dataMachine dispatch).run budget (configurationData state) =
      (((machine dispatch).run budget state).1,
        representedOutcome ((machine dispatch).run budget state).2) := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
      simp only [Machine.run, step_representation]
      cases found : (machine dispatch).step state with
      | none => rfl
      | some action =>
          cases action with
          | call request _ => nomatch request
          | silent after => simpa [representedAction] using ih after
          | publish events after => simp [representedAction, ih after]
          | finish final => rfl
          | fail events => rfl

theorem resume_after_prefix (dispatch : GroundedDispatch) (first second : Nat)
    (initial saved : Configuration) (observed : ResultSet)
    (paused : (machine dispatch).run first initial = (observed, .exhausted saved)) :
    (dataMachine dispatch).run (first + second) (configurationData initial) =
      (observed ++ ((dataMachine dispatch).run second (configurationData saved)).1,
        ((dataMachine dispatch).run second (configurationData saved)).2) := by
  have encoded := run_representation dispatch first initial
  rw [paused] at encoded
  exact (dataMachine dispatch).established_and_pending first second
    (configurationData initial) (configurationData saved) observed encoded

theorem finishes (dispatch : GroundedDispatch) (state : Configuration) (budget : Nat)
    (enough : finishingBudget dispatch state ≤ budget) :
    ∃ final, (dataMachine dispatch).run budget (configurationData state) =
      (state.remaining dispatch, .finished (configurationData final)) := by
  obtain ⟨final, completed⟩ := finishes_with_more_budget dispatch state budget enough
  refine ⟨final, ?_⟩
  rw [run_representation, completed]
  rfl

theorem initial_finishes (space : Space) (dispatch : GroundedDispatch) (task : Task) :
    ∃ final, (dataMachine dispatch).run
        (finishingBudget dispatch (Configuration.initial space task))
        (configurationData (Configuration.initial space task)) =
      (task.denote space dispatch, .finished (configurationData final)) ∧
      final.emitted = task.denote space dispatch ∧ final.space = space := by
  obtain ⟨final, completed, retained⟩ := RecursiveProductivity.initial_finishes space dispatch task
  refine ⟨final, ?_, retained⟩
  rw [run_representation, completed]
  rfl

end Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution
