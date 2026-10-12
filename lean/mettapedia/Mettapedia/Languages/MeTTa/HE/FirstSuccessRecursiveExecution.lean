import Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveStrategy
import Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# Reflected execution of the first-success recursive strategy

The complete existing recursive configuration is retained. Each advance enters
one existing request or consumes one existing continuation. Encoded execution
decodes its input and action independently. The constructed cost simulations
relate actual structured and represented residual states, preserving ordered
occurrences and exact verdicts at every finite budget. They establish the
representation stage; independent language and native callback stages remain
additional obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveEncoding
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def next (dispatch : GroundedDispatch) (state : Configuration) : Option Configuration :=
  match state.control, state.stack with
  | .work task, stack =>
      let entered := FirstSuccessRecursiveStrategy.enter state.space dispatch task
      some {state with control := entered.1, stack := entered.2 ++ stack}
  | .returning results, frame :: remaining =>
      let resumed := RecursiveMachine.resume state.space frame results
      some {state with control := resumed.1, stack := resumed.2 ++ remaining}
  | .returning _, [] => none

def machine (dispatch : GroundedDispatch) : Machine Configuration ResultPair Configuration Empty where
  step state :=
    match next dispatch state with
    | some after => some (.silent after)
    | none => match state.control with
      | .work _ => none
      | .returning [] => some (.finish state)
      | .returning (result :: remaining) =>
          some (.publish [result] {state with
            control := .returning remaining, emitted := state.emitted ++ [result]})

theorem next_preserves_context (dispatch : GroundedDispatch) (before after : Configuration)
    (advanced : next dispatch before = some after) :
    after.space = before.space ∧ after.emitted = before.emitted := by
  cases before with
  | mk space control stack emitted =>
      cases control with
      | work task => cases advanced; exact ⟨rfl, rfl⟩
      | returning results =>
          cases stack with
          | nil => simp [next] at advanced
          | cons frame remaining => cases advanced; exact ⟨rfl, rfl⟩

theorem step_moves (dispatch : GroundedDispatch) (state : Configuration) :
    ∃ action, (machine dispatch).step state = some action := by
  cases state with
  | mk space control stack emitted =>
      cases control with
      | work task => exact ⟨_, rfl⟩
      | returning results =>
          cases stack with
          | cons frame remaining => exact ⟨_, rfl⟩
          | nil => cases results <;> exact ⟨_, rfl⟩

theorem resume_prefix (dispatch : GroundedDispatch) (state saved : Configuration)
    (first second : Nat) (observed : ResultSet)
    (paused : (machine dispatch).run first state = (observed, .exhausted saved)) :
    (machine dispatch).run (first + second) state =
      (observed ++ ((machine dispatch).run second saved).1,
        ((machine dispatch).run second saved).2) :=
  (machine dispatch).established_and_pending first second state saved observed paused

abbrev Action := Transition Configuration ResultPair Configuration Empty

/-- Inspect represented state, then encode the computed observable action. -/
def stepData (dispatch : GroundedDispatch) (input : Atom) : Option Atom := do
  let state ← readConfiguration input
  return RecursiveDataExecution.actionData (← (machine dispatch).step state)

/-- Verdicts are complete decoded configurations, so the representation stage
has the same verdict carrier and can use the common simulation theory. -/
def dataMachine (dispatch : GroundedDispatch) : Machine Atom ResultPair Configuration Empty where
  step input := do
    let output ← stepData dispatch input
    let action ← RecursiveDataExecution.readAction output
    match action with
    | .silent state => return .silent (configurationData state)
    | .publish events state => return .publish events (configurationData state)
    | .finish state => return .finish state
    | .fail events => return .fail events
    | .call request _ => nomatch request

def representedAction : Action → Transition Atom ResultPair Configuration Empty
  | .silent state => .silent (configurationData state)
  | .publish events state => .publish events (configurationData state)
  | .finish state => .finish state
  | .fail events => .fail events
  | .call request _ => nomatch request

theorem step_representation (dispatch : GroundedDispatch) (state : Configuration) :
    (dataMachine dispatch).step (configurationData state) =
      representedAction <$> (machine dispatch).step state := by
  cases found : (machine dispatch).step state with
  | none => simp [dataMachine, stepData, found]
  | some action =>
      cases action with
      | call request _ => nomatch request
      | silent state => simp [dataMachine, stepData, found, representedAction]
      | publish events state => simp [dataMachine, stepData, found, representedAction]
      | finish state => simp [dataMachine, stepData, found, representedAction]
      | fail events => simp [dataMachine, stepData, found, representedAction]

theorem malformed_rejected (dispatch : GroundedDispatch) (input : Atom)
    (malformed : readConfiguration input = none) :
    (dataMachine dispatch).step input = none := by
  simp [dataMachine, stepData, malformed]

/-- A graph relation over complete configurations, not an answer-support relation. -/
def Represents (state : Configuration) (data : Atom) : Prop := data = configurationData state

theorem forwardSimulation (dispatch : GroundedDispatch) :
    CostSimulation (machine dispatch) (dataMachine dispatch) Represents 1 where
  silent := by
    rintro state _ after rfl advanced
    refine ⟨1, le_rfl, configurationData after, ?_, rfl⟩
    simp [Machine.run, step_representation, advanced, representedAction]
  publish := by
    rintro state _ events after rfl advanced
    refine ⟨1, le_rfl, configurationData after, ?_, rfl⟩
    simp [Machine.run, step_representation, advanced, representedAction]
  finish := by
    rintro state _ final rfl advanced
    exact ⟨1, le_rfl, by simp [Machine.run, step_representation, advanced, representedAction]⟩
  fail := by
    rintro state _ events rfl advanced
    exact ⟨1, le_rfl, by simp [Machine.run, step_representation, advanced, representedAction]⟩
  call := by
    rintro state _ request saved rfl _
    nomatch request

theorem backwardSimulation (dispatch : GroundedDispatch) :
    CostSimulation (dataMachine dispatch) (machine dispatch)
      (fun data state => Represents state data) 1 where
  silent := by
    rintro _ state dataAfter rfl advanced
    rw [step_representation] at advanced
    cases found : (machine dispatch).step state with
    | none => simp [found] at advanced
    | some action =>
        cases action <;> simp [found, representedAction] at advanced
        case silent after =>
          exact ⟨1, le_rfl, after, by simp [Machine.run, found], advanced.symm⟩
        case call request _ => nomatch request
  publish := by
    rintro _ state events dataAfter rfl advanced
    rw [step_representation] at advanced
    cases found : (machine dispatch).step state with
    | none => simp [found] at advanced
    | some action =>
        cases action <;> simp [found, representedAction] at advanced
        case publish published after =>
          obtain ⟨rfl, rfl⟩ := advanced
          exact ⟨1, le_rfl, after, by simp [Machine.run, found], rfl⟩
        case call request _ => nomatch request
  finish := by
    rintro _ state final rfl advanced
    rw [step_representation] at advanced
    cases found : (machine dispatch).step state with
    | none => simp [found] at advanced
    | some action =>
        cases action <;> simp [found, representedAction] at advanced
        case finish finished =>
          cases advanced
          exact ⟨1, le_rfl, by simp [Machine.run, found]⟩
        case call request _ => nomatch request
  fail := by
    rintro _ state events rfl advanced
    rw [step_representation] at advanced
    cases found : (machine dispatch).step state with
    | none => simp [found] at advanced
    | some action =>
        cases action <;> simp [found, representedAction] at advanced
        case fail published =>
          cases advanced
          exact ⟨1, le_rfl, by simp [Machine.run, found]⟩
        case call request _ => nomatch request
  call := by
    rintro _ state request saved _ _
    nomatch request

/-- The constructed representation is a reusable stage, with backward
completion reflection rather than an assumed completion contract. -/
def representationStage (dispatch : GroundedDispatch) :
    Stage (machine dispatch) (dataMachine dispatch) :=
  Stage.ofBackward Represents 1 (forwardSimulation dispatch) (backwardSimulation dispatch)

/-- Exhausted and stuck outcomes retain the represented residual; completed
verdicts retain the full decoded configuration. -/
def representedOutcome : Outcome Configuration Configuration Empty → Outcome Atom Configuration Empty
  | .finished state => .finished state
  | .faulted => .faulted
  | .stuck state => .stuck (configurationData state)
  | .exhausted state => .exhausted (configurationData state)
  | .suspended request _ => nomatch request

/-- The same finite budget exposes exactly the same ordered occurrences and
the related complete residual, rather than only an answer-support inclusion. -/
theorem run_representation (dispatch : GroundedDispatch) (budget : Nat) (state : Configuration) :
    (dataMachine dispatch).run budget (configurationData state) =
      (((machine dispatch).run budget state).1,
        representedOutcome ((machine dispatch).run budget state).2) := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
      rw [Machine.run, step_representation]
      cases advanced : (machine dispatch).step state with
      | none => simp only [advanced, Functor.map, Option.map_none, Machine.run, representedOutcome]
      | some action =>
          cases action with
          | silent after => simpa only [Functor.map, Option.map_some, representedAction, advanced,
              Machine.run] using ih after
          | publish events after =>
              simp only [Functor.map, Option.map_some, representedAction, Machine.run, advanced, ih after]
          | finish verdict => simp only [Functor.map, Option.map_some, representedAction, Machine.run,
              advanced, representedOutcome]
          | fail events => simp only [Functor.map, Option.map_some, representedAction, Machine.run,
              advanced, representedOutcome]
          | call request _ => nomatch request

theorem represented_resume_prefix (dispatch : GroundedDispatch)
    (state saved : Configuration) (first second : Nat) (observed : ResultSet)
    (paused : (machine dispatch).run first state = (observed, .exhausted saved)) :
    (dataMachine dispatch).run (first + second) (configurationData state) =
      (observed ++ ((dataMachine dispatch).run second (configurationData saved)).1,
        ((dataMachine dispatch).run second (configurationData saved)).2) := by
  rw [run_representation, resume_prefix dispatch state saved first second observed paused,
    run_representation]

end Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveExecution
