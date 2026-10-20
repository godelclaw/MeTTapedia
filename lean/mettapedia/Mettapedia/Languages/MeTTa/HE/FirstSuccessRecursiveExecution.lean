import Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveStrategy
import Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution
import Mettapedia.GSLT.Distinction.SimulationComposition
import Mettapedia.Machines.ProductiveCoreAdapters

/-!
# Reflected execution of the first-success recursive strategy

The complete existing recursive configuration is retained. Each advance enters
one existing request or consumes one existing continuation. Encoded execution
decodes its input and action independently. The constructed cost simulations
relate actual structured and represented residual states, preserving ordered
occurrences and exact verdicts at every finite budget. They establish the
representation stage; independent language and native callback stages remain
additional obligations.

Type queries follow an explicit policy over the complete configuration. The
literal profile reads annotations as written. Hyperon Experimental's profile
instantiates every signature returned at an invocation apart from all retained
names, so independent calls of one schematic signature never share an instance,
while the positions of one signature stay correlated.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveEncoding
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The type query consulted at each worker transition. It may read the whole
configuration; replenishing evaluator depths leaves its answers unchanged. -/
structure TypePolicy where
  types : Configuration → TypeLookup
  types_deepen : ∀ extra state, types (state.deepen extra) = types state

/-- The historical profile reads literal annotations at every use. -/
@[reducible] def rawTypes : TypePolicy where
  types state := rawTypeLookup state.space
  types_deepen extra state := by rw [Configuration.deepen_space]

/-- Each type-use query protects every retained caller, pending alternative
and published answer, as well as its own reached bindings and operands. -/
def invocationTypes (state : Configuration) : TypeLookup :=
  getAtomTypesScoped (RecursiveScope.configurationNames state) state.space

@[simp] theorem invocationTypes_deepen (extra : Nat) (state : Configuration) :
    invocationTypes (state.deepen extra) = invocationTypes state := by
  simp only [invocationTypes, RecursiveScope.configurationNames_deepen,
    Configuration.deepen_space]

/-- On a closed signature prefix the invocation query is literal: only later
schematic signatures receive call-site instances. -/
theorem invocationTypes_closed_append (state : Configuration) (bindings : Bindings)
    (subject expected : Atom) {closedPrefix rest : List Atom}
    (types : getAtomTypes state.space subject = closedPrefix ++ rest)
    (closed : ∀ signature ∈ closedPrefix, atomVariables signature = []) :
    ∃ instances, invocationTypes state bindings subject expected = closedPrefix ++ instances ∧
      instances.length = rest.length :=
  getAtomTypesScoped_closed_append _ _ _ _ _ types closed

theorem invocationTypes_closed (state : Configuration) (bindings : Bindings)
    (subject expected : Atom)
    (closed : ∀ signature ∈ getAtomTypes state.space subject, atomVariables signature = []) :
    invocationTypes state bindings subject expected = getAtomTypes state.space subject := by
  obtain ⟨instances, equal, length⟩ := invocationTypes_closed_append state bindings subject expected
    (List.append_nil _).symm closed
  have empty : instances = [] := List.eq_nil_of_length_eq_zero (by simpa using length)
  rw [equal, empty, List.append_nil]

/-- Hyperon Experimental's profile: each invocation instantiates its
signatures apart from the complete retained configuration. -/
def scopedTypes : TypePolicy where
  types := invocationTypes
  types_deepen := invocationTypes_deepen

def next (dispatch : GroundedDispatch) (state : Configuration)
    (policy : TypePolicy := rawTypes) : Option Configuration :=
  match state.control, state.stack with
  | .work task, stack =>
      let entered := FirstSuccessRecursiveStrategy.enter state.space dispatch task (policy.types state)
      some {state with control := entered.1, stack := entered.2 ++ stack}
  | .returning results, frame :: remaining =>
      let resumed := RecursiveMachine.resume state.space frame results (policy.types state)
      some {state with control := resumed.1, stack := resumed.2 ++ remaining}
  | .returning _, [] => none

def machine (dispatch : GroundedDispatch) (policy : TypePolicy := rawTypes) :
    Machine Configuration ResultPair Configuration Empty where
  step state :=
    match next dispatch state policy with
    | some after => some (.silent after)
    | none => match state.control with
      | .work _ => none
      | .returning [] => some (.finish state)
      | .returning (result :: remaining) =>
          some (.publish [result] {state with
            control := .returning remaining, emitted := state.emitted ++ [result]})

theorem next_preserves_context (dispatch : GroundedDispatch) (before after : Configuration)
    {policy : TypePolicy} (advanced : next dispatch before policy = some after) :
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

/-! ## Resource-checked first-success execution -/

namespace Checked

abbrev ResourceRequest := RecursiveMachine.Checked.ResourceRequest

/-- The atomic overload selector checks its visited prefix. Other pending
requests and return frames retain the common leaf-coverage conditions. -/
def blocked (dispatch : GroundedDispatch) (state : Configuration)
    (policy : TypePolicy := rawTypes) : Option ResourceRequest :=
  match state.control, state.stack with
  | .work task, _ =>
      if FirstSuccessRecursiveStrategy.taskReady state.space dispatch task (policy.types state) then none
      else some (match task with
        | .primitive value _ (_ + 1) _ _ =>
            if minimalCoreSupported value then .leafDepth else .primitiveService value
        | _ => if task.depth == 0 then .evaluationDepth else .leafDepth)
  | .returning results, frame :: _ =>
      if RecursiveMachine.Checked.frameReady state.space results frame (policy.types state) then none
      else some .leafDepth
  | .returning _, [] => none

def machine (dispatch : GroundedDispatch) (policy : TypePolicy := rawTypes) :
    Machine Configuration ResultPair Configuration ResourceRequest :=
  RecursiveMachine.Checked.guardMachine (FirstSuccessRecursiveExecution.machine dispatch policy)
    (fun state => blocked dispatch state policy)

/-- Replenishing only the pending operation preserves the complete avoidance
scope used by scoped type queries. Callers, alternatives and earlier answers
remain protected; no new type-instance names are introduced by a depth grant. -/
theorem invocationTypes_replenish (extra : Nat) (state : Configuration) :
    invocationTypes (RecursiveMachine.Checked.replenish extra state) = invocationTypes state := by
  rcases state with ⟨space, control, stack, emitted⟩
  cases control with
  | work task =>
      simp [invocationTypes, RecursiveMachine.Checked.replenish,
        RecursiveScope.configurationNames, RecursiveScope.liveAtoms, RecursiveScope.controlAtoms]
  | returning results =>
      cases stack with
      | nil => rfl
      | cons frame remaining => cases frame <;> rfl

theorem blocked_run (dispatch : GroundedDispatch) (state : Configuration)
    (request : ResourceRequest) (budget : Nat) {policy : TypePolicy}
    (pending : blocked dispatch state policy = some request) :
    (machine dispatch policy).run (budget + 1) state = ([], .suspended request state) := by
  exact (machine dispatch policy).run_succ_call
    (by simp [machine, RecursiveMachine.Checked.guardMachine, pending])

theorem resume_prefix (dispatch : GroundedDispatch) (state saved : Configuration)
    (first second : Nat) (observed : ResultSet) {policy : TypePolicy}
    (paused : (machine dispatch policy).run first state = (observed, .exhausted saved)) :
    (machine dispatch policy).run (first + second) state =
      (observed ++ ((machine dispatch policy).run second saved).1,
        ((machine dispatch policy).run second saved).2) :=
  (machine dispatch policy).established_and_pending first second state saved observed paused

/-- A depth grant changes only the pending operation. It uses the existing
replenishment map, which retains callers, world, scope and publication history. -/
def continueRun (dispatch : GroundedDispatch) (budget extra : Nat)
    (result : ResultSet × Outcome Configuration Configuration ResourceRequest)
    (policy : TypePolicy := rawTypes) :
    ResultSet × Outcome Configuration Configuration ResourceRequest :=
  match result with
  | (events, .suspended _ saved) =>
      let later := (machine dispatch policy).run budget (RecursiveMachine.Checked.replenish extra saved)
      (events ++ later.1, later.2)
  | result => (machine dispatch policy).continueRun budget result

/-- Grants preserve every already-published occurrence as a prefix. The
following events come only from the saved pending operation. -/
theorem continueRun_events_prefix (dispatch : GroundedDispatch) (budget extra : Nat)
    (result : ResultSet × Outcome Configuration Configuration ResourceRequest)
    (policy : TypePolicy := rawTypes) :
    result.1 <+: (continueRun dispatch budget extra result policy).1 := by
  rcases result with ⟨events, outcome⟩
  cases outcome <;> simp only [continueRun, Machine.continueRun]
  all_goals first | exact List.prefix_append _ _ | exact List.prefix_rfl

theorem finished_refines (dispatch : GroundedDispatch) (budget : Nat)
    (state : Configuration) (events : ResultSet) (final : Configuration) {policy : TypePolicy}
    (completed : (machine dispatch policy).run budget state = (events, .finished final)) :
    (FirstSuccessRecursiveExecution.machine dispatch policy).run budget state =
      (events, .finished final) :=
  RecursiveMachine.Checked.guard_finished_refines
    (FirstSuccessRecursiveExecution.machine dispatch policy) (fun state => blocked dispatch state policy)
    budget state final events completed

theorem step_deepen (dispatch : GroundedDispatch) (state : Configuration) (extra : Nat)
    {policy : TypePolicy} (ready : blocked dispatch state policy = none) :
    (FirstSuccessRecursiveExecution.machine dispatch policy).step (state.deepen extra) =
      ((FirstSuccessRecursiveExecution.machine dispatch policy).step state).map (fun transition =>
        (transition.mapState (Configuration.deepen extra)).relabel id (Configuration.deepen extra) id) := by
  rcases state with ⟨space, control, stack, emitted⟩
  cases control with
  | work task =>
      have covered : FirstSuccessRecursiveStrategy.taskReady space dispatch task
          (policy.types ⟨space, .work task, stack, emitted⟩) = true := by
        simpa [blocked] using ready
      have commute := FirstSuccessRecursiveStrategy.enter_deepen space dispatch task extra covered
      have scope : policy.types ⟨space, .work (task.replenish extra),
          stack.map (Frame.deepen extra), emitted⟩ =
          policy.types ⟨space, .work task, stack, emitted⟩ :=
        policy.types_deepen extra ⟨space, .work task, stack, emitted⟩
      simp only [FirstSuccessRecursiveExecution.machine, next, scope,
        Configuration.deepen, Control.deepen, commute,
        RecursiveMachine.Checked.deepenExpansion, List.map_append, Option.map_some, Transition.mapState, Transition.relabel]
  | returning results =>
      cases stack with
      | nil => cases results <;> rfl
      | cons frame remaining =>
          have covered : RecursiveMachine.Checked.frameReady space results frame
              (policy.types ⟨space, .returning results, frame :: remaining, emitted⟩) = true := by
            simpa [blocked] using ready
          have commute := RecursiveMachine.Checked.resume_deepen space frame results extra covered
          have scope : policy.types ⟨space, .returning results,
              frame.deepen extra :: remaining.map (Frame.deepen extra), emitted⟩ =
              policy.types ⟨space, .returning results, frame :: remaining, emitted⟩ :=
            policy.types_deepen extra ⟨space, .returning results, frame :: remaining, emitted⟩
          simp only [FirstSuccessRecursiveExecution.machine, next, scope,
            Configuration.deepen, Control.deepen,
            List.map_cons, commute, RecursiveMachine.Checked.deepenExpansion, List.map_append,
            Option.map_some, Transition.mapState, Transition.relabel]

/-- Actual checked completion earns the same occurrences after increasing
all pending evaluator depths, including those stored in continuation frames. -/
theorem completed_deepen (dispatch : GroundedDispatch) (extra budget : Nat)
    (state final : Configuration) (events : ResultSet) {policy : TypePolicy}
    (completed : (machine dispatch policy).run budget state = (events, .finished final)) :
    (FirstSuccessRecursiveExecution.machine dispatch policy).run budget (state.deepen extra) =
      (events, .finished (final.deepen extra)) :=
  RecursiveMachine.Checked.guard_completed_map
    (FirstSuccessRecursiveExecution.machine dispatch policy) (fun state => blocked dispatch state policy)
    (Configuration.deepen extra) (fun state ready => step_deepen dispatch state extra ready)
    budget state final events completed

/-- Represented execution reuses the common configuration/action readers and
the same resource request codec as the recursive worker. -/
def dataMachine (dispatch : GroundedDispatch) : Machine Atom ResultPair Atom ResourceRequest :=
  RecursiveDataExecution.dataMachineFor (machine dispatch)
    RecursiveDataExecution.Checked.requestData RecursiveDataExecution.Checked.readRequest

/-- The checked representation belongs to the existing machine-stage
category, including explicit resource calls and complete encoded verdicts. -/
def realizationStage (dispatch : GroundedDispatch) :
    Stage ((machine dispatch).relabel id configurationData id) (dataMachine dispatch) where
  related state data := data = configurationData state
  cost := 1
  forward := by
    rw [dataMachine, RecursiveDataExecution.dataMachineFor_eq_represent _ _ _
      RecursiveDataExecution.Checked.readRequest_requestData]
    exact ((Stage.ofRepresentation _ configurationData readConfiguration
      readConfiguration_configurationData).relabel id configurationData id).forward
  reflects := by
    rw [dataMachine, RecursiveDataExecution.dataMachineFor_eq_represent _ _ _
      RecursiveDataExecution.Checked.readRequest_requestData]
    exact ((Stage.ofRepresentation _ configurationData readConfiguration
      readConfiguration_configurationData).relabel id configurationData id).reflects

theorem realizationStage_matchesStuck (dispatch : GroundedDispatch) :
    MatchesStuck ((machine dispatch).relabel id configurationData id)
      (dataMachine dispatch) (realizationStage dispatch).related (realizationStage dispatch).cost := by
  change MatchesStuck _ _ (fun state data => data = configurationData state) 1
  rw [dataMachine, RecursiveDataExecution.dataMachineFor_eq_represent _ _ _
    RecursiveDataExecution.Checked.readRequest_requestData]
  exact (Stage.ofRepresentation_stuck (machine dispatch)
    configurationData readConfiguration readConfiguration_configurationData).relabel id configurationData id

theorem run_representation (dispatch : GroundedDispatch) (budget : Nat) (state : Configuration) :
    (dataMachine dispatch).run budget (configurationData state) =
      (((machine dispatch).run budget state).1,
        RecursiveDataExecution.representedOutcome ((machine dispatch).run budget state).2) :=
  RecursiveDataExecution.run_dataMachineFor (machine dispatch)
    RecursiveDataExecution.Checked.requestData RecursiveDataExecution.Checked.readRequest
    RecursiveDataExecution.Checked.readRequest_requestData budget state

theorem run_iff (dispatch : GroundedDispatch) (budget : Nat) (state : Configuration)
    (events : ResultSet) (outcome : Outcome Configuration Configuration ResourceRequest) :
    (dataMachine dispatch).run budget (configurationData state) =
        (events, RecursiveDataExecution.representedOutcome outcome) ↔
      (machine dispatch).run budget state = (events, outcome) := by
  rw [run_representation]
  rcases (machine dispatch).run budget state with ⟨published, actual⟩
  simp only [Prod.mk.injEq, RecursiveDataExecution.representedOutcome_injective.eq_iff]

theorem malformed_input_refused (dispatch : GroundedDispatch) (input : Atom)
    (malformed : readConfiguration input = none) : (dataMachine dispatch).step input = none := by
  simp [dataMachine, RecursiveDataExecution.dataMachineFor, RecursiveDataExecution.stepDataFor, malformed]

/-- Continue scheduler exhaustion unchanged, or grant depth to the suspended
operation. Malformed retained data is refused, never completed. -/
def continueDataRun (dispatch : GroundedDispatch) (budget extra : Nat) :
    ResultSet × Outcome Atom Atom ResourceRequest → ResultSet × Outcome Atom Atom ResourceRequest
  | (events, .suspended _ saved) =>
      match RecursiveDataExecution.Checked.replenishData extra saved with
      | none => (events, .stuck saved)
      | some granted =>
          let later := (dataMachine dispatch).run budget granted
          (events ++ later.1, later.2)
  | result => (dataMachine dispatch).continueRun budget result

theorem continueRun_representation (dispatch : GroundedDispatch) (budget extra : Nat)
    (result : ResultSet × Outcome Configuration Configuration ResourceRequest) :
    continueDataRun dispatch budget extra
        (result.1, RecursiveDataExecution.representedOutcome result.2) =
      ((continueRun dispatch budget extra result).1,
        RecursiveDataExecution.representedOutcome (continueRun dispatch budget extra result).2) := by
  rcases result with ⟨events, outcome⟩
  cases outcome <;>
    simp [continueDataRun, continueRun, Machine.continueRun,
      RecursiveDataExecution.representedOutcome, run_representation]

theorem represented_resume_prefix (dispatch : GroundedDispatch) (first second : Nat)
    (initial saved : Configuration) (observed : ResultSet)
    (paused : (machine dispatch).run first initial = (observed, .exhausted saved)) :
    (dataMachine dispatch).run (first + second) (configurationData initial) =
      (observed ++ ((dataMachine dispatch).run second (configurationData saved)).1,
        ((dataMachine dispatch).run second (configurationData saved)).2) := by
  have encoded := run_representation dispatch first initial
  rw [paused] at encoded
  exact (dataMachine dispatch).established_and_pending first second
    (configurationData initial) (configurationData saved) observed encoded

theorem data_blocked_run (dispatch : GroundedDispatch) (state : Configuration)
    (request : ResourceRequest) (budget : Nat)
    (pending : blocked dispatch state = some request) :
    (dataMachine dispatch).run (budget + 1) (configurationData state) =
      ([], .suspended request (configurationData state)) := by
  rw [run_representation, blocked_run dispatch state request budget pending]
  rfl

namespace Scheduler

open Mettapedia.Machines.ProductiveCoreAdapters

/-- The common first-order cursor executes the actual checked worker. The
selected type policy, complete pending configuration and resource requests
remain explicit; scheduling does not replace an unserved request by an answer. -/
def visit (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (fuel : Nat) (source : Configuration) : Nat × EventCursor.Result (machine dispatch policy) :=
  Machines.Cursor.advance (EventCursor.provider (machine dispatch policy)) EventCursor.client
    (EventCursor.charge (machine dispatch policy) price) fuel
    (EventCursor.packet (machine dispatch policy) ([], .exhausted source))

theorem visit_read (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (fuel : Nat) (source : Configuration) :
    EventCursor.read (machine dispatch policy) (visit dispatch policy price fuel source).2 =
      (machine dispatch policy).run fuel source := by
  simpa only [visit, List.nil_append] using
    (EventCursor.advance_run (machine dispatch policy) price fuel source []).2

theorem visit_account (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (fuel : Nat) (source : Configuration) :
    (visit dispatch policy price fuel source).1 = (machine dispatch policy).spent price fuel source :=
  (EventCursor.advance_run (machine dispatch policy) price fuel source []).1

theorem visit_split (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (earlier later : Nat) (source : Configuration) :
    visit dispatch policy price (earlier + later) source =
      Machines.Cursor.resume (EventCursor.provider (machine dispatch policy)) EventCursor.client
        (EventCursor.charge (machine dispatch policy) price) later
        (visit dispatch policy price earlier source) :=
  EventCursor.advance_split _ _ _ _ _ _

/-- A real pending request is retained at the shared scheduler boundary.
This does not equate a checked resource request with completed source failure. -/
theorem visit_blocked (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (source : Configuration) (request : ResourceRequest)
    (pending : blocked dispatch source policy = some request) :
    EventCursor.read (machine dispatch policy) (visit dispatch policy price 1 source).2 =
      ([], .suspended request source) := by
  rw [visit_read]
  exact blocked_run dispatch source request 0 pending

/-- An explicit depth grant starts at the saved worker operation and keeps the
previous event history and charge. A primitive-service request requires its
own reply and is left unchanged. This operation supplies no external ownership
or permission to clone the retained computation. -/
def grant (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (budget extra : Nat) (previous : Nat × EventCursor.Result (machine dispatch policy)) :
    Nat × EventCursor.Result (machine dispatch policy) :=
  match EventCursor.read (machine dispatch policy) previous.2 with
  | (events, .suspended request saved) =>
      match request with
      | .primitiveService _ => previous
      | _ =>
          let later := Machines.Cursor.advance (EventCursor.provider (machine dispatch policy))
            EventCursor.client (EventCursor.charge (machine dispatch policy) price) budget
            (EventCursor.packet (machine dispatch policy)
              (events, .exhausted (RecursiveMachine.Checked.replenish extra saved)))
          (previous.1 + later.1, later.2)
  | _ => Machines.Cursor.resume (EventCursor.provider (machine dispatch policy)) EventCursor.client
      (EventCursor.charge (machine dispatch policy) price) budget previous

/-- The granted cursor reads exactly the independently defined checked-worker
continuation with the same policy. The old events are not re-executed. -/
theorem grant_depth_read (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (budget extra : Nat) (previous : Nat × EventCursor.Result (machine dispatch policy))
    (events : ResultSet) (request : ResourceRequest) (saved : Configuration)
    (depth : request = .evaluationDepth ∨ request = .leafDepth)
    (pending : EventCursor.read (machine dispatch policy) previous.2 = (events, .suspended request saved)) :
    EventCursor.read (machine dispatch policy) (grant dispatch policy price budget extra previous).2 =
      continueRun dispatch budget extra (events, .suspended request saved) policy := by
  rcases depth with rfl | rfl
  all_goals
    unfold grant
    rw [pending]
    exact (EventCursor.advance_run (machine dispatch policy) price budget
      (RecursiveMachine.Checked.replenish extra saved) events).2

theorem grant_depth_account (dispatch : GroundedDispatch) (policy : TypePolicy) (price : Configuration → Nat)
    (budget extra : Nat) (previous : Nat × EventCursor.Result (machine dispatch policy))
    (events : ResultSet) (request : ResourceRequest) (saved : Configuration)
    (depth : request = .evaluationDepth ∨ request = .leafDepth)
    (pending : EventCursor.read (machine dispatch policy) previous.2 = (events, .suspended request saved)) :
    (grant dispatch policy price budget extra previous).1 = previous.1 +
      (machine dispatch policy).spent price budget (RecursiveMachine.Checked.replenish extra saved) := by
  rcases depth with rfl | rfl
  all_goals
    unfold grant
    rw [pending]
    exact congrArg (previous.1 + ·) (EventCursor.advance_run (machine dispatch policy) price budget
      (RecursiveMachine.Checked.replenish extra saved) events).1

theorem grant_service_unchanged (dispatch : GroundedDispatch) (policy : TypePolicy)
    (price : Configuration → Nat) (budget extra : Nat)
    (previous : Nat × EventCursor.Result (machine dispatch policy))
    (events : ResultSet) (instruction : Atom) (saved : Configuration)
    (pending : EventCursor.read (machine dispatch policy) previous.2 =
      (events, .suspended (.primitiveService instruction) saved)) :
    grant dispatch policy price budget extra previous = previous := by
  unfold grant
  rw [pending]

end Scheduler

end Checked

namespace Controls.SelectionPolicy

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks

private def arrow (argument returned : Atom) : Atom :=
  .expression [.symbol "->", argument, returned]
private def annotation (type : Atom) : Atom := .expression [.symbol ":", .symbol "ident", type]
private def declaration : Atom :=
  .expression [.symbol "=", .expression [.symbol "ident", .var "x"], .var "x"]
private def source : Space := Space.ofList
  [annotation (arrow Atom.atomType Atom.atomType),
   annotation (arrow (.symbol "Number") (.symbol "Number")), declaration]
private def seven : Atom := .grounded (.int 7)
private def call : Atom := .expression [.symbol "ident", seven]
private def start : Configuration := Configuration.initial source
  (.atom call Atom.undefinedType Bindings.empty 16 [])



private def typedItem : Atom := .symbol "item"
private def argumentSource : Space := Space.ofList
  [.expression [.symbol ":", typedItem, .symbol "A"],
   .expression [.symbol ":", typedItem, .symbol "B"],
   annotation (arrow Atom.atomType Atom.atomType), declaration]
private def argumentCall : Atom := .expression [.symbol "ident", typedItem]
private def argumentStart : Configuration := Configuration.initial argumentSource
  (.atom argumentCall Atom.undefinedType Bindings.empty 16 [])


theorem overloaded_type_scan_selects_one_answer :
    ((FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run 1000 start).1.map Prod.fst =
      [seven] := by decide +kernel

theorem repeated_argument_types_select_one_answer :
    ((FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run 1000 argumentStart).1.map Prod.fst =
      [typedItem] := by decide +kernel

private def duplicateSource : Space := Space.ofList
  [annotation (arrow (.symbol "Number") (.symbol "Number")), declaration, declaration]
private def duplicateStart : Configuration := Configuration.initial duplicateSource
  (.atom call Atom.undefinedType Bindings.empty 16 [])

theorem duplicate_equation_occurrences_remain_two_answers :
    ((FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run 1000 duplicateStart).1.map Prod.fst =
      [seven, seven] := by decide +kernel


theorem repeated_type_paths_are_not_duplicate_answers :
    ((Checked.machine GroundedDispatch.none).run 1000 argumentStart).1.map Prod.fst ≠
      [typedItem, typedItem] := by
  rw [repeated_argument_types_select_one_answer]
  intro equality
  have lengths := congrArg List.length equality
  simp at lengths

theorem duplicate_equations_are_not_collapsed :
    ((Checked.machine GroundedDispatch.none).run 1000 duplicateStart).1.map Prod.fst ≠ [seven] := by
  rw [duplicate_equation_occurrences_remain_two_answers]
  intro equality
  have lengths := congrArg List.length equality
  simp at lengths

end Controls.SelectionPolicy

namespace Controls.ScopedPolymorphism

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks

private def arrow : Atom := .expression [.symbol "->", .var "t", .var "t"]
private def source : Space := Space.ofList
  [.expression [.symbol ":", .symbol "ident", arrow],
   .expression [.symbol "=", .expression [.symbol "ident", .var "x"], .var "x"]]
private def seven : Atom := .grounded (.int 7)
private def yes : Atom := .grounded (.bool true)
private def pairCall : Atom := .expression [.symbol "Pair",
  .expression [.symbol "ident", seven], .expression [.symbol "ident", yes]]
private def pairStart : Configuration := Configuration.initial source
  (.atom pairCall Atom.undefinedType Bindings.empty 16 [])

/-- Two calls of one schematic signature in one retained tuple are typed by
independent call-site instances: the first call's choice of `t` is not reused. -/
theorem independent_calls_of_one_schematic_signature :
    ((Checked.machine GroundedDispatch.none scopedTypes).run 1000 pairStart).1.map Prod.fst =
      [.expression [.symbol "Pair", seven, yes]] := by decide +kernel

private def swappedStart : Configuration := Configuration.initial source
  (.atom (.expression [.symbol "Pair", .expression [.symbol "ident", yes],
    .expression [.symbol "ident", seven]]) Atom.undefinedType Bindings.empty 16 [])

theorem independent_calls_in_either_order :
    ((Checked.machine GroundedDispatch.none scopedTypes).run 1000 swappedStart).1.map Prod.fst =
      [.expression [.symbol "Pair", yes, seven]] := by decide +kernel

/-- A caller that already binds the schematic name `t` keeps its binding:
call-site instances avoid every reached binding name. -/
theorem caller_binding_of_the_schematic_name_is_protected :
    ((Checked.machine GroundedDispatch.none scopedTypes).run 1000
      (Configuration.initial source (.atom pairCall Atom.undefinedType
        (Bindings.empty.assign "t" (.symbol "Number")) 16 []))).1.map Prod.fst =
      [.expression [.symbol "Pair", seven, yes]] := by decide +kernel

/-- The historical literal-annotation profile reuses `t` across the two calls
and rejects the second argument, so the two profiles are observably different. -/
theorem literal_profile_leaks_the_first_instance :
    (((Checked.machine GroundedDispatch.none).run 1000 pairStart).1.map Prod.fst).map
      isEmptyOrError = [true] := by decide +kernel

/-- Declaration inspection stays literal; only invocation queries instantiate. -/
theorem annotation_lookup_stays_raw : getAtomTypes source (.symbol "ident") = [arrow] := by
  decide +kernel

private def correlated : Atom := .expression [.symbol "->", .var "t", .var "t", .symbol "Bool"]
private def correlatedSource : Space := Space.ofList
  [.expression [.symbol ":", .symbol "same", correlated],
   .expression [.symbol "=", .expression [.symbol "same", .var "x", .var "y"], .symbol "True"]]
private def start (call : Atom) : Configuration := Configuration.initial correlatedSource
  (.atom call Atom.undefinedType Bindings.empty 16 [])

/-- One instance is shared by every position of a single signature, so a
within-signature conflict is still a type error. -/
theorem within_signature_conflict_still_rejects :
    (((Checked.machine GroundedDispatch.none scopedTypes).run 1000
      (start (.expression [.symbol "same", seven, yes]))).1.map Prod.fst).map isEmptyOrError =
      [true] := by decide +kernel

theorem within_signature_agreement_succeeds :
    ((Checked.machine GroundedDispatch.none scopedTypes).run 1000
      (start (.expression [.symbol "same", seven, .grounded (.int 8)]))).1.map Prod.fst =
      [.symbol "True"] := by decide +kernel

private def pendingPair : Configuration := Configuration.initial source
  (.atom pairCall Atom.undefinedType Bindings.empty 0 [])

private theorem pending_pair_request (policy : TypePolicy) :
    Checked.blocked GroundedDispatch.none pendingPair policy = some .evaluationDepth := rfl

/-- An actual zero-depth scoped worker request crosses the shared cursor,
then the explicit depth grant keeps scoped invocation for both calls. -/
theorem scoped_cursor_depth_grant_keeps_independent_instances :
    (Machines.ProductiveCoreAdapters.EventCursor.read (Checked.machine GroundedDispatch.none scopedTypes)
      (Checked.Scheduler.grant GroundedDispatch.none scopedTypes (fun _ => 1) 1000 16
        (Checked.Scheduler.visit GroundedDispatch.none scopedTypes (fun _ => 1) 1 pendingPair)).2).1.map Prod.fst =
      [.expression [.symbol "Pair", seven, yes]] := by
  rw [Checked.Scheduler.grant_depth_read _ _ _ _ _ _ [] .evaluationDepth pendingPair (Or.inl rfl)
    (Checked.Scheduler.visit_blocked _ _ _ _ _ (pending_pair_request scopedTypes))]
  simpa only [Checked.continueRun,
    show RecursiveMachine.Checked.replenish 16 pendingPair = pairStart from rfl,
    List.nil_append] using independent_calls_of_one_schematic_signature

/-- The same actual request resumed with literal annotation lookup has the
already proved type-instance conflict. Scheduling does not identify policies. -/
theorem literal_cursor_depth_grant_keeps_policy_separation :
    ((Machines.ProductiveCoreAdapters.EventCursor.read (Checked.machine GroundedDispatch.none rawTypes)
      (Checked.Scheduler.grant GroundedDispatch.none rawTypes (fun _ => 1) 1000 16
        (Checked.Scheduler.visit GroundedDispatch.none rawTypes (fun _ => 1) 1 pendingPair)).2).1.map Prod.fst).map
      isEmptyOrError = [true] := by
  rw [Checked.Scheduler.grant_depth_read _ _ _ _ _ _ [] .evaluationDepth pendingPair (Or.inl rfl)
    (Checked.Scheduler.visit_blocked _ _ _ _ _ (pending_pair_request rawTypes))]
  simpa only [Checked.continueRun,
    show RecursiveMachine.Checked.replenish 16 pendingPair = pairStart from rfl,
    List.nil_append] using literal_profile_leaks_the_first_instance

/-- A real unsupported primitive is a retained service request. Neither a
scheduler allowance nor a depth grant supplies its external response. -/
theorem cursor_depth_grant_does_not_answer_service (policy : TypePolicy) (budget extra : Nat) :
    let saved := Configuration.initial source
      (.primitive (.symbol "opaque-service") Bindings.empty 1 [] none)
    Checked.Scheduler.grant GroundedDispatch.none policy (fun _ => 1) budget extra
        (Checked.Scheduler.visit GroundedDispatch.none policy (fun _ => 1) 1 saved) =
      Checked.Scheduler.visit GroundedDispatch.none policy (fun _ => 1) 1 saved := by
  dsimp only
  apply Checked.Scheduler.grant_service_unchanged _ _ _ _ _ _ [] (.symbol "opaque-service")
  exact Checked.Scheduler.visit_blocked _ _ _ _ _ rfl

end Controls.ScopedPolymorphism

end Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveExecution
