import Mettapedia.Languages.MeTTa.HE.RecursiveEncoding
import Mettapedia.Languages.MeTTa.HE.RecursiveProductivity
import Mettapedia.GSLT.Distinction.SimulationComposition

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

/-- The same action envelope serves pure approximations and checked execution.
Only the request payload depends on the selected interaction interface. -/
def actionDataFor {Request : Type} (requestData : Request → Atom) :
    Transition Configuration ResultPair Configuration Request → Atom
  | .silent state => .expression [.symbol "he-eval-silent-v1", configurationData state]
  | .publish results state =>
      .expression [.symbol "he-eval-publish-v1", resultsData results, configurationData state]
  | .finish state => .expression [.symbol "he-eval-finish-v1", configurationData state]
  | .fail results => .expression [.symbol "he-eval-fail-v1", resultsData results]
  | .call request saved =>
      .expression [.symbol "he-eval-call-v1", requestData request, configurationData saved]

def readActionFor {Request : Type} (readRequest : Atom → Option Request) :
    Atom → Option (Transition Configuration ResultPair Configuration Request)
  | .expression [.symbol "he-eval-silent-v1", state] => do return .silent (← readConfiguration state)
  | .expression [.symbol "he-eval-publish-v1", results, state] => do
      return .publish (← readResults results) (← readConfiguration state)
  | .expression [.symbol "he-eval-finish-v1", state] => do return .finish (← readConfiguration state)
  | .expression [.symbol "he-eval-fail-v1", results] => do return .fail (← readResults results)
  | .expression [.symbol "he-eval-call-v1", request, saved] => do
      return .call (← readRequest request) (← readConfiguration saved)
  | _ => none

@[simp] theorem readActionFor_actionDataFor {Request : Type}
    (requestData : Request → Atom) (readRequest : Atom → Option Request)
    (roundtrip : ∀ request, readRequest (requestData request) = some request)
    (action : Transition Configuration ResultPair Configuration Request) :
    readActionFor readRequest (actionDataFor requestData action) = some action := by
  cases action <;> simp [readActionFor, actionDataFor, roundtrip]

def actionData : Action → Atom := actionDataFor Empty.elim

def readAction : Atom → Option Action := readActionFor (fun _ => none)

@[simp] theorem readAction_actionData (action : Action) : readAction (actionData action) = some action := by
  exact readActionFor_actionDataFor Empty.elim (fun _ => none) (fun request => request.elim) action

def representedAction {Request : Type} :
    Transition Configuration ResultPair Configuration Request → Transition Atom ResultPair Atom Request
  | .silent state => .silent (configurationData state)
  | .publish results state => .publish results (configurationData state)
  | .finish state => .finish (configurationData state)
  | .fail results => .fail results
  | .call request saved => .call request (configurationData saved)

def stepDataFor {Request : Type}
    (machine : Machine Configuration ResultPair Configuration Request)
    (requestData : Request → Atom) (input : Atom) : Option Atom := do
  let state ← readConfiguration input
  return actionDataFor requestData (← machine.step state)

def dataMachineFor {Request : Type}
    (machine : Machine Configuration ResultPair Configuration Request)
    (requestData : Request → Atom) (readRequest : Atom → Option Request) :
    Machine Atom ResultPair Atom Request where
  step input := do
    let output ← stepDataFor machine requestData input
    return representedAction (← readActionFor readRequest output)

/-- Replaying the actual action envelope is the existing partial state adapter,
followed by the independent verdict representation. -/
theorem dataMachineFor_eq_represent {Request : Type}
    (machine : Machine Configuration ResultPair Configuration Request)
    (requestData : Request → Atom) (readRequest : Atom → Option Request)
    (roundtrip : ∀ request, readRequest (requestData request) = some request) :
    dataMachineFor machine requestData readRequest =
      (machine.represent configurationData readConfiguration).relabel id configurationData id := by
  change Machine.mk _ = Machine.mk _
  congr 1
  funext input
  cases decoded : readConfiguration input with
  | none => simp [stepDataFor, Machine.represent, decoded]
  | some state =>
      cases stepped : machine.step state with
      | none => simp [stepDataFor, Machine.represent, decoded, stepped]
      | some action =>
          cases action <;>
            simp [stepDataFor, Machine.represent, decoded,
              stepped, readActionFor_actionDataFor requestData readRequest roundtrip,
              representedAction, Transition.mapState, Transition.relabel]

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

def representedOutcome {Request : Type} :
    Outcome Configuration Configuration Request → Outcome Atom Atom Request
  | .finished state => .finished (configurationData state)
  | .exhausted state => .exhausted (configurationData state)
  | .stuck state => .stuck (configurationData state)
  | .faulted => .faulted
  | .suspended request saved => .suspended request (configurationData saved)

theorem representedOutcome_injective {Request : Type} :
    Function.Injective (representedOutcome (Request := Request)) := by
  intro first second same
  cases first <;> cases second <;>
    simp_all [representedOutcome, configurationData_injective.eq_iff]

theorem run_dataMachineFor {Request : Type}
    (machine : Machine Configuration ResultPair Configuration Request)
    (requestData : Request → Atom) (readRequest : Atom → Option Request)
    (roundtrip : ∀ request, readRequest (requestData request) = some request)
    (budget : Nat) (state : Configuration) :
    (dataMachineFor machine requestData readRequest).run budget (configurationData state) =
      ((machine.run budget state).1, representedOutcome (machine.run budget state).2) := by
  rw [dataMachineFor_eq_represent machine requestData readRequest roundtrip,
    Machine.run_relabel, Machine.run_represent machine configurationData readConfiguration
      readConfiguration_configurationData]
  rcases machine.run budget state with ⟨events, outcome⟩
  cases outcome <;> simp [Outcome.mapState, Outcome.relabel, representedOutcome]

theorem run_representation (dispatch : GroundedDispatch) (budget : Nat) (state : Configuration) :
    (dataMachine dispatch).run budget (configurationData state) =
      (((machine dispatch).run budget state).1,
        representedOutcome ((machine dispatch).run budget state).2) :=
  run_dataMachineFor (machine dispatch) Empty.elim (fun _ => none)
    (fun request => request.elim) budget state

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

/-! ## Checked data execution

The finite approximation above remains useful as a selected bounded semantics.
This interface also retains the coverage checks of the structured evaluator:
an uncovered leaf or exhausted evaluation depth suspends with the exact saved
configuration, rather than being reported as completed empty evaluation.
-/

namespace Checked

abbrev ResourceRequest := RecursiveMachine.Checked.ResourceRequest

def requestData : ResourceRequest → Atom
  | .evaluationDepth => .expression [.symbol "he-eval-evaluation-depth-v1"]
  | .leafDepth => .expression [.symbol "he-eval-leaf-depth-v1"]
  | .primitiveService instruction => .expression [.symbol "he-eval-primitive-service-v1", instruction]

def readRequest : Atom → Option ResourceRequest
  | .expression [.symbol "he-eval-evaluation-depth-v1"] => some .evaluationDepth
  | .expression [.symbol "he-eval-leaf-depth-v1"] => some .leafDepth
  | .expression [.symbol "he-eval-primitive-service-v1", instruction] => some (.primitiveService instruction)
  | _ => none

@[simp] theorem readRequest_requestData (request : ResourceRequest) :
    readRequest (requestData request) = some request := by cases request <;> rfl

def stepData (dispatch : GroundedDispatch) : Atom → Option Atom :=
  stepDataFor (RecursiveMachine.Checked.machine dispatch) requestData

def dataMachine (dispatch : GroundedDispatch) : Machine Atom ResultPair Atom ResourceRequest :=
  dataMachineFor (RecursiveMachine.Checked.machine dispatch) requestData readRequest

/-- The checked HE representation is an instance of the common machine-stage
category. Both sides use the same explicit verdict encoding; the source keeps
structured states and the target checks its submitted action data. -/
def realizationStage (dispatch : GroundedDispatch) :
    Stage ((RecursiveMachine.Checked.machine dispatch).relabel id configurationData id)
      (dataMachine dispatch) where
  related state data := data = configurationData state
  cost := 1
  forward := by
    rw [dataMachine, dataMachineFor_eq_represent _ _ _ readRequest_requestData]
    exact ((Stage.ofRepresentation _ configurationData readConfiguration
      readConfiguration_configurationData).relabel id configurationData id).forward
  reflects := by
    rw [dataMachine, dataMachineFor_eq_represent _ _ _ readRequest_requestData]
    exact ((Stage.ofRepresentation _ configurationData readConfiguration
      readConfiguration_configurationData).relabel id configurationData id).reflects

theorem realizationStage_matchesStuck (dispatch : GroundedDispatch) :
    MatchesStuck ((RecursiveMachine.Checked.machine dispatch).relabel id configurationData id)
      (dataMachine dispatch) (realizationStage dispatch).related (realizationStage dispatch).cost := by
  change MatchesStuck _ _ (fun state data => data = configurationData state) 1
  rw [dataMachine, dataMachineFor_eq_represent _ _ _ readRequest_requestData]
  exact (Stage.ofRepresentation_stuck (RecursiveMachine.Checked.machine dispatch)
    configurationData readConfiguration readConfiguration_configurationData).relabel
      id configurationData id

/-- The submitted data is decoded, checked, and the actual action is read back
through the common envelope. A resource request is not silently erased. -/
theorem run_representation (dispatch : GroundedDispatch) (budget : Nat) (state : Configuration) :
    (dataMachine dispatch).run budget (configurationData state) =
      (((RecursiveMachine.Checked.machine dispatch).run budget state).1,
        representedOutcome ((RecursiveMachine.Checked.machine dispatch).run budget state).2) :=
  run_dataMachineFor _ requestData readRequest readRequest_requestData budget state

/-- No encoded completion, fault, suspension or residual is invented on a
represented input. In particular this reflects the entire saved checkpoint,
not only its answer value or final-status bit. -/
theorem run_iff (dispatch : GroundedDispatch) (budget : Nat) (state : Configuration)
    (events : ResultSet) (outcome : Outcome Configuration Configuration ResourceRequest) :
    (dataMachine dispatch).run budget (configurationData state) =
        (events, representedOutcome outcome) ↔
      (RecursiveMachine.Checked.machine dispatch).run budget state = (events, outcome) := by
  rw [run_representation]
  rcases (RecursiveMachine.Checked.machine dispatch).run budget state with ⟨published, actual⟩
  simp only [Prod.mk.injEq, representedOutcome_injective.eq_iff]

theorem malformed_input_refused (dispatch : GroundedDispatch) (input : Atom)
    (malformed : readConfiguration input = none) : (dataMachine dispatch).step input = none := by
  simp [dataMachine, dataMachineFor, stepDataFor, malformed]

/-- Represent the grant at the actual suspended operation. The decoder
recovers its saved caller, alternatives, scope and published occurrences. -/
def replenishData (extra : Nat) (input : Atom) : Option Atom :=
  (readConfiguration input).map fun state => configurationData (RecursiveMachine.Checked.replenish extra state)

@[simp] theorem replenishData_configurationData (extra : Nat) (state : Configuration) :
    replenishData extra (configurationData state) =
      some (configurationData (RecursiveMachine.Checked.replenish extra state)) := by
  simp [replenishData]

/-- Continue scheduler exhaustion unchanged, or grant depth to a suspended
request. Malformed saved data cannot be turned into a completed result. -/
def continueRun (dispatch : GroundedDispatch) (budget extra : Nat) :
    ResultSet × Outcome Atom Atom ResourceRequest → ResultSet × Outcome Atom Atom ResourceRequest
  | (events, .suspended _ saved) =>
      match replenishData extra saved with
      | none => (events, .stuck saved)
      | some granted =>
          let later := (dataMachine dispatch).run budget granted
          (events ++ later.1, later.2)
  | result => (dataMachine dispatch).continueRun budget result

/-- A data checkpoint and its structured checkpoint continue with exactly the
same grant, occurrences and complete outcome. -/
theorem continueRun_representation (dispatch : GroundedDispatch) (budget extra : Nat)
    (result : ResultSet × Outcome Configuration Configuration ResourceRequest) :
    continueRun dispatch budget extra (result.1, representedOutcome result.2) =
      ((RecursiveMachine.Checked.continueRun dispatch budget extra result).1,
        representedOutcome (RecursiveMachine.Checked.continueRun dispatch budget extra result).2) := by
  rcases result with ⟨events, outcome⟩
  cases outcome <;>
    simp [continueRun, RecursiveMachine.Checked.continueRun, Machine.continueRun,
      representedOutcome, run_representation]

theorem resume_after_prefix (dispatch : GroundedDispatch) (first second : Nat)
    (initial saved : Configuration) (observed : ResultSet)
    (paused : (RecursiveMachine.Checked.machine dispatch).run first initial =
      (observed, .exhausted saved)) :
    (dataMachine dispatch).run (first + second) (configurationData initial) =
      (observed ++ ((dataMachine dispatch).run second (configurationData saved)).1,
        ((dataMachine dispatch).run second (configurationData saved)).2) := by
  have encoded := run_representation dispatch first initial
  rw [paused] at encoded
  exact (dataMachine dispatch).established_and_pending first second
    (configurationData initial) (configurationData saved) observed encoded

/-- Every blocked represented input retains the same explicit request and
saved configuration at any positive scheduler budget. -/
theorem blocked_run (dispatch : GroundedDispatch) (state : Configuration)
    (request : ResourceRequest) (budget : Nat)
    (blocked : RecursiveMachine.Checked.blocked dispatch state = some request) :
    (dataMachine dispatch).run (budget + 1) (configurationData state) =
      ([], .suspended request (configurationData state)) := by
  rw [run_representation, RecursiveMachine.Checked.blocked_run dispatch state request budget blocked]
  rfl

/-- Completed checked data execution agrees with the separately implemented
recursive evaluator, with every occurrence retained. This is the executable
evaluator boundary, independent of the language-specification adequacy claim. -/
theorem finished_results (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (budget : Nat) (events : ResultSet) (final : Configuration)
    (finished : (RecursiveMachine.Checked.machine dispatch).run budget
      (Configuration.initial space task) = (events, .finished final)) :
    (dataMachine dispatch).run budget (configurationData (Configuration.initial space task)) =
      (task.denote space dispatch, .finished (configurationData final)) ∧
      final.emitted = task.denote space dispatch ∧ final.space = space := by
  obtain ⟨same, history, retained⟩ := RecursiveExecution.finished_results space dispatch task
    budget events final (RecursiveMachine.Checked.finished_refines dispatch budget _ _ _ finished)
  refine ⟨?_, same ▸ history, retained⟩
  rw [run_representation, finished, same]
  rfl

end Checked

end Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution
