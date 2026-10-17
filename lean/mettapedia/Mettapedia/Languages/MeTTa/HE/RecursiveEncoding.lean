import Mettapedia.Languages.MeTTa.HE.RecursiveTasks
import Mettapedia.Languages.MeTTa.HE.TypedApplyEncoding

/-!
# Data representation of complete retained HE evaluator control

The representation includes the read-only space, current request or result,
every continuation and selected binding, pending alternatives, source fuel and
emitted occurrences. Payload atoms remain syntax. Decoding reconstructs pure
control data; it grants no ownership, external-effect or publication authority.
Grounded dispatch remains an explicit interpretation parameter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveEncoding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks
open TypedApplyEncoding (index readIndex bindingsData readBindings resultsData readResults)

def environmentsData (environments : List Bindings) : Atom :=
  .expression (environments.map bindingsData)

def readEnvironments : Atom → Option (List Bindings)
  | .expression entries => entries.mapM readBindings
  | _ => none

@[simp] theorem readEnvironments_environmentsData (environments : List Bindings) :
    readEnvironments (environmentsData environments) = some environments := by
  simp [readEnvironments, environmentsData, List.mapM_map, Function.comp_def]
  simpa using List.mapM_pure (m := Option) (l := environments) (f := id)

def modeData : InvocationMode → Atom
  | .raw => .expression [.symbol "he-invocation-raw-v1"]
  | .ordinary expected => .expression [.symbol "he-invocation-ordinary-v1", expected]

def readMode : Atom → Option InvocationMode
  | .expression [.symbol "he-invocation-raw-v1"] => some .raw
  | .expression [.symbol "he-invocation-ordinary-v1", expected] => some (.ordinary expected)
  | _ => none

@[simp] theorem readMode_modeData (mode : InvocationMode) : readMode (modeData mode) = some mode := by
  cases mode <;> rfl

def optionAtomData (caller : Option Atom) : Atom := .expression caller.toList

def readOptionAtom : Atom → Option (Option Atom)
  | .expression [] => some none
  | .expression [caller] => some (some caller)
  | _ => none

@[simp] theorem readOptionAtom_optionAtomData (caller : Option Atom) :
    readOptionAtom (optionAtomData caller) = some caller := by cases caller <;> rfl

def provenanceData : InvocationProvenance → Atom
  | .emitted => .symbol "he-emitted-v1"
  | .completed => .symbol "he-completed-v1"

def readProvenance : Atom → Option InvocationProvenance
  | .symbol "he-emitted-v1" => some .emitted
  | .symbol "he-completed-v1" => some .completed
  | _ => none

@[simp] theorem readProvenance_provenanceData (provenance : InvocationProvenance) :
    readProvenance (provenanceData provenance) = some provenance := by cases provenance <;> rfl

def taskData : Task → Atom
  | .atom value expected bindings fuel live =>
      .expression [.symbol "he-eval-atom-v2", value, expected, bindingsData bindings, index fuel, .expression live]
  | .expression value expected bindings fuel live =>
      .expression [.symbol "he-eval-expression-v2", value, expected, bindingsData bindings, index fuel, .expression live]
  | .func value operatorType bindings fuel live =>
      .expression [.symbol "he-eval-function-v2", value, operatorType, bindingsData bindings, index fuel, .expression live]
  | .args values types bindings fuel live =>
      .expression [.symbol "he-eval-arguments-v2", .expression values, .expression types,
        bindingsData bindings, index fuel, .expression live]
  | .tuple value bindings fuel live =>
      .expression [.symbol "he-eval-tuple-v2", value, bindingsData bindings, index fuel, .expression live]
  | .call value expected bindings fuel live =>
      .expression [.symbol "he-eval-call-v2", value, expected, bindingsData bindings, index fuel, .expression live]
  | .functions value expected bindings fuel types live =>
      .expression [.symbol "he-eval-functions-v2", value, expected, bindingsData bindings,
        index fuel, .expression types, .expression live]
  | .bindingAlternatives value operatorType expected fuel alternatives live =>
      .expression [.symbol "he-eval-bindings-v2", value, operatorType, expected,
        index fuel, environmentsData alternatives, .expression live]
  | .heads operatorType arguments fuel alternatives live =>
      .expression [.symbol "he-eval-heads-v2", operatorType, .expression arguments,
        index fuel, resultsData alternatives, .expression live]
  | .argumentHeads original remaining types fuel alternatives live =>
      .expression [.symbol "he-eval-argument-heads-v2", original, .expression remaining,
        .expression types, index fuel, resultsData alternatives, .expression live]
  | .tupleHeads tail fuel alternatives live =>
      .expression [.symbol "he-eval-tuple-heads-v2", tail, index fuel, resultsData alternatives, .expression live]
  | .calls expected fuel alternatives live =>
      .expression [.symbol "he-eval-calls-v2", expected, index fuel, resultsData alternatives, .expression live]
  | .atoms expected fuel alternatives live =>
      .expression [.symbol "he-eval-atoms-v2", expected, index fuel, resultsData alternatives, .expression live]
  | .returned original value expected bindings fuel live =>
      .expression [.symbol "he-eval-return-v1", original, value, expected,
        bindingsData bindings, index fuel, .expression live]
  | .returns original expected fuel alternatives live =>
      .expression [.symbol "he-eval-returns-v1", original, expected,
        index fuel, resultsData alternatives, .expression live]
  | .equations original expected incoming fuel alternatives live =>
      .expression [.symbol "he-eval-equations-raw-v4", original, expected, bindingsData incoming,
        index fuel, resultsData alternatives, .expression live]
  | .grounded original expected incoming fuel alternatives live =>
      .expression [.symbol "he-eval-grounded-raw-v4", original, expected, bindingsData incoming,
        index fuel, resultsData alternatives, .expression live]
  | .tupleCalls value expected bindings fuel live =>
      .expression [.symbol "he-eval-tuple-calls-v2", value, expected, bindingsData bindings, index fuel, .expression live]

  | .invocation mode value bindings fuel live caller =>
      .expression [.symbol "he-task-invocation-v1", modeData mode, value, bindingsData bindings, index fuel, .expression live, optionAtomData caller]
  | .produced value bindings fuel live caller provenance =>
      .expression [.symbol "he-task-produced-v1", value, bindingsData bindings, index fuel, .expression live, optionAtomData caller, provenanceData provenance]
  | .productions fuel alternatives live caller provenance =>
      .expression [.symbol "he-task-productions-v1", index fuel, resultsData alternatives, .expression live, optionAtomData caller, provenanceData provenance]
  | .minimal value bindings fuel live caller =>
      .expression [.symbol "he-task-minimal-v1", value, bindingsData bindings, index fuel, .expression live, optionAtomData caller]
  | .minimals fuel alternatives live caller =>
      .expression [.symbol "he-task-minimals-v1", index fuel, resultsData alternatives, .expression live, optionAtomData caller]
  | .primitive value bindings fuel live caller =>
      .expression [.symbol "he-task-primitive-v1", value, bindingsData bindings, index fuel, .expression live, optionAtomData caller]
  | .chainRows name template fuel alternatives =>
      .expression [.symbol "he-task-chainRows-v1", .var name, template, index fuel, resultsData alternatives]
  | .functionBody value bindings fuel live caller =>
      .expression [.symbol "he-task-functionBody-v1", value, bindingsData bindings, index fuel, .expression live, optionAtomData caller]
  | .bodyResults fuel alternatives live caller =>
      .expression [.symbol "he-task-bodyResults-v1", index fuel, resultsData alternatives, .expression live, optionAtomData caller]
  | .producerResults mode original incoming fuel live emptyReply alternatives =>
      .expression [.symbol "he-task-producerResults-v1", modeData mode, original, bindingsData incoming, index fuel, .expression live, emptyReply, resultsData alternatives]
  | .completed value expected bindings fuel =>
      .expression [.symbol "he-task-completed-v1", value, expected, bindingsData bindings, index fuel]

set_option maxHeartbeats 1200000 in
def readTask : Atom → Option Task
  | .expression [.symbol "he-eval-atom-v2", value, expected, bindings, fuel, .expression live] => do
      return .atom value expected (← readBindings bindings) (← readIndex fuel) live
  | .expression [.symbol "he-eval-expression-v2", value, expected, bindings, fuel, .expression live] => do
      return .expression value expected (← readBindings bindings) (← readIndex fuel) live
  | .expression [.symbol "he-eval-function-v2", value, operatorType, bindings, fuel, .expression live] => do
      return .func value operatorType (← readBindings bindings) (← readIndex fuel) live
  | .expression [.symbol "he-eval-arguments-v2", .expression values, .expression types, bindings, fuel, .expression live] => do
      return .args values types (← readBindings bindings) (← readIndex fuel) live
  | .expression [.symbol "he-eval-tuple-v2", value, bindings, fuel, .expression live] => do
      return .tuple value (← readBindings bindings) (← readIndex fuel) live
  | .expression [.symbol "he-eval-call-v2", value, expected, bindings, fuel, .expression live] => do
      return .call value expected (← readBindings bindings) (← readIndex fuel) live
  | .expression [.symbol "he-eval-functions-v2", value, expected, bindings, fuel, .expression types, .expression live] => do
      return .functions value expected (← readBindings bindings) (← readIndex fuel) types live
  | .expression [.symbol "he-eval-bindings-v2", value, operatorType, expected, fuel, alternatives, .expression live] => do
      return .bindingAlternatives value operatorType expected (← readIndex fuel) (← readEnvironments alternatives) live
  | .expression [.symbol "he-eval-heads-v2", operatorType, .expression arguments, fuel, alternatives, .expression live] => do
      return .heads operatorType arguments (← readIndex fuel) (← readResults alternatives) live
  | .expression [.symbol "he-eval-argument-heads-v2", original, .expression remaining,
      .expression types, fuel, alternatives, .expression live] => do
      return .argumentHeads original remaining types (← readIndex fuel) (← readResults alternatives) live
  | .expression [.symbol "he-eval-tuple-heads-v2", tail, fuel, alternatives, .expression live] => do
      return .tupleHeads tail (← readIndex fuel) (← readResults alternatives) live
  | .expression [.symbol "he-eval-calls-v2", expected, fuel, alternatives, .expression live] => do
      return .calls expected (← readIndex fuel) (← readResults alternatives) live
  | .expression [.symbol "he-eval-atoms-v2", expected, fuel, alternatives, .expression live] => do
      return .atoms expected (← readIndex fuel) (← readResults alternatives) live
  | .expression [.symbol "he-eval-return-v1", original, value, expected, bindings, fuel, .expression live] => do
      return .returned original value expected (← readBindings bindings) (← readIndex fuel) live
  | .expression [.symbol "he-eval-returns-v1", original, expected, fuel, alternatives, .expression live] => do
      return .returns original expected (← readIndex fuel) (← readResults alternatives) live
  | .expression [.symbol "he-eval-equations-raw-v4", original, expected, incoming, fuel, alternatives, .expression live] => do
      return .equations original expected (← readBindings incoming) (← readIndex fuel) (← readResults alternatives) live
  | .expression [.symbol "he-eval-grounded-raw-v4", original, expected, incoming, fuel, alternatives, .expression live] => do
      return .grounded original expected (← readBindings incoming) (← readIndex fuel) (← readResults alternatives) live
  | .expression [.symbol "he-eval-tuple-calls-v2", value, expected, bindings, fuel, .expression live] => do
      return .tupleCalls value expected (← readBindings bindings) (← readIndex fuel) live
  | .expression [.symbol "he-task-invocation-v1", mode, value, bindings, fuel, .expression live, caller] => do
      return .invocation (← readMode mode) value (← readBindings bindings) (← readIndex fuel) live (← readOptionAtom caller)
  | .expression [.symbol "he-task-produced-v1", value, bindings, fuel, .expression live, caller, provenance] => do
      return .produced value (← readBindings bindings) (← readIndex fuel) live (← readOptionAtom caller) (← readProvenance provenance)
  | .expression [.symbol "he-task-productions-v1", fuel, alternatives, .expression live, caller, provenance] => do
      return .productions (← readIndex fuel) (← readResults alternatives) live (← readOptionAtom caller) (← readProvenance provenance)
  | .expression [.symbol "he-task-minimal-v1", value, bindings, fuel, .expression live, caller] => do
      return .minimal value (← readBindings bindings) (← readIndex fuel) live (← readOptionAtom caller)
  | .expression [.symbol "he-task-minimals-v1", fuel, alternatives, .expression live, caller] => do
      return .minimals (← readIndex fuel) (← readResults alternatives) live (← readOptionAtom caller)
  | .expression [.symbol "he-task-primitive-v1", value, bindings, fuel, .expression live, caller] => do
      return .primitive value (← readBindings bindings) (← readIndex fuel) live (← readOptionAtom caller)
  | .expression [.symbol "he-task-chainRows-v1", .var name, template, fuel, alternatives] => do
      return .chainRows name template (← readIndex fuel) (← readResults alternatives)
  | .expression [.symbol "he-task-functionBody-v1", value, bindings, fuel, .expression live, caller] => do
      return .functionBody value (← readBindings bindings) (← readIndex fuel) live (← readOptionAtom caller)
  | .expression [.symbol "he-task-bodyResults-v1", fuel, alternatives, .expression live, caller] => do
      return .bodyResults (← readIndex fuel) (← readResults alternatives) live (← readOptionAtom caller)
  | .expression [.symbol "he-task-producerResults-v1", mode, original, incoming, fuel, .expression live, emptyReply, alternatives] => do
      return .producerResults (← readMode mode) original (← readBindings incoming) (← readIndex fuel) live emptyReply (← readResults alternatives)
  | .expression [.symbol "he-task-completed-v1", value, expected, bindings, fuel] => do
      return .completed value expected (← readBindings bindings) (← readIndex fuel)
  | _ => none

@[simp] theorem readTask_taskData (task : Task) : readTask (taskData task) = some task := by
  cases task <;> simp [readTask, taskData]


def frameData : Frame → Atom
  | .filter => .expression [.symbol "he-eval-filter-v1"]
  | .heads operatorType arguments fuel live =>
      .expression [.symbol "he-eval-head-frame-v2", operatorType, .expression arguments, index fuel,
        .expression live]
  | .argumentHeads original remaining types fuel live =>
      .expression [.symbol "he-eval-argument-frame-v2", original, .expression remaining,
        .expression types, index fuel, .expression live]
  | .tupleHeads tail fuel live =>
      .expression [.symbol "he-eval-tuple-frame-v2", tail, index fuel, .expression live]
  | .calls expected fuel live =>
      .expression [.symbol "he-eval-call-frame-v2", expected, index fuel, .expression live]
  | .functionTail head => .expression [.symbol "he-eval-function-tail-v1", head]
  | .argumentTail head => .expression [.symbol "he-eval-argument-tail-v1", head]
  | .tupleTail head => .expression [.symbol "he-eval-tuple-tail-v1", head]
  | .tupleSingleton => .expression [.symbol "he-eval-tuple-singleton-v1"]
  | .append remaining => .expression [.symbol "he-eval-append-v1", taskData remaining]
  | .prepend selected => .expression [.symbol "he-eval-prepend-v1", resultsData selected]
  | .fallback value expected bindings fuel types =>
      .expression [.symbol "he-eval-fallback-v1", value, expected, bindingsData bindings,
        index fuel, .expression types]

  | .invocationReturn mode original fuel live =>
      .expression [.symbol "he-frame-invocationReturn-v1", modeData mode, original, index fuel, .expression live]
  | .producerResults mode original incoming fuel live emptyReply =>
      .expression [.symbol "he-frame-producerResults-v1", modeData mode, original, bindingsData incoming, index fuel, .expression live, emptyReply]
  | .minimalResults fuel live caller =>
      .expression [.symbol "he-frame-minimalResults-v1", index fuel, .expression live, optionAtomData caller]
  | .chainResults name template fuel =>
      .expression [.symbol "he-frame-chainResults-v1", .var name, template, index fuel]
  | .functionTerminal caller =>
      .expression [.symbol "he-frame-functionTerminal-v1", optionAtomData caller]
  | .bodyResults fuel live caller =>
      .expression [.symbol "he-frame-bodyResults-v1", index fuel, .expression live, optionAtomData caller]

def readFrame : Atom → Option Frame
  | .expression [.symbol "he-eval-filter-v1"] => some .filter
  | .expression [.symbol "he-eval-head-frame-v2", operatorType, .expression arguments, fuel,
      .expression live] => do
      return .heads operatorType arguments (← readIndex fuel) live
  | .expression [.symbol "he-eval-argument-frame-v2", original, .expression remaining,
      .expression types, fuel, .expression live] => do
      return .argumentHeads original remaining types (← readIndex fuel) live
  | .expression [.symbol "he-eval-tuple-frame-v2", tail, fuel, .expression live] => do
      return .tupleHeads tail (← readIndex fuel) live
  | .expression [.symbol "he-eval-call-frame-v2", expected, fuel, .expression live] => do
      return .calls expected (← readIndex fuel) live
  | .expression [.symbol "he-eval-function-tail-v1", head] => some (.functionTail head)
  | .expression [.symbol "he-eval-argument-tail-v1", head] => some (.argumentTail head)
  | .expression [.symbol "he-eval-tuple-tail-v1", head] => some (.tupleTail head)
  | .expression [.symbol "he-eval-tuple-singleton-v1"] => some .tupleSingleton
  | .expression [.symbol "he-eval-append-v1", remaining] => do return .append (← readTask remaining)
  | .expression [.symbol "he-eval-prepend-v1", selected] => do return .prepend (← readResults selected)
  | .expression [.symbol "he-eval-fallback-v1", value, expected, bindings, fuel, .expression types] => do
      return .fallback value expected (← readBindings bindings) (← readIndex fuel) types
  | .expression [.symbol "he-frame-invocationReturn-v1", mode, original, fuel, .expression live] => do
      return .invocationReturn (← readMode mode) original (← readIndex fuel) live
  | .expression [.symbol "he-frame-producerResults-v1", mode, original, incoming, fuel, .expression live, emptyReply] => do
      return .producerResults (← readMode mode) original (← readBindings incoming) (← readIndex fuel) live emptyReply
  | .expression [.symbol "he-frame-minimalResults-v1", fuel, .expression live, caller] => do
      return .minimalResults (← readIndex fuel) live (← readOptionAtom caller)
  | .expression [.symbol "he-frame-chainResults-v1", .var name, template, fuel] => do
      return .chainResults name template (← readIndex fuel)
  | .expression [.symbol "he-frame-functionTerminal-v1", caller] => do
      return .functionTerminal (← readOptionAtom caller)
  | .expression [.symbol "he-frame-bodyResults-v1", fuel, .expression live, caller] => do
      return .bodyResults (← readIndex fuel) live (← readOptionAtom caller)
  | _ => none

@[simp] theorem readFrame_frameData (frame : Frame) : readFrame (frameData frame) = some frame := by
  cases frame <;> simp [readFrame, frameData]

def controlData : Control → Atom
  | .work task => .expression [.symbol "he-eval-work-v1", taskData task]
  | .returning results => .expression [.symbol "he-eval-returning-v1", resultsData results]

def readControl : Atom → Option Control
  | .expression [.symbol "he-eval-work-v1", task] => do return .work (← readTask task)
  | .expression [.symbol "he-eval-returning-v1", results] => do return .returning (← readResults results)
  | _ => none

@[simp] theorem readControl_controlData (control : Control) :
    readControl (controlData control) = some control := by
  cases control <;> simp [readControl, controlData]

def configurationData (state : Configuration) : Atom :=
  .expression [.symbol "he-retained-evaluator-v1", .expression state.space.atoms,
    controlData state.control, .expression (state.stack.map frameData), resultsData state.emitted]

def readConfiguration : Atom → Option Configuration
  | .expression [.symbol "he-retained-evaluator-v1", .expression atoms, control,
      .expression frames, emitted] => do
        return ⟨⟨atoms⟩, ← readControl control, ← frames.mapM readFrame, ← readResults emitted⟩
  | _ => none

@[simp] theorem readConfiguration_configurationData (state : Configuration) :
    readConfiguration (configurationData state) = some state := by
  cases state with
  | mk space control stack emitted =>
      cases space
      simp [readConfiguration, configurationData, List.mapM_map, Function.comp_def]
      rw [show stack.mapM (fun frame => some frame) = some stack by
        simpa using List.mapM_pure (m := Option) (l := stack) (f := id)]
      rfl

theorem configurationData_injective : Function.Injective configurationData := by
  intro first second same
  have decoded := congrArg readConfiguration same
  simpa using decoded

end Mettapedia.Languages.MeTTa.HE.RecursiveEncoding
