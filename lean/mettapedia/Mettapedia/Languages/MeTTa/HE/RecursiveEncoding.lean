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

def taskData : Task → Atom
  | .atom value expected bindings fuel =>
      .expression [.symbol "he-eval-atom-v1", value, expected, bindingsData bindings, index fuel]
  | .expression value expected bindings fuel =>
      .expression [.symbol "he-eval-expression-v1", value, expected, bindingsData bindings, index fuel]
  | .func value operatorType bindings fuel =>
      .expression [.symbol "he-eval-function-v1", value, operatorType, bindingsData bindings, index fuel]
  | .args values types bindings fuel =>
      .expression [.symbol "he-eval-arguments-v1", .expression values, .expression types,
        bindingsData bindings, index fuel]
  | .tuple value bindings fuel =>
      .expression [.symbol "he-eval-tuple-v1", value, bindingsData bindings, index fuel]
  | .call value expected bindings fuel =>
      .expression [.symbol "he-eval-call-v1", value, expected, bindingsData bindings, index fuel]
  | .functions value expected bindings fuel types =>
      .expression [.symbol "he-eval-functions-v1", value, expected, bindingsData bindings,
        index fuel, .expression types]
  | .bindingAlternatives value operatorType expected fuel alternatives =>
      .expression [.symbol "he-eval-bindings-v1", value, operatorType, expected,
        index fuel, environmentsData alternatives]
  | .heads operatorType arguments fuel alternatives =>
      .expression [.symbol "he-eval-heads-v1", operatorType, .expression arguments,
        index fuel, resultsData alternatives]
  | .argumentHeads original remaining types fuel alternatives =>
      .expression [.symbol "he-eval-argument-heads-v1", original, .expression remaining,
        .expression types, index fuel, resultsData alternatives]
  | .tupleHeads tail fuel alternatives =>
      .expression [.symbol "he-eval-tuple-heads-v1", tail, index fuel, resultsData alternatives]
  | .calls expected fuel alternatives =>
      .expression [.symbol "he-eval-calls-v1", expected, index fuel, resultsData alternatives]
  | .atoms expected fuel alternatives =>
      .expression [.symbol "he-eval-atoms-v1", expected, index fuel, resultsData alternatives]
  | .equations expected incoming fuel alternatives =>
      .expression [.symbol "he-eval-equations-v1", expected, bindingsData incoming,
        index fuel, resultsData alternatives]
  | .grounded expected incoming fuel alternatives =>
      .expression [.symbol "he-eval-grounded-v1", expected, bindingsData incoming,
        index fuel, resultsData alternatives]
  | .tupleCalls value expected bindings fuel =>
      .expression [.symbol "he-eval-tuple-calls-v1", value, expected, bindingsData bindings, index fuel]

def readTask : Atom → Option Task
  | .expression [.symbol "he-eval-atom-v1", value, expected, bindings, fuel] => do
      return .atom value expected (← readBindings bindings) (← readIndex fuel)
  | .expression [.symbol "he-eval-expression-v1", value, expected, bindings, fuel] => do
      return .expression value expected (← readBindings bindings) (← readIndex fuel)
  | .expression [.symbol "he-eval-function-v1", value, operatorType, bindings, fuel] => do
      return .func value operatorType (← readBindings bindings) (← readIndex fuel)
  | .expression [.symbol "he-eval-arguments-v1", .expression values, .expression types, bindings, fuel] => do
      return .args values types (← readBindings bindings) (← readIndex fuel)
  | .expression [.symbol "he-eval-tuple-v1", value, bindings, fuel] => do
      return .tuple value (← readBindings bindings) (← readIndex fuel)
  | .expression [.symbol "he-eval-call-v1", value, expected, bindings, fuel] => do
      return .call value expected (← readBindings bindings) (← readIndex fuel)
  | .expression [.symbol "he-eval-functions-v1", value, expected, bindings, fuel, .expression types] => do
      return .functions value expected (← readBindings bindings) (← readIndex fuel) types
  | .expression [.symbol "he-eval-bindings-v1", value, operatorType, expected, fuel, alternatives] => do
      return .bindingAlternatives value operatorType expected (← readIndex fuel) (← readEnvironments alternatives)
  | .expression [.symbol "he-eval-heads-v1", operatorType, .expression arguments, fuel, alternatives] => do
      return .heads operatorType arguments (← readIndex fuel) (← readResults alternatives)
  | .expression [.symbol "he-eval-argument-heads-v1", original, .expression remaining,
      .expression types, fuel, alternatives] => do
      return .argumentHeads original remaining types (← readIndex fuel) (← readResults alternatives)
  | .expression [.symbol "he-eval-tuple-heads-v1", tail, fuel, alternatives] => do
      return .tupleHeads tail (← readIndex fuel) (← readResults alternatives)
  | .expression [.symbol "he-eval-calls-v1", expected, fuel, alternatives] => do
      return .calls expected (← readIndex fuel) (← readResults alternatives)
  | .expression [.symbol "he-eval-atoms-v1", expected, fuel, alternatives] => do
      return .atoms expected (← readIndex fuel) (← readResults alternatives)
  | .expression [.symbol "he-eval-equations-v1", expected, incoming, fuel, alternatives] => do
      return .equations expected (← readBindings incoming) (← readIndex fuel) (← readResults alternatives)
  | .expression [.symbol "he-eval-grounded-v1", expected, incoming, fuel, alternatives] => do
      return .grounded expected (← readBindings incoming) (← readIndex fuel) (← readResults alternatives)
  | .expression [.symbol "he-eval-tuple-calls-v1", value, expected, bindings, fuel] => do
      return .tupleCalls value expected (← readBindings bindings) (← readIndex fuel)
  | _ => none

@[simp] theorem readTask_taskData (task : Task) : readTask (taskData task) = some task := by
  cases task <;> simp [readTask, taskData]

def frameData : Frame → Atom
  | .filter => .expression [.symbol "he-eval-filter-v1"]
  | .heads operatorType arguments fuel =>
      .expression [.symbol "he-eval-head-frame-v1", operatorType, .expression arguments, index fuel]
  | .argumentHeads original remaining types fuel =>
      .expression [.symbol "he-eval-argument-frame-v1", original, .expression remaining, .expression types, index fuel]
  | .tupleHeads tail fuel => .expression [.symbol "he-eval-tuple-frame-v1", tail, index fuel]
  | .calls expected fuel => .expression [.symbol "he-eval-call-frame-v1", expected, index fuel]
  | .functionTail head => .expression [.symbol "he-eval-function-tail-v1", head]
  | .argumentTail head => .expression [.symbol "he-eval-argument-tail-v1", head]
  | .tupleTail head => .expression [.symbol "he-eval-tuple-tail-v1", head]
  | .tupleSingleton => .expression [.symbol "he-eval-tuple-singleton-v1"]
  | .append remaining => .expression [.symbol "he-eval-append-v1", taskData remaining]
  | .prepend selected => .expression [.symbol "he-eval-prepend-v1", resultsData selected]
  | .fallback value expected bindings fuel types =>
      .expression [.symbol "he-eval-fallback-v1", value, expected, bindingsData bindings,
        index fuel, .expression types]

def readFrame : Atom → Option Frame
  | .expression [.symbol "he-eval-filter-v1"] => some .filter
  | .expression [.symbol "he-eval-head-frame-v1", operatorType, .expression arguments, fuel] => do
      return .heads operatorType arguments (← readIndex fuel)
  | .expression [.symbol "he-eval-argument-frame-v1", original, .expression remaining, .expression types, fuel] => do
      return .argumentHeads original remaining types (← readIndex fuel)
  | .expression [.symbol "he-eval-tuple-frame-v1", tail, fuel] => do
      return .tupleHeads tail (← readIndex fuel)
  | .expression [.symbol "he-eval-call-frame-v1", expected, fuel] => do
      return .calls expected (← readIndex fuel)
  | .expression [.symbol "he-eval-function-tail-v1", head] => some (.functionTail head)
  | .expression [.symbol "he-eval-argument-tail-v1", head] => some (.argumentTail head)
  | .expression [.symbol "he-eval-tuple-tail-v1", head] => some (.tupleTail head)
  | .expression [.symbol "he-eval-tuple-singleton-v1"] => some .tupleSingleton
  | .expression [.symbol "he-eval-append-v1", remaining] => do return .append (← readTask remaining)
  | .expression [.symbol "he-eval-prepend-v1", selected] => do return .prepend (← readResults selected)
  | .expression [.symbol "he-eval-fallback-v1", value, expected, bindings, fuel, .expression types] => do
      return .fallback value expected (← readBindings bindings) (← readIndex fuel) types
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
