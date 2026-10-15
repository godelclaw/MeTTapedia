import Mettapedia.Languages.MeTTa.HE.TypedApplyStreaming

/-!
# Data representation of the typed argument component

The representation retains the original arguments and domains, selected
prefix, binding assignments and equalities, pending candidates, remaining
frames and emitted history. Atom payloads are held as syntax; decoding does
not evaluate them or turn binding names into active variables.

This represents the existing typed application component. Its leaf services
are still explicit parameters. Inner evaluator continuations, Need cells,
world dependencies and pending external effects require their own retained
state and are not claimed to be present in this component.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypedApplyEncoding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def text (name : String) : Atom := .grounded (.string name)

def index (position : Nat) : Atom := .grounded (.int position)

def readIndex : Atom → Option Nat
  | .grounded (.int position) => if 0 ≤ position then some position.toNat else none
  | _ => none

@[simp] theorem readIndex_index (position : Nat) :
    readIndex (index position) = some position := by
  simp [readIndex, index]

private theorem read_map {Value : Type} (encode : Value → Atom)
    (decode : Atom → Option Value) (inverse : ∀ value, decode (encode value) = some value)
    (values : List Value) :
    (values.map encode).mapM decode = some values := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [inverse, ih]

def assignmentData (entry : String × Atom) : Atom :=
  .expression [text entry.1, entry.2]

def readAssignment : Atom → Option (String × Atom)
  | .expression [.grounded (.string name), value] => some (name, value)
  | _ => none

@[simp] theorem readAssignment_assignmentData (entry : String × Atom) :
    readAssignment (assignmentData entry) = some entry := by
  rcases entry with ⟨name, value⟩
  rfl

def equalityData (entry : String × String) : Atom :=
  .expression [text entry.1, text entry.2]

def readEquality : Atom → Option (String × String)
  | .expression [.grounded (.string left), .grounded (.string right)] => some (left, right)
  | _ => none

@[simp] theorem readEquality_equalityData (entry : String × String) :
    readEquality (equalityData entry) = some entry := by
  rcases entry with ⟨left, right⟩
  rfl

def bindingsData (environment : Bindings) : Atom :=
  .expression [.symbol "he-typed-bindings-v1",
    .expression (environment.assignments.map assignmentData),
    .expression (environment.equalities.map equalityData)]

def readBindings : Atom → Option Bindings
  | .expression [.symbol "he-typed-bindings-v1", .expression assignments,
      .expression equalities] => do
        return ⟨← assignments.mapM readAssignment, ← equalities.mapM readEquality⟩
  | _ => none

@[simp] theorem readBindings_bindingsData (environment : Bindings) :
    readBindings (bindingsData environment) = some environment := by
  rcases environment with ⟨assignments, equalities⟩
  simp [bindingsData, readBindings,
    read_map assignmentData readAssignment readAssignment_assignmentData,
    read_map equalityData readEquality readEquality_equalityData]

def resultData (result : ResultPair) : Atom :=
  .expression [result.1, bindingsData result.2]

def readResult : Atom → Option ResultPair
  | .expression [value, environment] => do return (value, ← readBindings environment)
  | _ => none

@[simp] theorem readResult_resultData (result : ResultPair) :
    readResult (resultData result) = some result := by
  rcases result with ⟨value, environment⟩
  simp [readResult, resultData]

def resultsData (results : ResultList) : Atom := .expression (results.map resultData)

def readResults : Atom → Option ResultList
  | .expression results => results.mapM readResult
  | _ => none

@[simp] theorem readResults_resultsData (results : ResultList) :
    readResults (resultsData results) = some results :=
  read_map resultData readResult readResult_resultData results

def stateData (state : TypedApplyState) : Atom :=
  .expression [.symbol "he-typed-state-v1", state.headAtom,
    .expression state.origArgs, .expression state.argTypes, index state.idx,
    .expression state.evArgs, bindingsData state.env]

def readState : Atom → Option TypedApplyState
  | .expression [.symbol "he-typed-state-v1", head, .expression original,
      .expression types, position, .expression selected, environment] => do
        return ⟨head, original, types, ← readIndex position,
          selected, ← readBindings environment⟩
  | _ => none

@[simp] theorem readState_stateData (state : TypedApplyState) :
    readState (stateData state) = some state := by
  rcases state with ⟨head, original, types, position, selected, environment⟩
  simp [readState, stateData]

def frameData : TypedApplyFrame → Atom
  | .apply state => .expression [.symbol "he-typed-apply-v1", stateData state]
  | .argConsumer pending original type state =>
      .expression [.symbol "he-typed-consumer-v1", resultsData pending,
        original, type, stateData state]

def readFrame : Atom → Option TypedApplyFrame
  | .expression [.symbol "he-typed-apply-v1", state] => do
      return .apply (← readState state)
  | .expression [.symbol "he-typed-consumer-v1", pending, original, type, state] => do
      return .argConsumer (← readResults pending) original type (← readState state)
  | _ => none

@[simp] theorem readFrame_frameData (frame : TypedApplyFrame) :
    readFrame (frameData frame) = some frame := by
  cases frame <;> simp [readFrame, frameData]

def configurationData (state : TypedApplyConfig) : Atom :=
  .expression [.symbol "he-typed-configuration-v1", .expression (state.worklist.map frameData),
    resultsData state.emitted]

def readConfiguration : Atom → Option TypedApplyConfig
  | .expression [.symbol "he-typed-configuration-v1", .expression worklist, history] => do
      return ⟨← worklist.mapM readFrame, ← readResults history⟩
  | _ => none

/-- Every represented configuration reconstructs every field, including
duplicate result occurrences and pending sibling environments. -/
@[simp] theorem readConfiguration_configurationData (state : TypedApplyConfig) :
    readConfiguration (configurationData state) = some state := by
  rcases state with ⟨worklist, history⟩
  simp [readConfiguration, configurationData,
    read_map frameData readFrame readFrame_frameData]

/-- Distinct saved configurations cannot collide in this representation. -/
theorem configurationData_injective : Function.Injective configurationData := by
  intro left right equal
  have decoded := congrArg readConfiguration equal
  simpa using decoded

end Mettapedia.Languages.MeTTa.HE.TypedApplyEncoding
