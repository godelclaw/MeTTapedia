import Mettapedia.Languages.MeTTa.HE.RecursiveService
import Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution
import Mettapedia.Languages.MeTTa.HE.ArgumentResultControls
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
import Mettapedia.Languages.MeTTa.HE.SmallStepQuiescence
import Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness
import Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedRecursiveAdequacy

/-!
# Retained evaluator controls

Controls distinguish selected and independent choices, duplicate occurrences,
raw error-shaped data, failure propagation, saved prefixes and malformed
configuration data. General correspondence and progress are established in
the imported modules; these examples exercise their concrete endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine RecursiveEncoding
open TypedApplyEncoding (index bindingsData resultsData)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def choice : Atom := .symbol "Choice"
def pick : Atom := .expression [.symbol "pick"]

def annotated (value type : Atom) : Atom := .expression [.symbol ":", value, type]
def equation (left right : Atom) : Atom := .expression [.symbol "=", left, right]
def functionType (types : List Atom) : Atom := .expression (.symbol "->" :: types)
def quoted (values : List Atom) : Atom := .expression [.symbol "quote", .expression values]

def choiceSpace : Space := Space.ofList
  [annotated a choice, annotated b choice,
    annotated (.symbol "pick") (functionType [choice]), equation pick a, equation pick b,
    annotated (.symbol "same") (functionType [choice, Atom.atomType]),
    equation (.expression [.symbol "same", .var "x"]) (quoted [.var "x", .var "x"]),
    annotated (.symbol "pair") (functionType [choice, choice, Atom.atomType]),
    equation (.expression [.symbol "pair", .var "x", .var "y"]) (quoted [.var "x", .var "y"]),
    annotated (.symbol "duplicate") (functionType [choice]),
    equation (.expression [.symbol "duplicate"]) a,
    equation (.expression [.symbol "duplicate"]) a,
    equation (.expression [.symbol "duplicate"]) b,
    annotated (.symbol "keep-raw") (functionType [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType]),
    equation (.expression [.symbol "keep-raw", .var "x", .var "y", .var "z"])
      (quoted [.var "x", .var "y", .var "z"]),
    annotated (.symbol "identity") (functionType [choice, choice]),
    equation (.expression [.symbol "identity", .var "value"]) (.var "value")]

def values (task : Task) : List Atom :=
  (task.denote choiceSpace GroundedDispatch.none).map Prod.fst

def shared : Task := .atom (.expression [.symbol "same", pick]) Atom.undefinedType Bindings.empty 32 []
def independent : Task :=
  .atom (.expression [.symbol "pair", pick, pick]) Atom.undefinedType Bindings.empty 32 []
def duplicated : Task :=
  .atom (.expression [.symbol "same", .expression [.symbol "duplicate"]])
    Atom.undefinedType Bindings.empty 32 []
def raw (arguments : List Atom) : Task :=
  .atom (.expression (.symbol "keep-raw" :: arguments)) Atom.undefinedType Bindings.empty 32 []

theorem choose_once_retains_correlation : values shared = [quoted [a, a], quoted [b, b]] := by decide

theorem independent_choices_retained :
    values independent = [quoted [a, a], quoted [a, b], quoted [b, a], quoted [b, b]] := by decide

theorem duplicate_occurrences_retained :
    values duplicated = [quoted [a, a], quoted [a, a], quoted [b, b]] := by decide

theorem shared_is_not_independent : values shared ≠ values independent := by decide

theorem duplicate_is_not_support_only : values duplicated ≠ values shared := by decide

theorem raw_error_symbol_retained :
    values (raw [.symbol "x", .symbol "Error", .symbol "y"]) =
      [quoted [.symbol "x", .symbol "Error", .symbol "y"]] := by decide

theorem raw_nested_error_retained :
    values (raw [.symbol "x", .expression [.symbol "Error", .symbol "y"], .symbol "z"]) =
      [quoted [.symbol "x", .expression [.symbol "Error", .symbol "y"], .symbol "z"]] := by decide

theorem selected_head_is_retained (head original : Atom) (remaining types : List Atom)
    (fuel : Nat) (environment : Bindings) (rest : ResultSet) (live : List Atom)
    (ordinary : (head != original && isEmptyOrError head) = false) :
    enter Space.empty GroundedDispatch.none
      (.argumentHeads original remaining types fuel ((head, environment) :: rest) live) =
      (.work (.args remaining types environment fuel (head :: live)),
        [.argumentTail head, .append (.argumentHeads original remaining types fuel rest live)]) := by
  simp [enter, ordinary]

def terminal : Configuration :=
  ⟨choiceSpace, .returning [(a, Bindings.empty), (a, Bindings.empty), (b, Bindings.empty)], [], []⟩

def afterFirst : Configuration :=
  ⟨choiceSpace, .returning [(a, Bindings.empty), (b, Bindings.empty)], [], [(a, Bindings.empty)]⟩

theorem first_prefix_retained : (machine GroundedDispatch.none).run 1 terminal =
    ([(a, Bindings.empty)], .exhausted afterFirst) := rfl

theorem resume_keeps_occurrences :
    ((machine GroundedDispatch.none).run 3 afterFirst).1 = [(a, Bindings.empty), (b, Bindings.empty)] := by decide

theorem uninterrupted_keeps_occurrences :
    ((machine GroundedDispatch.none).run 4 terminal).1 =
      [(a, Bindings.empty), (a, Bindings.empty), (b, Bindings.empty)] := by decide

theorem encoded_prefix_retained :
    (RecursiveDataExecution.dataMachine GroundedDispatch.none).run 1 (configurationData terminal) =
      ([(a, Bindings.empty)], .exhausted (configurationData afterFirst)) := by
  rw [RecursiveDataExecution.run_representation, first_prefix_retained]
  rfl

theorem empty_arguments_complete :
    enter Space.empty GroundedDispatch.none (.args [] [] Bindings.empty 1 []) =
      (.returning [(argumentPacket [], Bindings.empty)], []) := rfl

theorem mismatched_argument_lists_do_not_forge_success :
    enter Space.empty GroundedDispatch.none (.args [a] [] Bindings.empty 1 []) =
      (.returning [], []) := rfl

theorem zero_source_fuel_stops (value expected : Atom) (environment : Bindings) :
    enter Space.empty GroundedDispatch.none (.atom value expected environment 0 []) =
      (.returning [], []) := rfl


/-! ## Checked completion and retained resource requests -/

def depthBlocked : Configuration :=
  Configuration.initial Space.empty (.atom a Atom.atomType Bindings.empty 0 [])

theorem depth_exhaustion_retains_request :
    (Checked.machine GroundedDispatch.none).run 1 depthBlocked =
      ([], .suspended .evaluationDepth depthBlocked) := rfl

/-- A positive evaluator depth does not conceal a truncated leaf query. -/
def leafBlocked : Configuration :=
  Configuration.initial Space.empty (.call pick Atom.undefinedType Bindings.empty 1 [])

def queryBlocked : Configuration :=
  { leafBlocked with control := .work (.invocation (.ordinary Atom.undefinedType) pick Bindings.empty 1 []) }

theorem zero_leaf_depth_retains_request :
    (Checked.machine GroundedDispatch.none).run 2 leafBlocked =
      ([], .suspended .leafDepth queryBlocked) := rfl

def finishedFailure : Configuration :=
  Configuration.initial Space.empty (.args [a] [] Bindings.empty 1 [])

theorem genuine_failure_completes :
    (RecursiveService.service (fun value => some value) GroundedDispatch.none id).run 2
      finishedFailure = ([], .finished (.faulted .noResult)) := rfl

theorem exhausted_service_is_not_completed_failure :
    (RecursiveService.service (fun value => some value) GroundedDispatch.none id).run 2
      depthBlocked = ([], .suspended .evaluationDepth depthBlocked) := rfl

/-- This state has already selected `b`; only the pending argument needs depth. -/
def retainedArgument : Configuration :=
  ⟨Space.empty, .work (.args [a] [Atom.atomType] Bindings.empty 0 []),
    [.argumentTail b], [(a, Bindings.empty)]⟩

theorem depth_grant_keeps_selected_head_and_history :
    (Checked.replenish 4 retainedArgument).stack = [.argumentTail b] ∧
    (Checked.replenish 4 retainedArgument).emitted = [(a, Bindings.empty)] := by decide

theorem replenished_argument_publishes_once :
    ((Checked.machine GroundedDispatch.none).run 20
      (Checked.replenish 4 retainedArgument)).1 =
      [(argumentPacket [b, a], Bindings.empty)] := by decide

def nestedIdentity : Configuration :=
  Configuration.initial choiceSpace
    (.atom (.expression [.symbol "identity", .expression [.symbol "identity", a]])
      Atom.undefinedType Bindings.empty 32 [])

theorem checked_nested_call_preserves_value :
    ((Checked.machine GroundedDispatch.none).run 600 nestedIdentity).1.map Prod.fst = [a] := by decide

theorem checked_nested_call_completes :
    ∃ events final, (Checked.machine GroundedDispatch.none).run 600 nestedIdentity =
      (events, .finished final) := by
  have finished : (match ((Checked.machine GroundedDispatch.none).run 600 nestedIdentity).2 with
      | .finished _ => true | _ => false) = true := by decide
  cases observed : (Checked.machine GroundedDispatch.none).run 600 nestedIdentity with
  | mk events outcome =>
      rw [observed] at finished
      cases outcome <;> simp only [Bool.false_eq_true] at finished
      exact ⟨_, _, rfl⟩

/-- The arbitrary depth increase is justified by the completed retained run,
including both nested invocations, rather than by a closed scalar canary. -/
theorem completed_nested_depth_is_irrelevant (extra : Nat) :
    (evalAtom choiceSpace GroundedDispatch.none
      (.expression [.symbol "identity", .expression [.symbol "identity", a]])
      Atom.undefinedType Bindings.empty (32 + extra) []).map Prod.fst = [a] := by
  obtain ⟨events, final, completed⟩ := checked_nested_call_completes
  have stable := RecursiveExecution.completed_atom_depth_stable choiceSpace GroundedDispatch.none
    (.expression [.symbol "identity", .expression [.symbol "identity", a]])
    Atom.undefinedType Bindings.empty [] 32 600 events final completed extra
  rw [stable]
  have observed := checked_nested_call_preserves_value
  rw [completed] at observed
  exact observed

theorem completed_nested_call_stably_reaches :
    ∃ selected, EvalAtomStablyReaches choiceSpace GroundedDispatch.none
      (.expression [.symbol "identity", .expression [.symbol "identity", a]])
      Atom.undefinedType Bindings.empty (a, selected) := by
  obtain ⟨events, final, completed⟩ := checked_nested_call_completes
  have values := checked_nested_call_preserves_value
  rw [completed] at values
  have present : a ∈ events.map Prod.fst := by rw [values]; simp
  obtain ⟨⟨value, selected⟩, observed, equal⟩ := List.mem_map.mp present
  change value = a at equal
  subst value
  exact ⟨selected, RecursiveSemanticSoundness.completed_atom_stably_reaches
    choiceSpace GroundedDispatch.none _ _ _ 32 600 [] events final _ completed observed⟩

theorem equal_shallow_answers_do_not_certify_failure :
    evalAtom choiceSpace GroundedDispatch.none
        (.expression [.symbol "identity", .expression [.symbol "identity", a]])
        Atom.undefinedType Bindings.empty 0 [] = [] ∧
      evalAtom choiceSpace GroundedDispatch.none
        (.expression [.symbol "identity", .expression [.symbol "identity", a]])
        Atom.undefinedType Bindings.empty 1 [] = [] ∧
      (evalAtom choiceSpace GroundedDispatch.none
        (.expression [.symbol "identity", .expression [.symbol "identity", a]])
        Atom.undefinedType Bindings.empty 32 []).map Prod.fst = [a] := by
  exact ⟨rfl, rfl, completed_nested_depth_is_irrelevant 0⟩

/-! ## Checked configuration and action data -/

theorem encoded_depth_request_retains_whole_state :
    (RecursiveDataExecution.Checked.dataMachine GroundedDispatch.none).run 1
      (configurationData depthBlocked) =
      ([], .suspended .evaluationDepth (configurationData depthBlocked)) := by
  rw [RecursiveDataExecution.Checked.run_representation, depth_exhaustion_retains_request]
  rfl

theorem encoded_leaf_request_is_not_completion :
    (RecursiveDataExecution.Checked.dataMachine GroundedDispatch.none).run 2
      (configurationData leafBlocked) =
      ([], .suspended .leafDepth (configurationData queryBlocked)) := by
  rw [RecursiveDataExecution.Checked.run_representation, zero_leaf_depth_retains_request]
  rfl

theorem checked_and_bounded_empty_are_distinct :
    (RecursiveDataExecution.dataMachine GroundedDispatch.none).run 2
        (configurationData depthBlocked) =
      ([], .finished (configurationData {depthBlocked with control := .returning []})) ∧
    (RecursiveDataExecution.Checked.dataMachine GroundedDispatch.none).run 2
        (configurationData depthBlocked) =
      ([], .suspended .evaluationDepth (configurationData depthBlocked)) := by
  constructor <;> rfl

theorem encoded_grant_keeps_selected_head_and_history :
    RecursiveDataExecution.Checked.replenishData 4 (configurationData retainedArgument) =
      some (configurationData
        ⟨Space.empty, .work (.args [a] [Atom.atomType] Bindings.empty 4 []),
          [.argumentTail b], [(a, Bindings.empty)]⟩) := by
  rw [RecursiveDataExecution.Checked.replenishData_configurationData]
  rfl

theorem encoded_grant_publishes_pending_work_once :
    (RecursiveDataExecution.Checked.continueRun GroundedDispatch.none 20 4
      ([(a, Bindings.empty)], .suspended .evaluationDepth
        (configurationData retainedArgument))).1 =
      [(a, Bindings.empty), (argumentPacket [b, a], Bindings.empty)] := by
  have represented := RecursiveDataExecution.Checked.continueRun_representation
    GroundedDispatch.none 20 4
    ([(a, Bindings.empty)], .suspended .evaluationDepth retainedArgument)
  have events := congrArg Prod.fst represented
  change _ = [(a, Bindings.empty)] ++ _ at events
  simpa only [RecursiveMachine.Checked.continueRun, replenished_argument_publishes_once,
    RecursiveDataExecution.representedOutcome, List.cons_append, List.nil_append] using events

theorem encoded_duplicate_prefix_resumes :
    (RecursiveDataExecution.Checked.dataMachine GroundedDispatch.none).run 1
        (configurationData terminal) =
      ([(a, Bindings.empty)], .exhausted (configurationData afterFirst)) ∧
    ((RecursiveDataExecution.Checked.dataMachine GroundedDispatch.none).run 3
      (configurationData afterFirst)).1 = [(a, Bindings.empty), (b, Bindings.empty)] := by
  constructor <;> rfl

theorem encoded_nested_call_preserves_value :
    ((RecursiveDataExecution.Checked.dataMachine GroundedDispatch.none).run 600
      (configurationData nestedIdentity)).1.map Prod.fst = [a] := by
  rw [RecursiveDataExecution.Checked.run_representation]
  exact checked_nested_call_preserves_value

theorem request_envelope_roundtrip (request : Checked.ResourceRequest) (state : Configuration) :
    RecursiveDataExecution.readActionFor RecursiveDataExecution.Checked.readRequest
      (RecursiveDataExecution.actionDataFor RecursiveDataExecution.Checked.requestData
        (.call request state)) = some (.call request state) :=
  RecursiveDataExecution.readActionFor_actionDataFor _ _
    RecursiveDataExecution.Checked.readRequest_requestData _

theorem foreign_request_envelope_refused (state : Configuration) :
    RecursiveDataExecution.readActionFor RecursiveDataExecution.Checked.readRequest
      (.expression [.symbol "he-eval-call-v1", .symbol "foreign-request", configurationData state]) =
      none := by rfl

theorem malformed_suspended_configuration_refused :
    RecursiveDataExecution.Checked.continueRun GroundedDispatch.none 10 4
      ([(a, Bindings.empty)], .suspended .evaluationDepth (.symbol "not-a-checkpoint")) =
      ([(a, Bindings.empty)], .stuck (.symbol "not-a-checkpoint")) := rfl

theorem changed_grounded_failure_retained :
    (Task.args [ArgumentResult.Controls.failingArgument, .symbol "later"]
      [.symbol "Value", Atom.atomType] Bindings.empty 32 []).denote
        ArgumentResult.Controls.failureSpace ArgumentResult.Controls.failureDispatch =
      [(ArgumentResult.Controls.failedResult, Bindings.empty)] :=
  ArgumentResult.Controls.changed_grounded_error_propagates

theorem unchanged_error_is_raw_data :
    (Task.args [ArgumentResult.Controls.failedResult] [Atom.atomType] Bindings.empty 4 []).denote
      Space.empty GroundedDispatch.none =
      [(argumentPacket [ArgumentResult.Controls.failedResult], Bindings.empty)] :=
  ArgumentResult.Controls.unchanged_error_is_data

/-- The retained tuple machine preserves the singleton wrapper and the
nested tuple boundary, just as the source evaluator does. -/
theorem retained_tuple_preserves_nested_boundary :
    ((machine GroundedDispatch.none).run 64
      (Configuration.initial Space.empty
        (.tuple (.expression [.symbol "f", .expression [.symbol "a", .symbol "b"]])
          Bindings.empty 8 []))).1.map Prod.fst =
      [.expression [.symbol "f", .expression [.symbol "a", .symbol "b"]]] := by decide

theorem retained_singleton_is_not_unwrapped :
    ((machine GroundedDispatch.none).run 32
      (Configuration.initial Space.empty
        (.tuple (.expression [.symbol "g"]) Bindings.empty 8 []))).1.map Prod.fst =
      [.expression [.symbol "g"]] ∧
    ((machine GroundedDispatch.none).run 32
      (Configuration.initial Space.empty
        (.tuple (.expression [.symbol "g"]) Bindings.empty 8 []))).1.map Prod.fst ≠
      [.symbol "g"] := by decide

theorem negative_fuel_rejected :
    readTask (.expression [.symbol "he-eval-atom-v2", a, choice,
      bindingsData Bindings.empty, .grounded (.int (-1)), .expression []]) = none := by decide

theorem missing_binding_field_rejected :
    readTask (.expression [.symbol "he-eval-atom-v2", a, choice, index 4, .expression []]) =
      none := by decide

theorem missing_continuation_payload_rejected :
    readFrame (.expression [.symbol "he-eval-argument-tail-v1"]) = none := by decide

theorem extra_configuration_field_rejected :
    readConfiguration (.expression [.symbol "he-retained-evaluator-v1", .expression [],
      controlData (.returning []), .expression [], resultsData [], .symbol "extra"]) = none := by decide

theorem malformed_history_rejected :
    readConfiguration (.expression [.symbol "he-retained-evaluator-v1", .expression [],
      controlData (.returning []), .expression [], .expression [a]]) = none := by decide

theorem changed_pending_state_has_different_representation :
    configurationData terminal ≠ configurationData afterFirst := by
  intro equal
  have same := configurationData_injective equal
  have controls := congrArg Configuration.control same
  simp [terminal, afterFirst, a, b] at controls


/-- The empty tuple base does not admit an empty expression evaluation. -/
theorem empty_expression_interpretation_rejected (space : Space) (dispatch : GroundedDispatch)
    (expected : Atom) (bindings : Bindings) (result : ResultPair) :
    ¬InterpretExpression space dispatch Atom.unit expected bindings result := by
  intro interpreted
  cases interpreted <;> simp_all [Atom.unit]

theorem independent_empty_expression_rejected
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (expected : Atom)
    (bindings : Spec.Eval.BindingFrame) (output : Spec.Eval.FrameResult) :
    ¬Spec.Eval.InterpretExpressionRel space dispatch live (typing := typing)
      Atom.unit expected bindings output := by
  intro interpreted
  cases interpreted <;> simp_all [Atom.unit]

/-- Invert the independent singleton rules, including error propagation. -/
theorem independent_singleton_cases
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (input : Atom)
    (bindings : Spec.Eval.BindingFrame) (output : Spec.Eval.FrameResult) :
    Spec.Eval.InterpretTupleRel space dispatch live (typing := typing)
      (.expression [input]) bindings output ↔
      (∃ selected, Spec.Eval.EvalAtomRawRel space dispatch live (typing := typing)
          input Atom.undefinedType bindings selected ∧
        ¬Spec.Eval.IsEmptyOrErrorRel selected.1 ∧
        output = (.expression [selected.1], selected.2)) ∨
      (Spec.Eval.EvalAtomRawRel space dispatch live (typing := typing)
          input Atom.undefinedType bindings output ∧ Spec.Eval.IsEmptyOrErrorRel output.1) := by
  constructor
  · intro interpreted
    cases interpreted with
    | singleton _ _ selected evaluated ordinary =>
        exact Or.inl ⟨selected, evaluated, ordinary, rfl⟩
    | singletonError _ _ _ evaluated error => exact Or.inr ⟨evaluated, error⟩
    | headError _ _ _ _ nonempty _ _ => exact (nonempty rfl).elim
    | tailError _ _ _ _ _ nonempty _ _ _ _ => exact (nonempty rfl).elim
    | success _ _ _ _ _ nonempty _ _ _ _ => exact (nonempty rfl).elim
  · rintro (⟨selected, evaluated, ordinary, rfl⟩ | ⟨evaluated, error⟩)
    · exact .singleton input bindings selected evaluated ordinary
    · exact .singletonError input bindings output evaluated error

/-- The retained singleton path saves its wrapping continuation. -/
theorem singleton_enters_saved_frame (space : Space) (dispatch : GroundedDispatch)
    (value : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    enter space dispatch (.tuple (.expression [value]) bindings (fuel + 1) live) =
      (.work (.atom value Atom.undefinedType bindings fuel live), [.tupleSingleton]) := rfl

theorem empty_tuple_retains_bindings (bindings : Bindings) (fuel : Nat) :
    enter Space.empty GroundedDispatch.none (.tuple Atom.unit bindings (fuel + 1) []) =
      (.returning [(Atom.unit, bindings)], []) := rfl

def tupleBindings : Bindings := ⟨[("held", .symbol "value")], [("left", "right")]⟩
def nestedTuple : Atom := .expression [.var "head", .expression [.var "first", .var "last"]]

theorem singleton_variable_keeps_wrapper :
    (Task.tuple (.expression [.var "x"]) tupleBindings 4 []).denote Space.empty GroundedDispatch.none =
      [(.expression [.var "x"], tupleBindings)] := by decide

theorem nested_tail_does_not_flatten :
    (Task.tuple nestedTuple tupleBindings 16 []).denote Space.empty GroundedDispatch.none =
      [(nestedTuple, tupleBindings)] := by decide

theorem singleton_empty_propagates :
    (Task.tuple (.expression [Atom.empty]) tupleBindings 4 []).denote Space.empty GroundedDispatch.none =
      [(Atom.empty, tupleBindings)] := by decide

theorem singleton_error_propagates :
    (Task.tuple (.expression [.expression [.symbol "Error", .symbol "held", .symbol "problem"]])
      tupleBindings 4 []).denote Space.empty GroundedDispatch.none =
      [(.expression [.symbol "Error", .symbol "held", .symbol "problem"], tupleBindings)] := by decide

theorem singleton_result_is_not_unwrapped :
    (Task.tuple (.expression [.var "x"]) tupleBindings 4 []).denote Space.empty GroundedDispatch.none ≠
      [(.var "x", tupleBindings)] := by decide

theorem empty_tuple_is_not_dropped :
    (Task.tuple Atom.unit tupleBindings 1 []).denote Space.empty GroundedDispatch.none ≠ [] := by decide

/-- The recursive source tests a completed tail before prepending its head. -/
theorem constructed_error_tail_propagates :
    (Task.tuple (.expression [.symbol "a", .symbol "Error"]) tupleBindings 8 []).denote
      Space.empty GroundedDispatch.none = [(.expression [.symbol "Error"], tupleBindings)] := by decide

theorem tuple_duplicate_occurrences_keep_wrappers :
    values (.tuple (.expression [.expression [.symbol "duplicate"]]) Bindings.empty 32 []) =
      [.expression [a], .expression [a], .expression [b]] := by decide

theorem nested_tuple_duplicate_occurrences_keep_wrappers :
    values (.tuple (.expression [.symbol "tag", .expression [.expression [.symbol "duplicate"]]])
      Bindings.empty 32 []) =
      [.expression [.symbol "tag", .expression [a]],
        .expression [.symbol "tag", .expression [a]],
        .expression [.symbol "tag", .expression [b]]] := by decide

private def errorCompletionValues : List Atom :=
  [.symbol "a", .symbol "Error", .symbol "b", .symbol "Error", .symbol "c", .symbol "c"]

private theorem errorCompletionValues_quiescent :
    ∀ value ∈ errorCompletionValues, SelfEvalQuiescent Space.empty GroundedDispatch.none 0 value := by
  intro value member
  simp only [errorCompletionValues, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact .symbol rfl rfl

/-- Completion selects the rightmost Error suffix and retains its duplicate entries. -/
theorem completed_tuple_rightmost_error (bindings : Bindings) :
    InterpretTuple Space.empty GroundedDispatch.none (.expression errorCompletionValues) bindings
      (.expression [.symbol "Error", .symbol "c", .symbol "c"], bindings) := by
  exact tuple_rightmost_error_of_quiescent_elements
    [.symbol "a", .symbol "Error", .symbol "b"] [.symbol "c", .symbol "c"] bindings
    errorCompletionValues_quiescent (by decide)

theorem completed_tuple_rejects_earlier_error_suffix (bindings : Bindings) :
    ¬InterpretTuple Space.empty GroundedDispatch.none (.expression errorCompletionValues) bindings
      (.expression [.symbol "Error", .symbol "b", .symbol "Error", .symbol "c", .symbol "c"],
        bindings) := by
  intro interpreted
  have exactResult := tuple_rightmost_error_unique_of_quiescent_elements
    [.symbol "a", .symbol "Error", .symbol "b"] [.symbol "c", .symbol "c"]
    errorCompletionValues_quiescent (by decide) interpreted
  have distinct : (.expression
      [.symbol "Error", .symbol "b", .symbol "Error", .symbol "c", .symbol "c"] : Atom) ≠
        .expression [.symbol "Error", .symbol "c", .symbol "c"] := by decide
  exact distinct (congrArg Prod.fst exactResult)

theorem retained_tuple_rightmost_error :
    (Task.tuple (.expression errorCompletionValues) tupleBindings 16 []).denote
      Space.empty GroundedDispatch.none =
      [(.expression [.symbol "Error", .symbol "c", .symbol "c"], tupleBindings)] := by decide

def tupleInitial : Configuration :=
  Configuration.initial Space.empty (.tuple nestedTuple tupleBindings 16 [])

def tupleSaved : Configuration :=
  ⟨Space.empty, .work (.atom (.var "head") Atom.undefinedType tupleBindings 15
      [.expression [.expression [.var "first", .var "last"]]]),
    [.tupleHeads (.expression [.expression [.var "first", .var "last"]]) 15 []], []⟩

theorem tuple_pauses_before_first_child :
    (machine GroundedDispatch.none).run 1 tupleInitial = ([], .exhausted tupleSaved) := rfl

theorem encoded_tuple_resume (continuing : Nat) :
    (RecursiveDataExecution.dataMachine GroundedDispatch.none).run (1 + continuing)
        (configurationData tupleInitial) =
      (((RecursiveDataExecution.dataMachine GroundedDispatch.none).run continuing
          (configurationData tupleSaved)).1,
        ((RecursiveDataExecution.dataMachine GroundedDispatch.none).run continuing
          (configurationData tupleSaved)).2) := by
  simpa using RecursiveDataExecution.resume_after_prefix GroundedDispatch.none 1 continuing
    tupleInitial tupleSaved [] tuple_pauses_before_first_child

theorem tuple_resume_retains_nested_result :
    ∃ final, (machine GroundedDispatch.none).run
        (RecursiveProductivity.finishingBudget GroundedDispatch.none tupleSaved) tupleSaved =
      ([(nestedTuple, tupleBindings)], .finished final) := by
  have completed := RecursiveProductivity.finishes_with_more_budget GroundedDispatch.none
    tupleSaved (RecursiveProductivity.finishingBudget GroundedDispatch.none tupleSaved) le_rfl
  have remaining : tupleSaved.remaining GroundedDispatch.none = [(nestedTuple, tupleBindings)] := by decide
  simpa only [remaining] using completed

/-! ## Ordinary call return ownership -/

namespace OrdinaryReturn

private def frozen : Atom := .expression [.symbol "freeze", .grounded (.int 7)]
private def source : Space := Space.ofList [.expression [.symbol "=", frozen, Atom.notReducible]]
private def reached : Bindings := ⟨[("x", .symbol "A")], []⟩
private def supplied : Atom := .expression [.symbol "supply"]
private def beforeArguments : Atom := .expression [.symbol "freeze", supplied]
private def reducingSource : Space := Space.ofList
  (source.atoms ++ [.expression [.symbol "=", supplied, .grounded (.int 7)]])

/-- Refusal restores the assembled invocation after its arguments have run. -/
theorem restored_post_argument_call :
    (evalAtom reducingSource GroundedDispatch.none beforeArguments Atom.undefinedType
      Bindings.empty 64 []).map Prod.fst = [frozen] := by decide +kernel

/-- Neither the reserved protocol value nor the pre-argument call is returned. -/
theorem protocol_and_original_syntax_are_not_results :
    (evalAtom reducingSource GroundedDispatch.none beforeArguments Atom.undefinedType
      Bindings.empty 64 []).map Prod.fst ≠ [Atom.notReducible] ∧
    (evalAtom reducingSource GroundedDispatch.none beforeArguments Atom.undefinedType
      Bindings.empty 64 []).map Prod.fst ≠ [beforeArguments] := by decide +kernel

/-- The administrative return itself needs no further evaluation depth and
keeps the frame reached by the body. -/
theorem refusal_keeps_reached_binding_at_zero_depth :
    (Checked.machine GroundedDispatch.none).run 3
      ⟨source, .work (.returned frozen Atom.notReducible Atom.undefinedType reached 0 []), [], []⟩ =
      ([(frozen, reached)], .finished ⟨source, .returning [], [], [(frozen, reached)]⟩) := rfl

/-- Stopped results bypass further evaluation even under a rejecting callback. -/
theorem stopped_bypasses_child :
    ordinaryCallReturn frozen Atom.empty reached (fun _ _ => [(.symbol "wrong-child", reached)]) =
      [(Atom.empty, reached)] ∧
    ordinaryCallReturn frozen (.expression [.symbol "Error"]) reached
      (fun _ _ => [(.symbol "wrong-child", reached)]) = [(.expression [.symbol "Error"], reached)] := ⟨rfl, rfl⟩

/-- A normal return still owes its child evaluation; depth zero cannot certify
an empty completed result. -/
theorem ordinary_return_waits_for_evaluation :
    (Checked.machine GroundedDispatch.none).run 2
      ⟨source, .work (.returned frozen (.symbol "next") Atom.undefinedType reached 0 []), [], []⟩ =
      ([], .suspended .evaluationDepth
        ⟨source, .work (.atom (.symbol "next") Atom.undefinedType reached 0 []), [], []⟩) := rfl

/-- Two equal refusal replies are two occurrences under the same return owner. -/
theorem duplicate_refusals_remain_two :
    (Task.returns frozen Atom.undefinedType 0
      [(Atom.notReducible, reached), (Atom.notReducible, reached)] []).denote
        source GroundedDispatch.none = [(frozen, reached), (frozen, reached)] := rfl

/-- The saved return phase carries its original invocation and reached frame. -/
theorem return_checkpoint_roundtrip :
    readTask (taskData (.returned frozen Atom.notReducible Atom.undefinedType reached 0 [])) =
      some (.returned frozen Atom.notReducible Atom.undefinedType reached 0 []) :=
  readTask_taskData _

/-- Ordinary values use the child result as-is, including a completed empty list. -/
theorem empty_child_result_is_not_restored :
    ordinaryCallReturn frozen (.symbol "next") reached (fun _ _ => []) = [] := rfl

end OrdinaryReturn

end Mettapedia.Languages.MeTTa.HE.RecursiveControls


set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.RecursiveControls.Invocation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Syntax routing agrees with the independent classifier. This is separate
from correspondence of the selected instruction's execution. -/
theorem classifier_agrees (value : Atom) :
    minimalInstruction value = Spec.Eval.Minimal.embeddedInstruction value := by
  cases value with
  | symbol _ | var _ | grounded _ => rfl
  | expression parts =>
    cases parts with
    | nil => rfl
    | cons head tail => cases head <;> rfl

def seven : Atom := .grounded (.int 7)
def returned (value : Atom) : Atom := .expression [.symbol "return", value]
def function (body : Atom) : Atom := .expression [.symbol "function", body]
def correlated : Atom := function (.expression
  [.symbol "unify", .var "x", .symbol "B", returned Spec.Eval.Minimal.UnifyReadoutControls.template, .symbol "Fail"])

def completeWith (dispatch : GroundedDispatch) (space : Space) (task : Task) : ResultSet × Bool :=
  let execution := (Checked.machine dispatch).run 200
    (Configuration.initial space task)
  (execution.1, match execution.2 with | .finished _ => true | _ => false)

def complete (space : Space) (task : Task) : ResultSet × Bool :=
  completeWith GroundedDispatch.none space task

/-- This is the executable guarded worker, including its full saved return
stack and actual publication, not an evaluator approximation alone. -/
theorem immediate_function_finishes :
    complete Space.empty (.invocation .raw (function (returned seven)) Bindings.empty 30) =
      ([(seven, Bindings.empty)], true) := by decide

theorem binding_change_reads_both_pending_uses :
    complete Space.empty (.invocation .raw correlated Bindings.empty 30) =
      ([(Spec.Eval.Minimal.UnifyReadoutControls.observed, Spec.Eval.Minimal.UnifyReadoutControls.outputBindings)], true) := by decide

theorem successful_unify_reads_selected_branch :
    complete Space.empty (.primitive Spec.Eval.Minimal.UnifyReadoutControls.invocation Bindings.empty 30) =
      ([(Spec.Eval.Minimal.UnifyReadoutControls.observed, Spec.Eval.Minimal.UnifyReadoutControls.outputBindings)], true) := by decide

theorem refused_unify_keeps_unread_fallback :
    complete Space.empty (.primitive
      (.expression [.symbol "unify", .symbol "A", .symbol "C", Spec.Eval.Minimal.UnifyReadoutControls.template, .var "x"])
      Spec.Eval.Minimal.UnifyReadoutControls.outputBindings 30) =
      ([(.var "x", Spec.Eval.Minimal.UnifyReadoutControls.outputBindings)], true) := by decide

def named : Atom := .expression [.symbol "foo"]
def missingReturn : Atom := function (.expression [.symbol "SomeValue"])

theorem completed_function_keeps_actual_caller :
    complete Space.empty (.produced missingReturn Bindings.empty 30 [] (some named)) =
      ([(Atom.error named (.symbol "NoReturn"), Bindings.empty)], true) := by decide

theorem completed_provenance_does_not_enter_function :
    complete Space.empty (.produced missingReturn Bindings.empty 30 [] (some named) .completed) =
      ([(missingReturn, Bindings.empty)], true) := by decide

theorem completed_not_reducible_is_data :
    complete Space.empty (.completed Atom.notReducible Atom.atomType Bindings.empty 30) =
      ([(Atom.notReducible, Bindings.empty)], true) := by decide

def fromEmpty : Atom := .expression [.symbol "chain", Atom.empty, .var "saved", returned seven]

theorem internal_empty_is_not_dropped :
    complete Space.empty (.invocation .raw (function fromEmpty) Bindings.empty 30) =
      ([(seven, Bindings.empty)], true) := by decide

def fcall : Atom := .expression [.symbol "f"]
def value : Atom := .symbol "Value"
def fspace : Space := Space.ofList [.expression [.symbol "=", fcall, value]]

namespace TypedFScopedWorker

open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open FirstSuccessRecursiveStrategy FirstSuccessRecursiveExecution
open FirstSuccessSourceExecution FirstSuccessSourceApplicability
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation
open Spec.Match.Merge
open FirstSuccessScopedAdequacy
open FirstSuccessScopedAdequacy.ScopedRetainedRelation
open FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication

def typedFSignature : SelectedTypePolicy :=
  ⟨functionType [Atom.symbolType], [], Atom.symbolType, rfl⟩

def recursiveCall : Atom := .expression [.symbol "g"]

def recursiveEquation : Atom :=
  .expression [.symbol "=", recursiveCall, fcall]

def typedFSpace : Space :=
  Space.ofList
    [annotated (.symbol "f") typedFSignature.functionType,
      .expression [.symbol "=", fcall, value], recursiveEquation]

def typedFWork : EquationWork :=
  ⟨1, fcall, value, fcall, value, Bindings.empty⟩

def recursiveWork : EquationWork :=
  ⟨2, recursiveCall, fcall, recursiveCall, fcall, Bindings.empty⟩

private theorem typedF_closed : ClosedTypeAnnotations typedFSpace :=
  (closedColonAnnotations_of_bool (space := typedFSpace) (by decide +kernel)).closedTypeAnnotations

private theorem fcall_closed_alpha (live : List Atom) :
    AlphaVariantRel live fcall Bindings.empty fcall value fcall value := by
  refine ⟨id, Function.injective_id, ?_, ?_, ?_⟩
  · simpa only [ScopeObservation.renameTypeVars_id] using
      EquationFreshening.rename_alpha id fcall
  · simpa only [ScopeObservation.renameTypeVars_id] using
      EquationFreshening.rename_alpha id value
  · intro name occurs
    rcases occurs with occurs | occurs
    · cases occurs with
      | expression member child =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          subst member
          cases child
    · cases occurs

private theorem gcall_closed_alpha (live : List Atom) :
    AlphaVariantRel live fcall Bindings.empty recursiveCall fcall
      recursiveCall fcall := by
  refine ⟨id, Function.injective_id, ?_, ?_, ?_⟩
  · simpa only [ScopeObservation.renameTypeVars_id] using
      EquationFreshening.rename_alpha id recursiveCall
  · simpa only [ScopeObservation.renameTypeVars_id] using
      EquationFreshening.rename_alpha id fcall
  · intro name occurs
    rcases occurs with occurs | occurs
    · cases occurs with
      | expression member child =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          subst member
          cases child
    · cases occurs with
      | expression member child =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          subst member
          cases child

private theorem recursive_row_miss (live : List Atom) :
    EquationRowResultsRel live fcall Bindings.empty 2 recursiveEquation [] := by
  apply EquationRowResultsRel.miss 2 recursiveCall fcall recursiveCall fcall
    (gcall_closed_alpha live)
  intro pattern body renamed matched output viable
  obtain ⟨_, _, patternRenamed, _, _⟩ := renamed
  have same : pattern = recursiveCall := by
    simpa only [Spec.Type.RuntimeRefinement.renameTypeVars, List.map_cons, List.map_nil,
      recursiveCall] using EquationFreshening.alphaRename_eq patternRenamed
  subst pattern
  cases viable.1 with
  | expression children _ =>
      cases children with
      | cons first _ _ => exact symbol_mismatch_not_match (by decide) _ first

private theorem fcall_miss_alpha (live : List Atom) :
    AlphaVariantRel live recursiveCall Bindings.empty fcall value fcall value := by
  refine ⟨id, Function.injective_id, ?_, ?_, ?_⟩
  · simpa only [ScopeObservation.renameTypeVars_id] using
      EquationFreshening.rename_alpha id fcall
  · simpa only [ScopeObservation.renameTypeVars_id] using
      EquationFreshening.rename_alpha id value
  · intro name occurs
    rcases occurs with occurs | occurs
    · cases occurs with
      | expression member child =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          subst member
          cases child
    · cases occurs

private theorem fcall_row_miss_for_recursive (live : List Atom) :
    EquationRowResultsRel live recursiveCall Bindings.empty 1
      (.expression [.symbol "=", fcall, value]) [] := by
  apply EquationRowResultsRel.miss 1 fcall value fcall value (fcall_miss_alpha live)
  intro pattern body renamed matched output viable
  obtain ⟨_, _, patternRenamed, _, _⟩ := renamed
  have same : pattern = fcall := by
    simpa only [Spec.Type.RuntimeRefinement.renameTypeVars, List.map_cons, List.map_nil,
      fcall] using EquationFreshening.alphaRename_eq patternRenamed
  subst pattern
  cases viable.1 with
  | expression children _ =>
      cases children with
      | cons first _ _ => exact symbol_mismatch_not_match (by decide) _ first

private theorem recursive_hit_alpha (live : List Atom) :
    AlphaVariantRel live recursiveCall Bindings.empty recursiveCall fcall
      recursiveCall fcall := by
  refine ⟨id, Function.injective_id, ?_, ?_, ?_⟩
  · simpa only [ScopeObservation.renameTypeVars_id] using
      EquationFreshening.rename_alpha id recursiveCall
  · simpa only [ScopeObservation.renameTypeVars_id] using
      EquationFreshening.rename_alpha id fcall
  · intro name occurs
    rcases occurs with occurs | occurs
    · cases occurs with
      | expression member child =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          subst member
          cases child
    · cases occurs with
      | expression member child =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          subst member
          cases child

private theorem recursive_identical_match :
    MatchRel equalityGroundedSemantic recursiveCall recursiveCall Bindings.empty := by
  exact .expression
    (.cons (.symSym "g" semanticLoopFree_empty) (.mk (.refl []) .nil) .nil)
    semanticLoopFree_empty

private theorem empty_logical_merge :
    LogicalMergeRel Bindings.empty Bindings.empty Bindings.empty := by
  refine ⟨BindingSourceAgreement.refl _, fun name => .var name, ?_⟩
  simp [Spec.Type.RuntimeRefinement.TypeBindingSatisfied, Bindings.empty]

private theorem fcall_identical_match :
    MatchRel equalityGroundedSemantic fcall fcall Bindings.empty := by
  exact .expression
    (.cons (.symSym "f" semanticLoopFree_empty) (.mk (.refl []) .nil) .nil)
    semanticLoopFree_empty

private theorem typedFSignature_identical_match :
    TypeMatchRel typedFSignature.functionType typedFSignature.functionType
      Bindings.empty Bindings.empty := by
  apply TypeMatchRel.structural <;> try decide
  · exact .expression
      (.cons (.symSym "->" semanticLoopFree_empty) (.mk (.refl []) .nil)
        (.cons (.symSym "Symbol" semanticLoopFree_empty) (.mk (.refl []) .nil) .nil))
      semanticLoopFree_empty
  · exact .mk (.refl []) .nil

theorem typedF_frontier (live : List Atom) :
    EquationFrontierRel typedFSpace live fcall Bindings.empty [typedFWork] := by
  apply EquationFrontierRel.completed (blocks := [[], [typedFWork], []])
  exact .cons
    (.irrelevant 0 (annotated (.symbol "f") typedFSignature.functionType)
      (by intro left right bad; simp [annotated] at bad))
    (.cons
      (.hit 1 fcall value fcall value Bindings.empty Bindings.empty
        (fcall_closed_alpha live) fcall_identical_match empty_logical_merge)
      (.cons (recursive_row_miss live) .nil))

theorem recursive_frontier (live : List Atom) :
    EquationFrontierRel typedFSpace live recursiveCall Bindings.empty [recursiveWork] := by
  apply EquationFrontierRel.completed (blocks := [[], [], [recursiveWork]])
  exact .cons
    (.irrelevant 0 (annotated (.symbol "f") typedFSignature.functionType)
      (by intro left right bad; simp [annotated] at bad))
    (.cons (fcall_row_miss_for_recursive live)
      (.cons
        (.hit 2 recursiveCall fcall recursiveCall fcall Bindings.empty Bindings.empty
          (recursive_hit_alpha live) recursive_identical_match empty_logical_merge)
        .nil))

theorem typedF_scoped_type_query (protectedScope : List String) (expected : Atom) :
    Completed.scopedLookup protectedScope typedFSpace Completed.Frame.empty.bindings
      (.symbol "f") expected [typedFSignature.functionType] := by
  refine ⟨[typedFSignature.functionType], ?_, .cons ?_ (.nil _)⟩
  · apply StorageTypesRel.symbolKnown
    · exact .hit
        (.skip (by intro type; simp)
          (.skip (by intro type; simp [recursiveEquation, recursiveCall, fcall]) .nil))
    · simp
  · exact ⟨id, Function.injective_id, by simp,
      by simp [typedFSignature, functionType, TypeSubst.typeVars, TypeSubst.typeVarsList,
        Atom.symbolType]⟩

theorem typedF_scoped_operator_query :
    Completed.scopedLookup
      (invocationTypeScope [] [] fcall Atom.undefinedType Completed.Frame.empty.bindings)
      typedFSpace Completed.Frame.empty.bindings (.symbol "f") Atom.undefinedType
      [typedFSignature.functionType] :=
  typedF_scoped_type_query _ _

theorem typedF_contextual_selected :
    Completed.InvocationSelectionRel typedFSpace Completed.scopedLookup Policy.unmarked
      [] [] fcall (.symbol "f") Atom.undefinedType Completed.Frame.empty
      (.selected typedFSignature [Completed.Frame.empty]) := by
  let cLookup := Completed.scopedLookup
    (invocationTypeScope [] [] fcall Atom.undefinedType Completed.Frame.empty.bindings)
    typedFSpace
  have returned : Completed.TypeCheckRel Policy.unmarked Atom.undefinedType
      Completed.Frame.empty typedFSignature.returnType (.inr Completed.Frame.empty) :=
    .accepted (.unchanged
      (Completed.Frame.empty.preserved_type_match Policy.unmarked
        (.undefinedLeft typedFSignature.returnType Completed.Frame.empty.bindings)))
  have checked : Completed.ApplicationChecksRel typedFSpace cLookup Policy.unmarked
      fcall Atom.undefinedType typedFSignature Completed.Frame.empty [Completed.Frame.empty] [] := by
    simpa only [fcall, Completed.checkedFrames, Completed.checkedFailures,
      List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append,
      List.map_nil] using
      (Completed.ApplicationChecksRel.checked rfl
        (Completed.ApplicabilityArgumentsRel.nil (space := typedFSpace) (lookup := cLookup)
          (policy := Policy.unmarked) (expression := fcall) (position := 1)
          (frames := [Completed.Frame.empty]))
        (.cons returned .nil))
  exact ⟨[typedFSignature.functionType], typedF_scoped_operator_query,
    .selected checked (by simp)⟩

theorem typedF_worker_selected :
    let state : Configuration :=
      ⟨typedFSpace,
        .work (.functions fcall Atom.undefinedType Bindings.empty 10
          [typedFSignature.functionType]),
        [.filter], []⟩
    FirstSuccessRecursiveStrategy.select (lookup := invocationTypes state)
      typedFSpace fcall Atom.undefinedType Bindings.empty 10
      [typedFSignature.functionType] = .selected typedFSignature [Bindings.empty] := by
  intro state
  have applicable :
      checkIfFunctionTypeIsApplicable (lookup := invocationTypes state)
        fcall typedFSignature.functionType Atom.undefinedType typedFSpace Bindings.empty 10 =
        .inr [Bindings.empty] := by
    decide +kernel
  simp only [typedFSignature, functionType] at applicable ⊢
  simp only [FirstSuccessRecursiveStrategy.select,
    FirstSuccessRecursiveStrategy.readPolicy]
  rw [applicable]
  rfl

/-- The closed `f` signature is independent of every retained worker frame and
published prefix.  This is the framing law needed to reuse the selected call
inside a recursive equation body. -/
theorem typedF_invocation_types
    (control : Control) (stack : List RecursiveTasks.Frame) (emitted : ResultSet)
    (bindings : Bindings) (expected : Atom) :
    invocationTypes ⟨typedFSpace, control, stack, emitted⟩ bindings
      (.symbol "f") expected = [typedFSignature.functionType] := by
  rw [invocationTypes_closed]
  · change getAtomTypes typedFSpace (.symbol "f") = [typedFSignature.functionType]
    decide +kernel
  · intro signature present
    have equal : signature = typedFSignature.functionType := by
      simpa [typedFSpace, fspace, Space.add, Space.ofList, getAtomTypes,
        getAnnotatedTypes, annotated, recursiveEquation, recursiveCall] using present
    subst signature
    change atomVariables typedFSignature.functionType = []
    decide +kernel

/-- Selection of the closed nullary `f` declaration is likewise independent
of the administrative caller stack. -/
theorem typedF_worker_selected_at
    (wStack : List RecursiveTasks.Frame) (wEmitted : ResultSet) :
    let state : Configuration :=
      ⟨typedFSpace,
        .work (.functions fcall Atom.undefinedType Bindings.empty 10
          [typedFSignature.functionType]),
        .filter :: wStack, wEmitted⟩
    FirstSuccessRecursiveStrategy.select (lookup := invocationTypes state)
      typedFSpace fcall Atom.undefinedType Bindings.empty 10
      [typedFSignature.functionType] = .selected typedFSignature [Bindings.empty] := by
  intro state
  have applicable :
      checkIfFunctionTypeIsApplicable (lookup := invocationTypes state)
        fcall typedFSignature.functionType Atom.undefinedType typedFSpace Bindings.empty 10 =
        .inr [Bindings.empty] := by
    rfl
  simp only [typedFSignature, functionType] at applicable ⊢
  simp only [FirstSuccessRecursiveStrategy.select,
    FirstSuccessRecursiveStrategy.readPolicy]
  rw [applicable]
  rfl

/-- Structural selected-entry evidence for `f` above any administrative
worker stack and emitted prefix. -/
theorem typedF_entry_at
    (wStack : List RecursiveTasks.Frame) (wEmitted : ResultSet) :
    ScopedSelectedFunctionEntry typedFSpace Policy.unmarked
      (.symbol "f") [] (.symbol "f") Atom.undefinedType
      Bindings.empty Bindings.empty 8 [] []
      (.expression .active [.symbol "f"]) (.symbol "f") []
      Completed.Frame.empty Completed.Frame.empty .active typedFSignature
      [typedFSignature.functionType] wStack wEmitted := by
  refine
    { entry_ready := by
        simpa only [Entry.Value.erase, List.map_cons, List.map_nil] using
          (ScopedAtomEntryReady.initial Policy.unmarked
            (.expression .active [.symbol "f"]) (Or.inl rfl))
      read_shape := by simp
      operator_erase := by simp only [Entry.Value.erase]
      arguments_erase := rfl
      input_not_stopped := by decide
      expected_not_atom := by decide
      expected_not_expression := by decide
      candidate_eq := by
        simpa only [fcall] using
          typedF_invocation_types
            (.work (.expression fcall Atom.undefinedType Bindings.empty 11 []))
            (.filter :: wStack) wEmitted Bindings.empty Atom.undefinedType
      selection_ready := by rfl
      worker_selected := by
        simpa only [fcall] using typedF_worker_selected_at wStack wEmitted
      contextual_selected := typedF_contextual_selected
      input_activation := SourceBindingComparison.FrameRelated.of_principal
        PrincipalBindingFrame.empty (.refl _)
      selected_activation := SourceBindingComparison.FrameRelated.of_principal
        PrincipalBindingFrame.empty (.refl _)
      arity_eq := rfl
      argument_types_eq := rfl
      operator_not_stopped := by decide }

theorem typedF_entry :
    ScopedSelectedFunctionEntry typedFSpace Policy.unmarked
      (.symbol "f") [] (.symbol "f") Atom.undefinedType
      Bindings.empty Bindings.empty 8 [] []
      (.expression .active [.symbol "f"]) (.symbol "f") []
      Completed.Frame.empty Completed.Frame.empty .active typedFSignature
      [typedFSignature.functionType] [] [] :=
  typedF_entry_at [] []

/-- Closed-signature operator casts are stable under administrative framing.
The worker calculation and the completed cast judgment still remain explicit
parts of the admission. -/
theorem typedF_operator_admission_at
    (wLive cLive : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame) (wEmitted : ResultSet) :
    ScopedCastAdmission typedFSpace Policy.unmarked
      (.symbol "f") typedFSignature.functionType (.symbol "f")
      Bindings.empty Completed.Frame.empty 8 wLive cLive scope wStack wEmitted
      [(.symbol "f", Bindings.empty)]
      [((Completed.Frame.empty.read Policy.unmarked (.symbol "f")).erase,
        Completed.Frame.empty.bindings)]
      [(Completed.Frame.empty.read Policy.unmarked (.symbol "f"), Completed.Frame.empty)] := by
  have ready : ScopedAtomEntryReady Policy.unmarked (.symbol "f") (.symbol "f")
      Completed.Frame.empty := by
    simpa only [Entry.Value.erase] using
      (ScopedAtomEntryReady.initial Policy.unmarked (.symbol "f") (Or.inl rfl))
  have entered : Entry.Rel Policy.unmarked.reentry .active (.symbol "f")
      typedFSignature.functionType .cast :=
    Entry.Rel.cast (policy := Policy.unmarked.reentry) (status := .active)
      (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.symbol "f")
      (by decide) (Or.inl ⟨"f", rfl⟩) (by intro impossible; cases impossible)
  apply ScopedCastAdmission.unchanged
  · exact ready
  · simpa only [Completed.Frame.read_empty, Entry.Value.status, Entry.Value.erase] using entered
  · change typeCastCovered (.symbol "f") typedFSignature.functionType typedFSpace
      Bindings.empty 8
        (invocationTypes
          ⟨typedFSpace,
            .work (.atom (.symbol "f") typedFSignature.functionType Bindings.empty 9 wLive),
            wStack, wEmitted⟩) = true
    rw [invocationTypes_eq_rawTypeLookup_of_closed typedF_closed]
    change typeCastCovered (.symbol "f") typedFSignature.functionType typedFSpace
      Bindings.empty 8 (rawTypeLookup typedFSpace) = true
    decide +kernel
  · change typeCast (.symbol "f") typedFSignature.functionType typedFSpace
      Bindings.empty 8
        (invocationTypes
          ⟨typedFSpace,
            .work (.atom (.symbol "f") typedFSignature.functionType Bindings.empty 9 wLive),
            wStack, wEmitted⟩) = [(.symbol "f", Bindings.empty)]
    rw [invocationTypes_eq_rawTypeLookup_of_closed typedF_closed]
    change typeCast (.symbol "f") typedFSignature.functionType typedFSpace
      Bindings.empty 8 (rawTypeLookup typedFSpace) = [(.symbol "f", Bindings.empty)]
    decide +kernel
  · simpa only [Completed.Frame.read_empty, Entry.Value.erase] using
      (typedF_scoped_type_query
        (invocationTypeScope scope cLive (.symbol "f") typedFSignature.functionType
          Completed.Frame.empty.bindings)
        typedFSignature.functionType)
  · exact Completed.Frame.empty.preserved_type_match Policy.unmarked
      typedFSignature_identical_match
  · exact SourceBindingComparison.FrameRelated.of_principal
      PrincipalBindingFrame.empty (.refl _)

/-- A selected nullary call uses the declared arrow, evaluates its operator,
visits its physical equation, and returns the equation body above any related
administrative caller stacks. -/
theorem typedF_selected_derivation_at
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    let ctxCall : Entry.Value := .expression .active [.symbol "f"]
    let ctxValue : Entry.Value := .symbol "Value"
    ScopedAtomDerivation typedFSpace HE.GroundedDispatch.none noHost Policy.unmarked
      wEmitted cEmitted 12 [] [] [] fcall ctxCall Atom.undefinedType Bindings.empty
      Completed.Frame.empty wStack cStack 42
      [(value, Bindings.empty)] [(ctxValue, Completed.Frame.empty)] := by
  intro ctxCall ctxValue
  let resultType : Atom := Atom.symbolType
  let wCallStack : List RecursiveTasks.Frame :=
    .calls resultType 10 [] ::
      .append (.bindingAlternatives fcall typedFSignature.functionType resultType 10 [] []) ::
      .filter :: wStack
  let cCallStack : List RecursiveTasks.Contextual.Continuation :=
    .calls [] [] resultType ::
      .append (.invocations [] [] Atom.undefinedType typedFSignature (.symbol "f") [] []) ::
      .publish fcall :: cStack
  let wOperatorStack : List RecursiveTasks.Frame :=
    .heads typedFSignature.functionType [] 9 [resultType] :: wCallStack
  let cOperatorStack : List RecursiveTasks.Contextual.Continuation :=
    .functionHeads [resultType] [] [] :: cCallStack
  let wArgsStack : List RecursiveTasks.Frame :=
    .functionTail (.symbol "f") ::
      .append (.heads typedFSignature.functionType [] 9 [] [resultType]) ::
      .calls resultType 10 [] ::
      .append (.bindingAlternatives fcall typedFSignature.functionType resultType 10 [] []) ::
      .filter :: wStack
  let cArgsStack : List RecursiveTasks.Contextual.Continuation :=
    .functionAssemble (.symbol "f") ::
      .append (.functionBranches [resultType] [] [] []) ::
      .calls [] [] resultType ::
      .append (.invocations [] [] Atom.undefinedType typedFSignature (.symbol "f") [] []) ::
      .publish fcall :: cStack
  let wDrainStack : List RecursiveTasks.Frame :=
    .append (.calls resultType 10 [] []) ::
      .append (.bindingAlternatives fcall typedFSignature.functionType resultType 10 [] []) ::
      .filter :: wStack
  let cDrainStack : List RecursiveTasks.Contextual.Continuation :=
    .append (.calls [] [] resultType []) ::
      .append (.invocations [] [] Atom.undefinedType typedFSignature (.symbol "f") [] []) ::
      .publish fcall :: cStack
  have actEmpty : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
    SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)
  have opAdmission : ScopedCastAdmission typedFSpace Policy.unmarked
      (.symbol "f") typedFSignature.functionType (.symbol "f")
      Bindings.empty Completed.Frame.empty 8
      [typedFSignature.functionType, resultType]
      [typedFSignature.functionType, resultType] [] wOperatorStack wEmitted
      [(.symbol "f", Bindings.empty)]
      [((Completed.Frame.empty.read Policy.unmarked (.symbol "f")).erase,
        Completed.Frame.empty.bindings)]
      [(Completed.Frame.empty.read Policy.unmarked (.symbol "f"), Completed.Frame.empty)] :=
    typedF_operator_admission_at
      [typedFSignature.functionType, resultType]
      [typedFSignature.functionType, resultType] [] wOperatorStack wEmitted
  have operatorDerivation : ScopedAtomDerivation typedFSpace HE.GroundedDispatch.none
      noHost Policy.unmarked wEmitted cEmitted 9
      [typedFSignature.functionType, resultType]
      [typedFSignature.functionType, resultType] []
      (.symbol "f") (.symbol "f") typedFSignature.functionType Bindings.empty
      Completed.Frame.empty wOperatorStack cOperatorStack 1
      [(.symbol "f", Bindings.empty)] [(.symbol "f", Completed.Frame.empty)] := by
    simpa only [Completed.Frame.read_empty] using
      (ScopedAtomDerivation.cast 8
        [typedFSignature.functionType, resultType] [typedFSignature.functionType, resultType] []
        (.symbol "f") typedFSignature.functionType (.symbol "f")
        Bindings.empty Completed.Frame.empty wOperatorStack cOperatorStack
        [(.symbol "f", Bindings.empty)]
        [((Completed.Frame.empty.read Policy.unmarked (.symbol "f")).erase,
          Completed.Frame.empty.bindings)]
        [(Completed.Frame.empty.read Policy.unmarked (.symbol "f"), Completed.Frame.empty)]
        opAdmission)
  have argumentsDerivation : ScopedArgsDerivation typedFSpace HE.GroundedDispatch.none
      noHost Policy.unmarked wEmitted cEmitted [] 9 1 [(.symbol "f"), resultType]
      [] [] [] [] [] Bindings.empty Completed.Frame.empty Bindings.empty
      Completed.Frame.empty wArgsStack cArgsStack := by
    exact ScopedArgsDerivation.nil [] 8 [(.symbol "f"), resultType]
      Bindings.empty Completed.Frame.empty wArgsStack cArgsStack actEmpty
  have eqReady :
      (matchCovered 9 (.merge Bindings.empty
          (Spec.Type.Presentation.BindingTheory.aliasConstraints Bindings.empty)) &&
        (mergeBindings Bindings.empty
          (Spec.Type.Presentation.BindingTheory.aliasConstraints Bindings.empty) 9).all fun merged =>
          (merged.hasLoop || merged.applyFullCovered value 9)) = true := by
    decide +kernel
  have mergeFilterEq :
      ((mergeBindings Bindings.empty
          (Spec.Type.Presentation.BindingTheory.aliasConstraints Bindings.empty) 9).filterMap fun merged =>
        if merged.hasLoop then none else some (merged.applyFull value 9, merged)) =
      [(value, Bindings.empty)] := by
    decide +kernel
  have callUnify : Entry.Value.UnifyRel Policy.unmarked.rebuilding
      Completed.Frame.empty.environment ctxCall (Entry.Value.ofAtom typedFWork.pattern)
      Completed.Frame.empty.environment := by
    have ctxCallEq : ctxCall = Entry.Value.ofAtom fcall := by
      simp [ctxCall, fcall, Entry.Value.ofAtom]
    rw [ctxCallEq]
    exact
      (Entry.Value.UnifyRel.ordinary
        (Entry.Value.AppliedUnifyRel.identical (policy := Policy.unmarked.rebuilding)
          (environment := []) (by rfl)))
  have valueReady : ScopedAtomEntryReady Policy.unmarked value ctxValue
      Completed.Frame.empty := by
    simpa only [ctxValue, value, Entry.Value.erase] using
      (ScopedAtomEntryReady.initial Policy.unmarked ctxValue (Or.inl rfl))
  have ctxProdEq : ctxValue =
      Completed.Frame.empty.read Policy.unmarked (Entry.Value.ofAtom typedFWork.body) := by
    simp [ctxValue, typedFWork, value, Entry.Value.ofAtom]
  have tailDerivation : ScopedEquationDerivation typedFSpace HE.GroundedDispatch.none
      noHost Policy.unmarked wEmitted cEmitted fcall resultType Bindings.empty 8 [] []
      ctxCall Completed.Frame.empty 1 1 1
      (.prepend [(value, Bindings.empty)] :: wDrainStack)
      (.prepend [(Completed.Frame.empty.read Policy.unmarked ctxValue,
        Completed.Frame.empty)] :: cDrainStack)
      [] [] [] [] [] [] [] := by
    exact ScopedEquationDerivation.nil
      (.prepend [(value, Bindings.empty)] :: wDrainStack)
      fcall resultType Bindings.empty 8 [] [] ctxCall Completed.Frame.empty
      (.prepend [(Completed.Frame.empty.read Policy.unmarked ctxValue,
        Completed.Frame.empty)] :: cDrainStack)
  have equationDerivationRaw : ScopedEquationDerivation typedFSpace HE.GroundedDispatch.none
      noHost Policy.unmarked wEmitted cEmitted fcall resultType Bindings.empty 8 [] []
      ctxCall Completed.Frame.empty 4 5 6 wDrainStack cDrainStack
      [(value, Bindings.empty)] [typedFWork]
      [(value, Bindings.empty)] [(value, Bindings.empty)]
      [(ctxValue, Completed.Frame.empty)]
      [(value, Bindings.empty)]
      [(Completed.Frame.empty.read Policy.unmarked ctxValue, Completed.Frame.empty)] := by
    apply ScopedEquationDerivation.cons_ordinary_typePass
      (rhs := value) (wBodyVal := value) (selected := Bindings.empty)
      (wBMid := Bindings.empty) (work := typedFWork) (ctxProdVal := ctxValue)
      (cFrameMid := Completed.Frame.empty)
      (eqReady := eqReady) (mergeFilterEq := mergeFilterEq)
      (outBindingsEq := rfl) (unifyRel := callUnify)
      (ctxProdEq := ctxProdEq)
      (notFunc := by intro body bad; cases bad)
      (notRefused := by decide) (clean := by decide)
      (typePass := Or.inr (Or.inl rfl))
      (entryReady := valueReady) (actMid := actEmpty)
      (tailDerivation := tailDerivation)
  have equationDerivation : ScopedEquationDerivation typedFSpace HE.GroundedDispatch.none
      noHost Policy.unmarked wEmitted cEmitted fcall resultType Bindings.empty 8 [] []
      ctxCall Completed.Frame.empty 4 5 6 wDrainStack cDrainStack
      [(value, Bindings.empty)] [typedFWork]
      [(value, Bindings.empty)] [(value, Bindings.empty)]
      [(ctxValue, Completed.Frame.empty)]
      [(value, Bindings.empty)] [(ctxValue, Completed.Frame.empty)] := by
    simpa only [Completed.Frame.read_empty] using equationDerivationRaw
  have callAdmission : ScopedEquationCallAdmission typedFSpace HE.GroundedDispatch.none
      noHost fcall resultType Bindings.empty 8 [] ctxCall Completed.Frame.empty
      [(value, Bindings.empty)] [typedFWork] [(value, Bindings.empty)]
      [(value, Bindings.empty)] 1 := by
    refine
      { value_erase := by simp [ctxCall, fcall, Entry.Value.erase]
        not_error := by decide
        not_executable := ?_
        non_grounded := ?_
        not_minimal := by decide
        query_covered := by decide +kernel
        query_eq := by decide +kernel
        bodies_nonempty := by simp
        frontier := by
          simpa [ctxCall, fcall, Entry.Value.erase, Completed.Frame.empty] using
            typedF_frontier [resultType]
        works_nonempty := by simp
        returned_covered := by intro pair member; simp at member; rcases member with rfl; decide +kernel
        returned_stable := by intro pair member; simp at member; rcases member with rfl; rfl }
    · intro _op _args _same
      rfl
    · simp [NonGroundedCallRel, Spec.Eval.Minimal.HostCall,
        Spec.Eval.Minimal.embeddedInstruction, noHost, ctxCall, Entry.Value.erase]
  have operatorResultRel : ScopedResultRel
      ((.symbol "f", Bindings.empty) : ResultPair)
      ((.symbol "f", Completed.Frame.empty) : Completed.Result) :=
    ⟨by simp only [Entry.Value.erase], actEmpty⟩
  have derivationRaw := ScopedAtomDerivation.selected_function
    (entry := typedF_entry_at wStack wEmitted) (callAdmission := callAdmission)
    (operatorResultRel := operatorResultRel)
    (opSteps := 1) (argSteps := 1) (eqSteps := 4) (prodSteps := 5)
    (retSteps := 6)
    (operatorDerivation := by
      simpa [resultType, wOperatorStack, wCallStack, cOperatorStack, cCallStack,
        Completed.invocationReturnType, typedFSignature, Atom.expressionType,
        Atom.symbolType, Atom.undefinedType,
        expectedApplicationScope, TypeSubst.typeVars, TypeSubst.typeVarsList,
        Entry.Value.erase, fcall] using operatorDerivation)
    (argumentsDerivation := by
      simpa [resultType, wArgsStack, wCallStack, cArgsStack, cCallStack,
        Completed.invocationReturnType, typedFSignature, Atom.expressionType,
        Atom.symbolType, fcall] using
        argumentsDerivation)
    (equationDerivation := by
      simpa [resultType, wDrainStack, cDrainStack,
        Completed.invocationReturnType, typedFSignature, Atom.expressionType,
        Atom.symbolType, fcall, ctxCall] using
        equationDerivation)
  simpa [fcall, ctxCall, ctxValue, Completed.invocationReturnType, typedFSignature,
    Atom.expressionType, Atom.symbolType, Atom.undefinedType,
    successPriority, completedSuccessPriority,
    Completed.readResult, Completed.publishResult, Entry.Value.publish,
    Entry.publish, Entry.Value.withStatus, Entry.Value.erase, isErrorAtom, value,
    Completed.Frame.read_empty] using derivationRaw

theorem typedF_selected_derivation :
    let ctxCall : Entry.Value := .expression .active [.symbol "f"]
    let ctxValue : Entry.Value := .symbol "Value"
    ScopedAtomDerivation typedFSpace HE.GroundedDispatch.none noHost Policy.unmarked
      [] [] 12 [] [] [] fcall ctxCall Atom.undefinedType Bindings.empty
      Completed.Frame.empty [] [] 42
      [(value, Bindings.empty)] [(ctxValue, Completed.Frame.empty)] :=
  typedF_selected_derivation_at [] [] [] []

/-- The selected-function proof object is operationally inhabited: the checked
scoped worker finishes with the equation body, and the same proof reconstructs
the independent completed source judgment. -/
theorem typedF_selected_function_complete :
    let ctxCall : Entry.Value := .expression .active [.symbol "f"]
    let ctxValue : Entry.Value := .symbol "Value"
    (∃ budget,
      (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none scopedTypes).run
        budget
        ⟨typedFSpace,
          .work (.atom fcall Atom.undefinedType Bindings.empty 12 []), [], []⟩ =
      ([(value, Bindings.empty)],
        .finished
          ⟨typedFSpace, .returning [], [], [(value, Bindings.empty)]⟩)) ∧
    Completed.AtomRel typedFSpace noHost Completed.scopedLookup
      [] [] ctxCall Atom.undefinedType Completed.Frame.empty
      [(ctxValue, Completed.Frame.empty)] (policy := Policy.unmarked) := by
  intro ctxCall ctxValue
  have derivation := typedF_selected_derivation
  have completed := derivation.complete_and_drain_bag
  dsimp only at completed
  exact ⟨completed.2.2.2.1, derivation.contextual_source⟩

/-- The physical `g → f` equation exercises the genuinely recursive boundary:
the equation return pass invokes a complete selected-function derivation while
the worker and contextual machines retain differently factored continuations.
Both the independent call judgment and the checked worker completion are
constructed from the same stack-free recursive proof object. -/
theorem recursive_equation_selected_child_complete :
    let ctxCall : Entry.Value := Entry.Value.ofAtom recursiveCall
    let ctxBody : Entry.Value := .expression .active [.symbol "f"]
    let ctxValue : Entry.Value := .symbol "Value"
    EquationFrontierRel typedFSpace [Atom.undefinedType] recursiveCall
      Bindings.empty [recursiveWork] ∧
    ScopedEquationDerivation typedFSpace HE.GroundedDispatch.none noHost
      Policy.unmarked [] [] recursiveCall Atom.undefinedType Bindings.empty 11 [] []
      ctxCall Completed.Frame.empty 4 5 47 [] []
      [(fcall, Bindings.empty)] [recursiveWork]
      [(fcall, Bindings.empty)] [(fcall, Bindings.empty)]
      [(ctxBody, Completed.Frame.empty)]
      [(value, Bindings.empty)] [(ctxValue, Completed.Frame.empty)] ∧
    Completed.CallRel typedFSpace noHost Completed.scopedLookup [] []
      ctxCall Atom.undefinedType Completed.Frame.empty
      [(ctxValue, Completed.Frame.empty)] (policy := Policy.unmarked) ∧
    ∃ budget,
      (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none scopedTypes).run
        budget
        ⟨typedFSpace,
          .work (.call recursiveCall Atom.undefinedType Bindings.empty 13 []), [], []⟩ =
      ([(value, Bindings.empty)],
        .finished
          ⟨typedFSpace, .returning [], [], [(value, Bindings.empty)]⟩) := by
  intro ctxCall ctxBody ctxValue
  have actEmpty : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
    SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)
  have eqReady :
      (matchCovered 12 (.merge Bindings.empty
          (Spec.Type.Presentation.BindingTheory.aliasConstraints Bindings.empty)) &&
        (mergeBindings Bindings.empty
          (Spec.Type.Presentation.BindingTheory.aliasConstraints Bindings.empty) 12).all fun merged =>
          (merged.hasLoop || merged.applyFullCovered fcall 12)) = true := by
    decide +kernel
  have mergeFilterEq :
      ((mergeBindings Bindings.empty
          (Spec.Type.Presentation.BindingTheory.aliasConstraints Bindings.empty) 12).filterMap fun merged =>
        if merged.hasLoop then none else some (merged.applyFull fcall 12, merged)) =
      [(fcall, Bindings.empty)] := by
    decide +kernel
  have callUnify : Entry.Value.UnifyRel Policy.unmarked.rebuilding
      Completed.Frame.empty.environment ctxCall (Entry.Value.ofAtom recursiveWork.pattern)
      Completed.Frame.empty.environment := by
    have same : ctxCall = Entry.Value.ofAtom recursiveCall := by
      simp [ctxCall]
    rw [same]
    exact Entry.Value.UnifyRel.ordinary
      (Entry.Value.AppliedUnifyRel.identical (policy := Policy.unmarked.rebuilding)
        (environment := []) (by rfl))
  have ctxProdEq : ctxBody =
      Completed.Frame.empty.read Policy.unmarked (Entry.Value.ofAtom recursiveWork.body) := by
    simp [ctxBody, recursiveWork, fcall, Entry.Value.ofAtom]
  let wChildStack : List RecursiveTasks.Frame :=
    [.append (.returns recursiveCall Atom.undefinedType 12 [] [])]
  let cChildStack : List RecursiveTasks.Contextual.Continuation :=
    [.append (.boundaryBatch [] [] none (.returned ctxCall Atom.undefinedType) []),
      .append (.equations [] [] ctxCall Atom.undefinedType Completed.Frame.empty [])]
  have childDerivation : ScopedAtomDerivation typedFSpace HE.GroundedDispatch.none
      noHost Policy.unmarked [] [] 12 [] [] [] fcall ctxBody Atom.undefinedType
      Bindings.empty Completed.Frame.empty wChildStack cChildStack 42
      [(value, Bindings.empty)] [(ctxValue, Completed.Frame.empty)] := by
    simpa [wChildStack, cChildStack, ctxBody, ctxValue, fcall] using
      (typedF_selected_derivation_at wChildStack cChildStack [] [])
  have tailDerivation : ScopedEquationDerivation typedFSpace HE.GroundedDispatch.none
      noHost Policy.unmarked [] [] recursiveCall Atom.undefinedType Bindings.empty 11 [] []
      ctxCall Completed.Frame.empty 1 1 1
      [.prepend [(value, Bindings.empty)]]
      [.prepend [(ctxValue, Completed.Frame.empty)]]
      [] [] [] [] [] [] [] :=
    ScopedEquationDerivation.nil [.prepend [(value, Bindings.empty)]]
      recursiveCall Atom.undefinedType Bindings.empty 11 [] [] ctxCall
      Completed.Frame.empty [.prepend [(ctxValue, Completed.Frame.empty)]]
  have equationDerivation : ScopedEquationDerivation typedFSpace
      HE.GroundedDispatch.none noHost Policy.unmarked [] [] recursiveCall
      Atom.undefinedType Bindings.empty 11 [] [] ctxCall Completed.Frame.empty
      4 5 47 [] [] [(fcall, Bindings.empty)] [recursiveWork]
      [(fcall, Bindings.empty)] [(fcall, Bindings.empty)]
      [(ctxBody, Completed.Frame.empty)]
      [(value, Bindings.empty)] [(ctxValue, Completed.Frame.empty)] := by
    apply ScopedEquationDerivation.cons_ordinary_evaluate
      (rhs := fcall) (wBodyVal := fcall) (selected := Bindings.empty)
      (wBMid := Bindings.empty) (work := recursiveWork) (ctxProdVal := ctxBody)
      (cFrameMid := Completed.Frame.empty) (childSteps := 42)
      (remEqSteps := 1) (remProdSteps := 1) (remRetSteps := 1)
      (remRows := []) (remWorks := [])
      (remBodyResults := []) (remProdResults := []) (remCtxProdResults := [])
      (headFinalResults := [(value, Bindings.empty)]) (remFinalResults := [])
      (headCtxFinalResults := [(ctxValue, Completed.Frame.empty)])
      (remCtxFinalResults := [])
      (eqReady := eqReady) (mergeFilterEq := mergeFilterEq)
      (outBindingsEq := by simp [recursiveWork, Completed.Frame.empty])
      (unifyRel := callUnify) (ctxProdEq := ctxProdEq)
      (bodyEraseEq := by simp [ctxBody, fcall, Entry.Value.erase])
      (notFunc := by intro body; simp [fcall])
      (notRefused := by decide) (clean := by decide)
      (actMid := actEmpty) (childDerivation := by
        simpa [wChildStack, cChildStack] using childDerivation)
      (tailDerivation := tailDerivation)
  have recursiveNotMinimal : minimalInstruction recursiveCall = false := by
    change minimalInstruction (.expression [.symbol "g"]) = false
    decide
  have recursiveNonGrounded : NonGroundedCallRel noHost ctxCall.erase := by
    rw [show ctxCall.erase = recursiveCall by
      simp [ctxCall, recursiveCall, Entry.Value.ofAtom, Entry.Value.erase]]
    change NonGroundedCallRel noHost (.expression [.symbol "g"])
    constructor
    · simp [Spec.Eval.Minimal.HostCall, noHost]
    · decide
  have spine := equationDerivation.to_concreteSpine
  have callRun := spine.call_run
    (by simp [ctxCall, recursiveCall, Entry.Value.ofAtom, Entry.Value.erase])
    (by simp [recursiveCall, isErrorAtom])
    (by intro _op _args _same; rfl)
    recursiveNonGrounded recursiveNotMinimal
    (by decide +kernel) (by decide +kernel) (by simp)
    (by simpa [ctxCall, recursiveCall, Entry.Value.ofAtom, Entry.Value.erase,
      Completed.Frame.empty] using recursive_frontier [Atom.undefinedType])
    (by simp)
  have sourceBodies := equationDerivation.to_completed_equationBodiesRel
  have sourceCall : Completed.CallRel typedFSpace noHost Completed.scopedLookup [] []
      ctxCall Atom.undefinedType Completed.Frame.empty
      [(ctxValue, Completed.Frame.empty)] (policy := Policy.unmarked) := by
    apply Completed.CallRel.equations
    · simp [ctxCall, recursiveCall, Entry.Value.ofAtom, Entry.Value.erase,
        Conformance.isErrorRel_iff_isErrorAtom, isErrorAtom]
    · exact recursiveNonGrounded
    · simpa [ctxCall, recursiveCall, Entry.Value.ofAtom, Entry.Value.erase,
        Completed.Frame.empty] using recursive_frontier [Atom.undefinedType]
    · simp
    · exact sourceBodies
  have workerPrefix := callRun.2.1 2
  have workerDrain :
      (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none scopedTypes).run 2
        ⟨typedFSpace, .returning [(value, Bindings.empty)], [], []⟩ =
      ([(value, Bindings.empty)],
        .finished ⟨typedFSpace, .returning [], [], [(value, Bindings.empty)]⟩) := rfl
  refine ⟨recursive_frontier [Atom.undefinedType], equationDerivation, sourceCall, 63, ?_⟩
  simpa only [show 4 + 5 + 47 + 5 + 2 = 63 by decide] using
    workerPrefix.trans workerDrain

end TypedFScopedWorker

def rawSelect : Atom := .expression [.symbol "unify", .symbol "X", .symbol "X", fcall, .symbol "Fail"]

theorem raw_selection_is_not_reactivated :
    complete fspace (.invocation .raw rawSelect Bindings.empty 30) =
      ([(fcall, Bindings.empty)], true) := by decide

theorem ordinary_selection_resumes_return_demand :
    complete fspace (.call rawSelect Atom.undefinedType Bindings.empty 30) =
      ([(value, Bindings.empty)], true) := by decide

def duplicates : Space := Space.ofList
  [.expression [.symbol "=", fcall, function (returned seven)],
   .expression [.symbol "=", fcall, function (returned seven)]]

theorem identical_physical_equations_publish_twice :
    complete duplicates (.invocation .raw fcall Bindings.empty 30) =
      ([(seven, Bindings.empty), (seven, Bindings.empty)], true) := by decide

theorem unknown_service_saves_exact_continuation
    (bindings : Bindings) (fuel : Nat) (live : List Atom) (caller : Option Atom)
    (stack : List Frame) (published : ResultSet) :
    let instruction := Atom.expression [.symbol "context-space"]
    let state : Configuration := ⟨Space.empty,
      .work (.primitive instruction bindings (fuel + 1) live caller), stack, published⟩
    (Checked.machine GroundedDispatch.none).run 1 state =
      ([], .suspended (.primitiveService instruction) state) := by
  rfl

/-- The exact independently constructed selected source primitive agrees with
this actual binding-changing worker run. -/
theorem selected_unify_source_and_execution :
    Spec.Eval.Minimal.CoreStepRel Space.empty Spec.Eval.Minimal.UnifyReadoutControls.dispatch [] Spec.Eval.Minimal.UnifyReadoutControls.invocation Spec.Eval.Minimal.UnifyReadoutControls.initial (Spec.Eval.Minimal.UnifyReadoutControls.observed, Spec.Eval.Minimal.UnifyReadoutControls.reached) ∧
    complete Space.empty (.primitive Spec.Eval.Minimal.UnifyReadoutControls.invocation Bindings.empty 30) =
      ([(Spec.Eval.Minimal.UnifyReadoutControls.observed, Spec.Eval.Minimal.UnifyReadoutControls.outputBindings)], true) :=
  ⟨Spec.Eval.Minimal.UnifyReadoutControls.success_reads_both_and_preserves_text _ _ _, successful_unify_reads_selected_branch⟩

theorem unread_success_is_refused_by_source :
    ¬Spec.Eval.Minimal.CoreStepRel Space.empty Spec.Eval.Minimal.UnifyReadoutControls.dispatch [] Spec.Eval.Minimal.UnifyReadoutControls.invocation Spec.Eval.Minimal.UnifyReadoutControls.initial (Spec.Eval.Minimal.UnifyReadoutControls.template, Spec.Eval.Minimal.UnifyReadoutControls.reached) :=
  Spec.Eval.Minimal.UnifyReadoutControls.success_cannot_return_unread_template _ _ _

theorem selected_failure_cannot_erase_frame :
    ¬Spec.Eval.Minimal.CoreStepRel Space.empty Spec.Eval.Minimal.UnifyReadoutControls.dispatch []
      (.expression [.symbol "unify", .symbol "A", .symbol "C", Spec.Eval.Minimal.UnifyReadoutControls.template, .var "x"])
      Spec.Eval.Minimal.UnifyReadoutControls.reached (.var "x", Spec.Eval.BindingFrame.historical Spec.Eval.Minimal.UnifyReadoutControls.outputBindings) :=
  Spec.Eval.Minimal.UnifyReadoutControls.no_match_cannot_erase_selected_frame _ _ _

def host : Atom := .grounded (.string "control-host")
def hostCall : Atom := .expression [host]
def callerA : Bindings := Bindings.empty.assign "x" (.symbol "A")
def replyB : Bindings := Bindings.empty.assign "x" (.symbol "B")
def conflictingHost : GroundedDispatch where
  isExecutable operator := operator == host
  execute _ _ := .ok [(seven, replyB)]

/-- The declared host profile has a nonempty reply, but all actual binding
merges fail. Rust's post-merge fallback is internal Empty at the old frame. -/
theorem host_filtered_empty_keeps_caller :
    completeWith conflictingHost Space.empty
      (.invocation .raw hostCall callerA 30) = ([(Atom.empty, callerA)], true) := by decide

/-- Query refusal has a distinct protocol from a host's filtered-empty reply. -/
theorem query_refusal_is_not_host_empty :
    complete Space.empty (.invocation .raw fcall callerA 30) =
      ([(Atom.notReducible, callerA)], true) := by decide

/-- The primitive eval reads its operand at its actual selected caller before
invocation, including a variable referring to a full function block. -/
theorem eval_operand_is_materialized :
    complete Space.empty (.primitive (.expression [.symbol "eval", .var "saved"])
      (Bindings.empty.assign "saved" (function (returned seven))) 30) =
      ([(seven, Bindings.empty.assign "saved" (function (returned seven)))], true) := by decide

#print axioms TypedFScopedWorker.typedF_frontier
#print axioms TypedFScopedWorker.recursive_frontier
#print axioms TypedFScopedWorker.typedF_invocation_types
#print axioms TypedFScopedWorker.typedF_entry_at
#print axioms TypedFScopedWorker.typedF_entry
#print axioms TypedFScopedWorker.typedF_operator_admission_at
#print axioms TypedFScopedWorker.typedF_selected_derivation_at
#print axioms TypedFScopedWorker.typedF_selected_derivation
#print axioms TypedFScopedWorker.typedF_selected_function_complete
#print axioms TypedFScopedWorker.recursive_equation_selected_child_complete

end Mettapedia.Languages.MeTTa.HE.RecursiveControls.Invocation


set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.RecursiveControls.Invocation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveEncoding
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedApplyEncoding (index bindingsData resultsData)

theorem missing_producer_provenance_refused :
    readTask (.expression [.symbol "he-task-produced-v1", missingReturn,
      bindingsData Bindings.empty, index 20, .expression [], optionAtomData (some named)]) = none := by
  decide

theorem invalid_producer_provenance_refused :
    readTask (.expression [.symbol "he-task-produced-v1", missingReturn,
      bindingsData Bindings.empty, index 20, .expression [], optionAtomData (some named),
      .symbol "guess-from-function-shape"]) = none := by decide

theorem stale_equation_policy_refused :
    readTask (.expression [.symbol "he-eval-equations-v3", fcall, Atom.undefinedType,
      bindingsData Bindings.empty, index 20, resultsData [], .expression []]) = none := by decide

theorem raw_and_ordinary_encodings_distinct :
    taskData (.invocation .raw rawSelect Bindings.empty 20) ≠
      taskData (.invocation (.ordinary Atom.undefinedType) rawSelect Bindings.empty 20) := by decide

theorem encoded_unknown_service_retains_every_field
    (space : Space) (bindings : Bindings) (fuel budget : Nat) (live : List Atom)
    (caller : Option Atom) (stack : List Frame) (published : ResultSet) :
    let instruction := Atom.expression [.symbol "context-space"]
    let state : Configuration := ⟨space,
      .work (.primitive instruction bindings (fuel + 1) live caller), stack, published⟩
    (RecursiveDataExecution.Checked.dataMachine GroundedDispatch.none).run (budget + 1)
        (configurationData state) =
      ([], .suspended (.primitiveService instruction) (configurationData state)) := by
  apply RecursiveDataExecution.Checked.blocked_run
  rfl

theorem depth_grant_cannot_supply_a_primitive_service
    (space : Space) (bindings : Bindings) (fuel budget extra : Nat) (live : List Atom)
    (caller : Option Atom) (stack : List Frame) (published : ResultSet) :
    let instruction := Atom.expression [.symbol "context-space"]
    let state : Configuration := ⟨space,
      .work (.primitive instruction bindings (fuel + 1) live caller), stack, published⟩
    RecursiveDataExecution.Checked.continueRun GroundedDispatch.none (budget + 1) extra
      (published, .suspended (.primitiveService instruction) (configurationData state)) =
      (published, .suspended (.primitiveService instruction)
        (configurationData (RecursiveMachine.Checked.replenish extra state))) := by
  dsimp
  simp only [RecursiveDataExecution.Checked.continueRun,
    RecursiveDataExecution.Checked.replenishData_configurationData]
  rw [RecursiveDataExecution.Checked.blocked_run GroundedDispatch.none _
    (.primitiveService (.expression [.symbol "context-space"])) budget (by
    simp [RecursiveMachine.Checked.replenish, Task.replenish, Nat.succ_add,
      RecursiveMachine.Checked.blocked, RecursiveMachine.Checked.taskReady,
      minimalCoreSupported])]
  simp

theorem encoded_emitted_and_completed_remain_distinct :
    (RecursiveDataExecution.Checked.dataMachine GroundedDispatch.none).run 200
        (configurationData (Configuration.initial Space.empty
          (.produced missingReturn Bindings.empty 30 [] (some named) .emitted))) ≠
      (RecursiveDataExecution.Checked.dataMachine GroundedDispatch.none).run 200
        (configurationData (Configuration.initial Space.empty
          (.produced missingReturn Bindings.empty 30 [] (some named) .completed))) := by
  intro same
  have values := congrArg (fun run : ResultSet × Outcome Atom Atom
    RecursiveMachine.Checked.ResourceRequest => run.1.map Prod.fst) same
  have different :
      ((RecursiveDataExecution.Checked.dataMachine GroundedDispatch.none).run 200
        (configurationData (Configuration.initial Space.empty
          (.produced missingReturn Bindings.empty 30 [] (some named) .emitted)))).1.map Prod.fst ≠
      ((RecursiveDataExecution.Checked.dataMachine GroundedDispatch.none).run 200
        (configurationData (Configuration.initial Space.empty
          (.produced missingReturn Bindings.empty 30 [] (some named) .completed)))).1.map Prod.fst := by
    decide
  exact different values

end Mettapedia.Languages.MeTTa.HE.RecursiveControls.Invocation


set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.RecursiveControls.Invocation.Aliases
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Steps Spec.Match.Merge Spec.Match.ModelTheory
open Spec.Type.Presentation

def bindings : Bindings := Bindings.empty.addEquality "x" "y"
def pending : Atom := .expression [.symbol "Pair", .var "x", .var "y", .grounded (.string "$y")]
def observed : Atom := .expression [.symbol "Pair", .var "x", .var "x", .grounded (.string "$y")]
def instruction : Atom := .expression [.symbol "unify", .var "x", .var "y", pending, .symbol "Fail"]

theorem loop_free : SemanticLoopFree bindings :=
  (hasLoop_eq_false_iff_semanticLoopFree bindings).mp (by decide)

theorem shape : AssignmentsNonVariable bindings := by
  intro key value present
  simp [bindings, Bindings.addEquality, Bindings.empty] at present

theorem coherent : CanonicalClassCoherent bindings loop_free shape := by
  intro source assignment
  have present := assignment.2.1
  simp [bindings, Bindings.addEquality, Bindings.empty] at present

def frame : BindingFrame := .selected bindings
  (QueryBindingProjection.nativeReadoutPresentation bindings)
  (QueryBindingProjection.nativeReadoutPresentation_certificate loop_free shape coherent
    (fun _ => Iff.rfl))

theorem candidate : UnifyCandidateRel (.var "x") (.var "y") Bindings.empty bindings := by
  refine ⟨bindings, .varVar _ _ loop_free, ?_⟩
  apply MergeRel.logicalMerge (.mk (by simp [constraints, Bindings.empty]) .nil)
  exact ⟨fun _ => .symbol "Shared", by
    simp [bindings, Spec.Type.RuntimeRefinement.TypeBindingSatisfied,
      Bindings.addEquality, Bindings.empty]⟩

theorem actual_read : frame.Materialization pending observed := by
  change observed = (QueryBindingProjection.nativeReadoutPresentation bindings).apply pending
  rw [QueryBindingProjection.nativeReadoutPresentation_apply loop_free shape coherent pending
    (bindings.resolutionFuel pending) (bindings.applyFullCovered_resolutionFuel pending)]
  decide

theorem source_reads_both_aliases (space : Space) (live : List Atom) (caller : Option Atom) :
    Minimal.CoreStepRel space Minimal.UnifyReadoutControls.dispatch live instruction
      Minimal.UnifyReadoutControls.initial (observed, frame) (caller := caller) := by
  apply Minimal.CoreStepRel.unifySuccess
  · exact candidate
  · exact .selected _ _
  · exact actual_read

theorem checked_reads_both_aliases :
    complete Space.empty (.primitive instruction Bindings.empty 30) =
      ([(observed, bindings)], true) := by decide

theorem assignment_only_readout_is_wrong :
    bindings.applyDefault pending ≠ observed := by decide

theorem source_refuses_uncorrelated_success (space : Space) (live : List Atom)
    (caller : Option Atom) :
    ¬Minimal.CoreStepRel space Minimal.UnifyReadoutControls.dispatch live instruction
      Minimal.UnifyReadoutControls.initial (pending, frame) (caller := caller) := by
  intro step
  rcases Minimal.unify_step_exact.mp step with ⟨_, _, read⟩ | ⟨missing, _⟩
  · have same := read.output_eq actual_read
    exact (by decide : pending ≠ observed) same
  · exact missing _ candidate

theorem refusal_keeps_alias_caller_and_unread_fallback :
    complete Space.empty (.primitive
      (.expression [.symbol "unify", .symbol "A", .symbol "C", .symbol "Yes", pending])
      bindings 30) = ([(pending, bindings)], true) := by decide

theorem later_constraint_observes_sharing :
    complete Space.empty (.invocation .raw
      (function (.expression [.symbol "chain", instruction, .var "pair",
        .expression [.symbol "unify", .var "pair",
          .expression [.symbol "Pair", .symbol "Left", .symbol "Right", .grounded (.string "$y")],
          returned (.symbol "CorrelationLost"), returned (.symbol "Shared")]]))
      Bindings.empty 50) = ([(.symbol "Shared", bindings)], true) := by decide

end Mettapedia.Languages.MeTTa.HE.RecursiveControls.Invocation.Aliases


set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.RecursiveControls.Invocation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem completed_function_is_a_new_ordinary_result :
    (seven, Bindings.empty) ∈ mettaCall Space.empty GroundedDispatch.none
      (function (returned seven)) Atom.atomType Bindings.empty 30 := by decide

theorem old_call_relation_has_no_function_completion :
    ¬MettaCall Space.empty GroundedDispatch.none
      (function (returned seven)) Atom.atomType Bindings.empty (seven, Bindings.empty) := by
  intro derived
  have queryEmpty (avoid : List String) (fuel : Nat) :
      queryEquationsAvoiding avoid Space.empty (function (returned seven)) fuel = [] := by
    cases fuel <;> simp [queryEquationsAvoiding, Space.empty]
  cases derived
  all_goals simp_all [function, returned, seven, Space.empty,
    GroundedDispatch.none, isErrorAtom]

theorem old_unconditional_call_soundness_is_false :
    ¬(∀ atom expected bindings fuel result,
      result ∈ mettaCall Space.empty GroundedDispatch.none atom expected bindings fuel →
        MettaCall Space.empty GroundedDispatch.none atom expected bindings result) := by
  intro claimed
  exact old_call_relation_has_no_function_completion
    (claimed _ _ _ _ _ completed_function_is_a_new_ordinary_result)

end Mettapedia.Languages.MeTTa.HE.RecursiveControls.Invocation

/-! ## Polymorphic invocation controls

One annotation `(-> $t $t)` is used by two calls in one tuple. The actual
retained worker reuses the literal variable for both calls, so the binding
`t ↦ Number` from the first call rejects the second. An instance freshened
against the complete retained configuration accepts it. -/

section PolymorphicInvocationControls
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Languages.MeTTa.HE.RecursiveControls.PolymorphicInvocation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def arrow : Atom := .expression [.symbol "->", .var "t", .var "t"]
def context : Space := Space.ofList [
  .expression [.symbol ":", .symbol "ident", arrow],
  .expression [.symbol "=", .expression [.symbol "ident", .var "x"], .var "x"]]
def numberCall : Atom := .expression [.symbol "ident", .grounded (.int 7)]
def boolCall : Atom := .expression [.symbol "ident", .grounded (.bool true)]
def pairCall : Atom := .expression [.symbol "Pair", numberCall, boolCall]
def prior : Bindings := Bindings.empty.assign "t" (.symbol "Number")
def initial (atom : Atom) : RecursiveTasks.Configuration :=
  ⟨context, .work (.atom atom Atom.undefinedType Bindings.empty 40 []), [], []⟩
def error : Atom := mkError boolCall (.badArgType 1 (.var "t") (.symbol "Bool"))

theorem first_use_constrains_type_variable :
    checkIfFunctionTypeIsApplicable numberCall arrow Atom.undefinedType context Bindings.empty 20 =
      .inr [prior] := by decide +kernel

theorem reused_variable_rejects_independent_call :
    checkIfFunctionTypeIsApplicable boolCall arrow Atom.undefinedType context prior 20 =
      .inl [error] := by decide +kernel

theorem fresh_variable_accepts_independent_call :
    checkIfFunctionTypeIsApplicable boolCall
      (.expression [.symbol "->", .var "fresh", .var "fresh"])
      Atom.undefinedType context prior 20 =
      .inr [prior.assign "fresh" (.symbol "Bool")] := by decide +kernel

/-- This is an actual retained-worker result, not the definition of a second
evaluator. The two calls share one enclosing tuple continuation. -/
theorem retained_repeated_polymorphism_obstruction :
    ((FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run 1000
      (initial pairCall)).1.map Prod.fst = [error] := by decide +kernel

theorem retained_single_call_positive :
    ((FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run 1000
      (initial numberCall)).1.map Prod.fst = [.grounded (.int 7)] := by decide +kernel

theorem raw_annotation_does_not_instantiate :
    getAnnotatedTypes context (.symbol "ident") = [arrow] := by decide +kernel

theorem independent_annotation_does_not_instantiate :
    ¬Spec.Type.TypeOfRel context (.symbol "ident")
      (.expression [.symbol "->", .var "fresh", .var "fresh"]) := by
  rw [Spec.Type.Conformance.typeOfRel_iff_mem_getAtomTypes]
  decide +kernel

end Mettapedia.Languages.MeTTa.HE.RecursiveControls.PolymorphicInvocation

namespace Mettapedia.Languages.MeTTa.HE.RecursiveControls.PolymorphicInvocation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open FirstSuccessSourceApplicability FirstSuccessSourceApplicability.InvocationSignature
open Spec.Type.Presentation
open Spec.Type.RuntimeRefinement

def retained : RecursiveTasks.Configuration :=
  ⟨context, .work (.expression boolCall Atom.undefinedType
    ⟨[("t#2", .var "nested")], [("left", "right")]⟩ 10 []),
    [.invocationReturn (.ordinary (.var "t#0"))
      (.expression [.symbol "origin", .var "t#1"]) 8 []],
    [(.var "t#3", Bindings.empty)]⟩

theorem retained_names : RecursiveScope.configurationNames retained =
    ["t#2", "nested", "left", "right", "t#0", "t#1", "t#3"] := by
  simp [RecursiveScope.configurationNames, RecursiveScope.liveAtoms,
    RecursiveScope.controlAtoms, RecursiveScope.taskAtoms, RecursiveScope.frameAtoms,
    RecursiveScope.bindingAtoms, RecursiveScope.resultAtoms, retained, boolCall,
    InvocationMode.expected, Atom.undefinedType, Bindings.empty, atomVariables, atomListVariables]

theorem complete_scope_avoids_saved_receivers_and_output :
    instantiate (retainedAvoid retained []) 0 arrow =
      .expression [.symbol "->", .var "t#4", .var "t#4"] := by
  simp only [instantiate, arrow, renameTypeVars, List.map_cons, List.map_nil]
  simp only [retainedAvoid, retained_names, TypeSubst.typeVarsList, List.append_nil]
  decide +kernel

/-- A caller may save a pending demand even when the current task's narrow
live list is empty. This is a configuration fact, not a reachable-state claim. -/
theorem narrow_live_is_not_complete_configuration_scope :
    instantiate (avoid [] boolCall Atom.undefinedType [] Bindings.empty) 0 arrow =
      .expression [.symbol "->", .var "t#0", .var "t#0"] ∧
    "t#0" ∈ RecursiveScope.configurationNames retained := by
  simp only [instantiate, arrow, renameTypeVars, List.map_cons, List.map_nil]
  rw [retained_names]
  decide +kernel

theorem repeated_arrow_positions_remain_one_variable :
    instantiate ["t#0", "t#1"] 0 arrow =
      .expression [.symbol "->", .var "t#2", .var "t#2"] := by
  simp only [instantiate, arrow, renameTypeVars, List.map_cons, List.map_nil]
  decide +kernel

theorem fresh_second_invocation_checks :
    checkIfFunctionTypeIsApplicable boolCall
      (instantiate (avoid [] boolCall Atom.undefinedType [] prior) 0 arrow)
      Atom.undefinedType context prior 20 =
      .inr [prior.assign "t#0" (.symbol "Bool")] := by
  simp only [instantiate, arrow, renameTypeVars, List.map_cons, List.map_nil]
  decide +kernel

def firstInstanceBinding : Bindings := Bindings.empty.assign "t#0" (.symbol "Number")

/-- The first local check creates the support protected by the second one. -/
theorem sequential_instantiated_checks :
    checkIfFunctionTypeIsApplicable numberCall
      (instantiate (avoid [] numberCall Atom.undefinedType [] Bindings.empty) 0 arrow)
      Atom.undefinedType context Bindings.empty 20 = .inr [firstInstanceBinding] ∧
    checkIfFunctionTypeIsApplicable boolCall
      (instantiate (avoid [] boolCall Atom.undefinedType [] firstInstanceBinding) 0 arrow)
      Atom.undefinedType context firstInstanceBinding 20 =
      .inr [firstInstanceBinding.assign "t#1" (.symbol "Bool")] := by
  simp only [instantiate, arrow, renameTypeVars, List.map_cons, List.map_nil]
  decide +kernel

theorem closed_list_preserved_with_duplicates :
    instantiateAll ["live"] 0 [
      .expression [.symbol "->", .symbol "Number", .symbol "Number"],
      .expression [.symbol "->", .symbol "Number", .symbol "Number"]] = [
      .expression [.symbol "->", .symbol "Number", .symbol "Number"],
      .expression [.symbol "->", .symbol "Number", .symbol "Number"]] := by
  simp [instantiateAll, instantiate, renameTypeVars]

theorem distinct_physical_polymorphic_occurrences :
    instantiateAll [] 0 [arrow, arrow] = [
      .expression [.symbol "->", .var "t#0", .var "t#0"],
      .expression [.symbol "->", .var "t#1", .var "t#1"]] := by
  simp only [instantiateAll, instantiate, arrow, renameTypeVars, List.map_cons, List.map_nil]
  decide +kernel

theorem fresh_class_can_have_unrelated_equalities :
    Spec.Type.TypeMatchRel (.var "t") (.symbol "Bool")
      ⟨[("saved", .symbol "Number")], [("left", "right")]⟩
      (Bindings.assign ⟨[("saved", .symbol "Number")], [("left", "right")]⟩ "t" (.symbol "Bool")) := by
  exact independent_fresh_symbol_type_match "t" "Bool" _ (by decide) (by decide) (by decide +kernel)

theorem insufficient_depth_remains_uncovered :
    matchTypes (.var "fresh") (.symbol "Bool") prior 0 = [] ∧
      matchTypesCovered (.var "fresh") (.symbol "Bool") prior 0 = false := by decide +kernel

end Mettapedia.Languages.MeTTa.HE.RecursiveControls.PolymorphicInvocation

end PolymorphicInvocationControls
