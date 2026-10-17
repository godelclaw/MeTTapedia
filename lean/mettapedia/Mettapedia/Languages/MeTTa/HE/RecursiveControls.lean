import Mettapedia.Languages.MeTTa.HE.RecursiveService
import Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution
import Mettapedia.Languages.MeTTa.HE.ArgumentResultControls
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
import Mettapedia.Languages.MeTTa.HE.SmallStepQuiescence
import Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness

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
