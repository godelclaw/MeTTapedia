import Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution
import Mettapedia.Languages.MeTTa.HE.ArgumentResultControls
import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Languages.MeTTa.HE.SmallStepQuiescence

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

def shared : Task := .atom (.expression [.symbol "same", pick]) Atom.undefinedType Bindings.empty 32
def independent : Task :=
  .atom (.expression [.symbol "pair", pick, pick]) Atom.undefinedType Bindings.empty 32
def duplicated : Task :=
  .atom (.expression [.symbol "same", .expression [.symbol "duplicate"]])
    Atom.undefinedType Bindings.empty 32
def raw (arguments : List Atom) : Task :=
  .atom (.expression (.symbol "keep-raw" :: arguments)) Atom.undefinedType Bindings.empty 32

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
    (fuel : Nat) (environment : Bindings) (rest : ResultSet)
    (ordinary : (head != original && isEmptyOrError head) = false) :
    enter Space.empty GroundedDispatch.none
      (.argumentHeads original remaining types fuel ((head, environment) :: rest)) =
      (.work (.args remaining types environment fuel),
        [.argumentTail head, .append (.argumentHeads original remaining types fuel rest)]) := by
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
    enter Space.empty GroundedDispatch.none (.args [] [] Bindings.empty 1) =
      (.returning [(argumentPacket [], Bindings.empty)], []) := rfl

theorem mismatched_argument_lists_do_not_forge_success :
    enter Space.empty GroundedDispatch.none (.args [a] [] Bindings.empty 1) =
      (.returning [], []) := rfl

theorem zero_source_fuel_stops (value expected : Atom) (environment : Bindings) :
    enter Space.empty GroundedDispatch.none (.atom value expected environment 0) =
      (.returning [], []) := rfl

theorem changed_grounded_failure_retained :
    (Task.args [ArgumentResult.Controls.failingArgument, .symbol "later"]
      [.symbol "Value", Atom.atomType] Bindings.empty 32).denote
        ArgumentResult.Controls.failureSpace ArgumentResult.Controls.failureDispatch =
      [(ArgumentResult.Controls.failedResult, Bindings.empty)] :=
  ArgumentResult.Controls.changed_grounded_error_propagates

theorem unchanged_error_is_raw_data :
    (Task.args [ArgumentResult.Controls.failedResult] [Atom.atomType] Bindings.empty 4).denote
      Space.empty GroundedDispatch.none =
      [(argumentPacket [ArgumentResult.Controls.failedResult], Bindings.empty)] :=
  ArgumentResult.Controls.unchanged_error_is_data

/-- The retained tuple machine preserves the singleton wrapper and the
nested tuple boundary, just as the source evaluator does. -/
theorem retained_tuple_preserves_nested_boundary :
    ((machine GroundedDispatch.none).run 64
      (Configuration.initial Space.empty
        (.tuple (.expression [.symbol "f", .expression [.symbol "a", .symbol "b"]])
          Bindings.empty 8))).1.map Prod.fst =
      [.expression [.symbol "f", .expression [.symbol "a", .symbol "b"]]] := by decide

theorem retained_singleton_is_not_unwrapped :
    ((machine GroundedDispatch.none).run 32
      (Configuration.initial Space.empty
        (.tuple (.expression [.symbol "g"]) Bindings.empty 8))).1.map Prod.fst =
      [.expression [.symbol "g"]] ∧
    ((machine GroundedDispatch.none).run 32
      (Configuration.initial Space.empty
        (.tuple (.expression [.symbol "g"]) Bindings.empty 8))).1.map Prod.fst ≠
      [.symbol "g"] := by decide

theorem negative_fuel_rejected :
    readTask (.expression [.symbol "he-eval-atom-v1", a, choice,
      bindingsData Bindings.empty, .grounded (.int (-1))]) = none := by decide

theorem missing_binding_field_rejected :
    readTask (.expression [.symbol "he-eval-atom-v1", a, choice, index 4]) = none := by decide

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
    (typing : Spec.Eval.EvalTypeService) (expected : Atom) (bindings : Bindings) (output : ResultPair) :
    ¬Spec.Eval.InterpretExpressionRel space dispatch live (typing := typing)
      Atom.unit expected bindings output := by
  intro interpreted
  cases interpreted <;> simp_all [Atom.unit]

/-- Invert the independent singleton rules, including error propagation. -/
theorem independent_singleton_cases
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (input : Atom) (bindings : Bindings) (output : ResultPair) :
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
    (value : Atom) (bindings : Bindings) (fuel : Nat) :
    enter space dispatch (.tuple (.expression [value]) bindings (fuel + 1)) =
      (.work (.atom value Atom.undefinedType bindings fuel), [.tupleSingleton]) := rfl

theorem empty_tuple_retains_bindings (bindings : Bindings) (fuel : Nat) :
    enter Space.empty GroundedDispatch.none (.tuple Atom.unit bindings (fuel + 1)) =
      (.returning [(Atom.unit, bindings)], []) := rfl

def tupleBindings : Bindings := ⟨[("held", .symbol "value")], [("left", "right")]⟩
def nestedTuple : Atom := .expression [.var "head", .expression [.var "first", .var "last"]]

theorem singleton_variable_keeps_wrapper :
    (Task.tuple (.expression [.var "x"]) tupleBindings 4).denote Space.empty GroundedDispatch.none =
      [(.expression [.var "x"], tupleBindings)] := by decide

theorem nested_tail_does_not_flatten :
    (Task.tuple nestedTuple tupleBindings 16).denote Space.empty GroundedDispatch.none =
      [(nestedTuple, tupleBindings)] := by decide

theorem singleton_empty_propagates :
    (Task.tuple (.expression [Atom.empty]) tupleBindings 4).denote Space.empty GroundedDispatch.none =
      [(Atom.empty, tupleBindings)] := by decide

theorem singleton_error_propagates :
    (Task.tuple (.expression [.expression [.symbol "Error", .symbol "held", .symbol "problem"]])
      tupleBindings 4).denote Space.empty GroundedDispatch.none =
      [(.expression [.symbol "Error", .symbol "held", .symbol "problem"], tupleBindings)] := by decide

theorem singleton_result_is_not_unwrapped :
    (Task.tuple (.expression [.var "x"]) tupleBindings 4).denote Space.empty GroundedDispatch.none ≠
      [(.var "x", tupleBindings)] := by decide

theorem empty_tuple_is_not_dropped :
    (Task.tuple Atom.unit tupleBindings 1).denote Space.empty GroundedDispatch.none ≠ [] := by decide

/-- The recursive source tests a completed tail before prepending its head. -/
theorem constructed_error_tail_propagates :
    (Task.tuple (.expression [.symbol "a", .symbol "Error"]) tupleBindings 8).denote
      Space.empty GroundedDispatch.none = [(.expression [.symbol "Error"], tupleBindings)] := by decide

theorem tuple_duplicate_occurrences_keep_wrappers :
    values (.tuple (.expression [.expression [.symbol "duplicate"]]) Bindings.empty 32) =
      [.expression [a], .expression [a], .expression [b]] := by decide

theorem nested_tuple_duplicate_occurrences_keep_wrappers :
    values (.tuple (.expression [.symbol "tag", .expression [.expression [.symbol "duplicate"]]])
      Bindings.empty 32) =
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
    (Task.tuple (.expression errorCompletionValues) tupleBindings 16).denote
      Space.empty GroundedDispatch.none =
      [(.expression [.symbol "Error", .symbol "c", .symbol "c"], tupleBindings)] := by decide

def tupleInitial : Configuration :=
  Configuration.initial Space.empty (.tuple nestedTuple tupleBindings 16)

def tupleSaved : Configuration :=
  ⟨Space.empty, .work (.atom (.var "head") Atom.undefinedType tupleBindings 15),
    [.tupleHeads (.expression [.expression [.var "first", .var "last"]]) 15], []⟩

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

end Mettapedia.Languages.MeTTa.HE.RecursiveControls
