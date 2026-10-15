import Mettapedia.Languages.C11.ReadExpressionData
import Mettapedia.Languages.C11.ObjectAccessControls

/-!
# Contextual integer expression and complete residual controls

The controls retain both arithmetic operand positions, nested focus contexts,
duplicate reads, scope shadowing, short-circuiting, conditional conversions,
trap/fault distinctions and complete paused configurations. Negative controls
reject invalid scalar data, stale allocations, missing names, bad choices and
attempts to use a volatile object through the pure profile.

These examples supplement general contextual and history correspondence.
They do not establish full C source elaboration or native compiler refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ReadExpressionControls

open ReadExpression ObjectAccessMemory ObjectAccessControls
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def integer (value : Int) : ExpressionData := .value ⟨.int, value⟩
def unsigned (value : Int) : ExpressionData := .value ⟨.unsignedInt, value⟩

def environment : ScopedLvalues.Environment :=
  [[("x", location), ("y", otherLocation), ("alias", location)], [("x", otherLocation)]]

def targets (policy : SignedConversionPolicy) (data : ExpressionData) : List ExpressionData :=
  match decodeExpression intLayout data with
  | none => []
  | some expression => (steps intLayout policy afterStore environment expression).map (fun pair => encodeExpression pair.2)

def contexts (data : ExpressionData) : List (List FrameData) :=
  match decodeExpression intLayout data with
  | none => []
  | some expression => (steps intLayout intervalReductionPolicy afterStore environment expression).map
      (fun pair => encodeContext pair.1.context)

theorem arithmetic_retains_left_and_right_occurrences :
    targets intervalReductionPolicy (.arithmetic .add (.read "x") (.read "y")) =
      [.arithmetic .add (integer (-17)) (.read "y"), .arithmetic .add (.read "x") (integer 0)] := by cbv

theorem duplicate_reads_keep_both_positions :
    targets intervalReductionPolicy (.arithmetic .add (.read "x") (.read "x")) =
      [.arithmetic .add (integer (-17)) (.read "x"), .arithmetic .add (.read "x") (integer (-17))] := by cbv

theorem duplicate_reads_keep_distinct_contexts :
    contexts (.arithmetic .add (.read "x") (.read "x")) =
      [[.arithmeticLeft .add (.read "x")], [.arithmeticRight .add (.read "x")]] := by cbv

theorem nested_operands_keep_two_frame_contexts :
    contexts (.arithmetic .multiply (.cast .int (.read "x")) (.cast .int (.read "y"))) =
      [[.arithmeticLeft .multiply (.cast .int (.read "y")), .cast .int],
       [.arithmeticRight .multiply (.cast .int (.read "x")), .cast .int]] := by cbv

theorem nearest_scoped_object_is_read : targets intervalReductionPolicy (.read "x") = [integer (-17)] := by cbv

theorem cast_to_bool_uses_nonzero_truth :
    targets intervalReductionPolicy (.cast .boolean (integer 2)) = [.value ⟨.boolean, 1⟩] := by decide +kernel

theorem cast_to_bool_preserves_zero :
    targets intervalReductionPolicy (.cast .boolean (integer 0)) = [.value ⟨.boolean, 0⟩] := by cbv

theorem signed_overflow_has_arithmetic_fault :
    targets intervalReductionPolicy (.arithmetic .add (integer 2147483647) (integer 1)) =
      [.fault (.arithmetic .overflow)] := by decide +kernel

theorem zero_divisor_has_distinct_arithmetic_fault :
    targets intervalReductionPolicy (.arithmetic .divide (integer 1) (integer 0)) =
      [.fault (.arithmetic .divisionByZero)] := by decide +kernel

theorem unsigned_subtraction_wraps :
    targets intervalReductionPolicy (.arithmetic .subtract (unsigned 0) (unsigned 1)) = [unsigned 4294967295] :=
  by decide +kernel

theorem out_of_range_cast_retains_selected_signal :
    targets (signalingPolicy 9) (.cast (.signed (.standard .char)) (integer 128)) =
      [.fault (.conversionSignal 9)] := by decide +kernel

theorem false_and_skips_zero_division :
    targets intervalReductionPolicy (.logicalAnd (integer 0) (.arithmetic .divide (integer 1) (integer 0))) =
      [integer 0] := by decide +kernel

theorem true_or_skips_zero_division :
    targets intervalReductionPolicy (.logicalOr (integer 7) (.arithmetic .divide (integer 1) (integer 0))) =
      [integer 1] := by decide +kernel

theorem true_and_selects_normalization :
    targets intervalReductionPolicy (.logicalAnd (integer 1) (integer 7)) = [.truth (integer 7)] := by cbv

theorem false_or_selects_normalization :
    targets intervalReductionPolicy (.logicalOr (integer 0) (integer (-17))) = [.truth (integer (-17))] := by cbv

theorem selected_conditional_retains_result_conversion :
    targets intervalReductionPolicy (.conditional .boolean (integer 1) (integer 2)
      (.arithmetic .divide (integer 1) (integer 0))) = [.cast .boolean (integer 2)] := by decide +kernel

theorem comma_waits_for_its_first_operand :
    targets intervalReductionPolicy (.comma (.read "x") (.read "y")) = [.comma (integer (-17)) (.read "y")] := by cbv

theorem comma_selects_second_after_value :
    targets intervalReductionPolicy (.comma (integer 0) (.read "y")) = [.read "y"] := by cbv

theorem missing_name_has_no_pure_step : targets intervalReductionPolicy (.read "missing") = [] := by cbv

theorem invalid_literal_data_rejected : decodeExpression intLayout (integer 2147483648) = none := by decide +kernel

theorem invalid_bool_literal_data_rejected :
    decodeExpression intLayout (.value ⟨.boolean, 2⟩) = none := by decide +kernel

theorem invalid_untaken_syntax_is_not_laundered :
    decodeExpression intLayout (.logicalAnd (integer 0) (integer 2147483648)) = none := by decide +kernel

def zero : IntegerScalar.Value intLayout.parameters := ⟨.int, ⟨0, by decide⟩⟩
def minusSeventeen : IntegerScalar.Value intLayout.parameters := ⟨.int, ⟨-17, by decide⟩⟩

def initial : Configuration intLayout :=
  ⟨⟨afterStore, environment, .arithmetic .add (.read "x") (.read "y"), 40⟩, [0, 0, 0]⟩
def paused : Configuration intLayout :=
  ⟨⟨afterStore, environment, .arithmetic .add (.value minusSeventeen) (.read "y"), 41⟩, [0, 0]⟩
def argumentsDone : Configuration intLayout :=
  ⟨⟨afterStore, environment, .arithmetic .add (.value minusSeventeen) (.value zero), 42⟩, [0]⟩
def completed : Configuration intLayout := ⟨⟨afterStore, environment, .value minusSeventeen, 43⟩, []⟩

def firstEvent : Occurrence intLayout :=
  ⟨40, ⟨[.arithmeticLeft .add (.read "y")], .read "x" location (.integer (.value (-17) false))⟩⟩
def secondEvent : Occurrence intLayout :=
  ⟨41, ⟨[.arithmeticRight .add (.value minusSeventeen)], .read "y" otherLocation (.integer (.value 0 false))⟩⟩
def finalEvent : Occurrence intLayout := ⟨42, event intLayout (.arithmetic .add)⟩

theorem zero_budget_retains_complete_configuration :
    (machine intLayout intervalReductionPolicy).run 0 initial = ([], .exhausted initial) := by cbv

theorem first_read_retains_complete_residual :
    (machine intLayout intervalReductionPolicy).run 1 initial = ([firstEvent], .exhausted paused) := by cbv

theorem second_read_retains_complete_residual :
    (machine intLayout intervalReductionPolicy).run 1 paused = ([secondEvent], .exhausted argumentsDone) := by cbv

theorem complete_execution_keeps_exact_occurrences :
    (machine intLayout intervalReductionPolicy).run 4 initial =
      ([firstEvent, secondEvent, finalEvent], .finished minusSeventeen) := by cbv

theorem resumed_execution_has_same_history :
    (machine intLayout intervalReductionPolicy).run 4 initial =
      ([firstEvent] ++ ((machine intLayout intervalReductionPolicy).run 3 paused).1,
        ((machine intLayout intervalReductionPolicy).run 3 paused).2) :=
  prefix_resumption intLayout intervalReductionPolicy 1 3 initial paused [firstEvent] first_read_retains_complete_residual

theorem restarting_repeats_first_occurrence :
    ((machine intLayout intervalReductionPolicy).run 1 initial).1 ++
      ((machine intLayout intervalReductionPolicy).run 4 initial).1 ≠
        ((machine intLayout intervalReductionPolicy).run 4 initial).1 := by decide +kernel

theorem resumed_accounts_have_three_reductions :
    (machine intLayout intervalReductionPolicy).spent price 4 initial = 3 := by decide +kernel

theorem paused_data_retains_every_branch_and_choice : decodeConfiguration intLayout (encodeConfiguration paused) = some paused :=
  decodeConfiguration_encode intLayout paused

theorem represented_step_retains_next_configuration :
    stepData intLayout intervalReductionPolicy (encodeCore initial.core) 0 =
      some (encodeOccurrence firstEvent, encodeCore paused.core) := by cbv

theorem invalid_choice_is_refused : choose intLayout intervalReductionPolicy initial.core 2 = none := by cbv

theorem empty_choice_list_suspends_with_same_state :
    (machine intLayout intervalReductionPolicy).step {initial with choices := []} =
      some (.call (.choose 2) {initial with choices := []}) := by cbv

theorem ended_allocation_cannot_be_read :
    steps intLayout intervalReductionPolicy
      ⟨[(7, ⟨false, List.replicate 8 (some (ObjectControls.b 0))⟩)], [(object, integerRecord)]⟩
      environment (.read "x") = [] := by cbv

theorem volatile_object_requires_another_interface :
    steps intLayout intervalReductionPolicy
      ⟨afterStore.storage, [(object, declaredRecord ⟨intType, {volatile := true}⟩ 4)]⟩
      environment (.read "x") = [] := by cbv

theorem first_read_has_independent_derivation :
    Advance intLayout intervalReductionPolicy initial.core firstEvent paused.core :=
  choose_sound intLayout intervalReductionPolicy initial.core paused.core 0 firstEvent (by cbv)

end Mettapedia.Languages.C11.ReadExpressionControls
