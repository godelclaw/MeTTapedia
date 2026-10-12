import Mettapedia.Languages.C11.IntegerStep
import Mettapedia.Languages.C11.IntegerControls

/-!
# Represented integer step and resumption controls

The accepted numeric configuration, invalid representation, conversion signal
and undefined arithmetic outcome remain four distinct cases. These controls
exercise the decoder, semantic step and labelled prefix/residual driver.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerStep.Controls

open IntegerControls

def addition : Instruction := .binary u32 .add
  (unsigned32 4294967295 (by decide)) (unsigned32 1 (by decide))

def additionData : ConfigurationData :=
  .pending (.binary (.unsigned 32) .add 4294967295 1)

def conversionData : ConfigurationData :=
  .pending (.conversion 128 (.integer (.signed 7 (.twosComplement true))))

def additionReceipt : Receipt := ⟨addition, .binary (.value 0)⟩

theorem represented_addition_decodes_exact_operands :
    decode additionData = some (.pending addition) := rfl

theorem represented_addition_has_the_modular_step :
    stepData intervalReductionPolicy additionData = some (.completed (.binary (.value 0))) := rfl

theorem decoded_step_has_the_language_reduction :
    Reduction intervalReductionPolicy (.pending addition) (.completed (.binary (.value 0))) :=
  step_sound _ _ _ rfl

theorem zero_precision_has_no_integer_format : decodeFormat (.unsigned 0) = none := rfl

theorem negative_unsigned_operand_is_invalid_data :
    decode (.pending (.binary (.unsigned 32) .add (-1) 1)) = none := rfl

theorem out_of_range_signed_operand_is_invalid_data :
    decode (.pending (.binary (.signed 31 (.twosComplement true)) .add 2147483648 0)) = none := rfl

theorem invalid_data_has_no_semantic_step :
    stepData intervalReductionPolicy (.pending (.binary (.unsigned 32) .add (-1) 1)) = none := rfl

theorem valid_zero_division_reaches_an_undefined_outcome :
    stepData intervalReductionPolicy (.pending (.binary (.signed 31 (.twosComplement true)) .divide 7 0)) =
      some (.completed (.binary (.undefined .divisionByZero))) := rfl

theorem value_conversion_policy_is_retained :
    stepData intervalReductionPolicy conversionData = some (.completed (.conversion (.value (-128)))) := rfl

theorem signal_conversion_policy_is_retained :
    stepData (signalingPolicy 8) conversionData = some (.completed (.conversion (.signal 8))) := rfl

theorem signed_representation_is_retained_in_data :
    encodeFormat (.signed 7 (by decide) .onesComplement) = .signed 7 .onesComplement ∧
      encodeFormat (.signed 7 (by decide) (.twosComplement true)) =
        .signed 7 (.twosComplement true) := ⟨rfl, rfl⟩

theorem trap_minimum_policy_is_retained_in_data :
    encodeFormat (.signed 7 (by decide) (.twosComplement false)) =
      .signed 7 (.twosComplement false) := rfl

theorem trap_minimum_cannot_enter_as_an_operand_value :
    decode (.pending (.binary (.signed 7 (.twosComplement false)) .add (-128) 0)) = none := rfl

theorem pause_after_reduction_keeps_the_result_configuration :
    (machine intervalReductionPolicy).run 1 (.pending addition) =
      ([additionReceipt], .exhausted (.completed (.binary (.value 0)))) := rfl

theorem resuming_completion_emits_no_second_occurrence :
    (machine intervalReductionPolicy).run 1 (.completed (.binary (.value 0))) =
      ([], .finished (.binary (.value 0))) := rfl

theorem resumed_prefix_is_the_uninterrupted_trace :
    (machine intervalReductionPolicy).run 2 (.pending addition) =
      ([additionReceipt] ++
          ((machine intervalReductionPolicy).run 1 (.completed (.binary (.value 0)))).1,
        ((machine intervalReductionPolicy).run 1 (.completed (.binary (.value 0)))).2) :=
  resume_after_prefix _ 1 1 _ _ _ rfl

theorem restarting_has_a_second_occurrence :
    ((machine intervalReductionPolicy).run 1 (.pending addition)).1 ≠
      ((machine intervalReductionPolicy).run 1 (.completed (.binary (.value 0)))).1 := by decide

theorem completion_administration_has_zero_reduction_charge :
    (machine intervalReductionPolicy).spent price 1 (.completed (.binary (.value 0))) = 0 := rfl

theorem complete_run_has_one_reduction_charge :
    (machine intervalReductionPolicy).spent price 2 (.pending addition) = 1 := rfl

theorem completed_data_has_no_further_language_reduction :
    stepData intervalReductionPolicy (.completed (.binary (.value 0))) = none := rfl

end Mettapedia.Languages.C11.IntegerStep.Controls
