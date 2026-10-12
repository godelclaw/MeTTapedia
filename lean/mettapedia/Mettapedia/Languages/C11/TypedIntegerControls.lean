import Mettapedia.Languages.C11.IntegerProfiles
import Mettapedia.Languages.C11.TypedIntegerStep

/-!
# Typed integer conversion and reduction controls

Controls cover promotions, rank/range distinctions between value profiles,
signed-to-unsigned conversion, arithmetic faults and represented input range
checks. Undefined examples are semantic controls, not native executions.
The finite native comparison suite exercises all admitted canonical operand
type pairs separately from these kernel-checked controls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.TypedIntegerControls

private abbrev lp64 := integerValueProfile .lp64
private abbrev ilp32 := integerValueProfile .ilp32
private abbrev llp64 := integerValueProfile .llp64
private abbrev signedChar : IntegerType IntegerExtension := .signed (.standard .char)
private abbrev unsignedChar : IntegerType IntegerExtension := .unsigned (.standard .char)
private abbrev unsignedShort : IntegerType IntegerExtension := .unsigned (.standard .short)
private abbrev signedLong : IntegerType IntegerExtension := .signed (.standard .long)
private abbrev unsignedLong : IntegerType IntegerExtension := .unsigned (.standard .long)
private abbrev signedLongLong : IntegerType IntegerExtension := .signed (.standard .longLong)
private abbrev unsignedLongLong : IntegerType IntegerExtension := .unsigned (.standard .longLong)
private abbrev signed128 : IntegerType IntegerExtension := .signed (.extended .int128)

def compute (model : IntegerDataModel) (operation : IntegerBinaryOperator)
    (leftType rightType : IntegerType IntegerExtension) (left right : Int) :
    Option (TypedIntegerOutcome IntegerExtension) := do
  let input ← TypedIntegerStep.decodeInput (integerValueProfile model) ⟨operation, leftType, rightType, left, right⟩
  some (TypedIntegerStep.execute (integerValueProfile model) input)

theorem boolean_promotes_to_int : promoteIntegerType lp64 .boolean = .int := by decide
theorem signed_char_promotes_to_int : promoteIntegerType lp64 signedChar = .int := by decide
theorem unsigned_char_promotes_to_int : promoteIntegerType lp64 unsignedChar = .int := by decide
theorem unsigned_short_promotes_to_int : promoteIntegerType lp64 unsignedShort = .int := by decide
theorem int_is_not_promoted_further : promoteIntegerType lp64 .int = .int := by decide
theorem unsigned_int_is_not_promoted_further : promoteIntegerType lp64 .unsignedInt = .unsignedInt := by decide
theorem extension_is_not_promoted : promoteIntegerType lp64 signed128 = signed128 := by decide

theorem unsigned_rank_dominates : usualIntegerType lp64 .int .unsignedInt = .unsignedInt := by decide
theorem higher_signed_rank_with_room : usualIntegerType lp64 signedLong .unsignedInt = signedLong := by decide
theorem higher_signed_rank_without_room : usualIntegerType ilp32 signedLong .unsignedInt = unsignedLong := by decide
theorem llp64_uses_unsigned_counterpart : usualIntegerType llp64 signedLong .unsignedInt = unsignedLong := by decide
theorem signed_rank_alone_is_insufficient : usualIntegerType ilp32 signedLong .unsignedInt ≠ signedLong := by decide
theorem equal_width_distinct_ranks : usualIntegerType lp64 signedLong signedLongLong = signedLongLong := by decide
theorem higher_unsigned_rank : usualIntegerType lp64 unsignedLong unsignedLongLong = unsignedLongLong := by decide
theorem signed_extension_covers_unsigned_long : usualIntegerType lp64 unsignedLong signed128 = signed128 := by decide

theorem signed_unsigned_addition : compute .lp64 .add .int .unsignedInt (-1) 1 =
    some ⟨.unsignedInt, .value 0⟩ := by decide
theorem signed_unsigned_subtraction : compute .lp64 .subtract .int .unsignedInt (-1) 1 =
    some ⟨.unsignedInt, .value 4294967294⟩ := by decide
theorem small_signed_multiplication_promotes : compute .lp64 .multiply signedChar signedChar 127 127 =
    some ⟨.int, .value 16129⟩ := by decide
theorem small_unsigned_addition_does_not_wrap_at_char : compute .lp64 .add unsignedChar .int 255 1 =
    some ⟨.int, .value 256⟩ := by decide
theorem small_unsigned_addition_does_not_wrap_at_short : compute .lp64 .add unsignedShort .int 65535 1 =
    some ⟨.int, .value 65536⟩ := by decide
theorem mixed_unsigned_division : compute .lp64 .divide .int .unsignedInt (-7) 2 =
    some ⟨.unsignedInt, .value 2147483644⟩ := by decide
theorem mixed_unsigned_remainder : compute .lp64 .remainder .int .unsignedInt (-7) 2 =
    some ⟨.unsignedInt, .value 1⟩ := by decide
theorem wider_signed_division : compute .lp64 .divide signedLong .unsignedInt (-7) 2 =
    some ⟨signedLong, .value (-3)⟩ := by decide
theorem wider_signed_remainder : compute .lp64 .remainder signedLong .unsignedInt (-7) 2 =
    some ⟨signedLong, .value (-1)⟩ := by decide
theorem long_unsigned_conversion : compute .lp64 .add signedLong unsignedLong (-1) 1 =
    some ⟨unsignedLong, .value 0⟩ := by decide
theorem ilp32_long_conversion : compute .ilp32 .add signedLong .unsignedInt (-1) 2 =
    some ⟨unsignedLong, .value 1⟩ := by decide
theorem unsigned_arithmetic_wraps : compute .lp64 .add .unsignedInt .int 4294967295 1 =
    some ⟨.unsignedInt, .value 0⟩ := by decide

theorem signed_overflow_is_undefined : compute .lp64 .add signedLongLong .int 9223372036854775807 1 =
    some ⟨signedLongLong, .undefined .overflow⟩ := by decide
theorem mixed_zero_divisor_is_undefined : compute .lp64 .divide .int .unsignedInt (-1) 0 =
    some ⟨.unsignedInt, .undefined .divisionByZero⟩ := by decide

theorem negative_unsigned_input_is_invalid :
    TypedIntegerStep.decodeInput lp64 ⟨.add, .unsignedInt, .int, -1, 1⟩ = none := by decide
theorem oversized_signed_input_is_invalid :
    TypedIntegerStep.decodeInput lp64 ⟨.add, .int, .int, 2147483648, 1⟩ = none := by decide
theorem nonboolean_input_is_invalid :
    TypedIntegerStep.decodeInput lp64 ⟨.add, .boolean, .int, 2, 1⟩ = none := by decide
theorem invalid_input_has_no_represented_step :
    TypedIntegerStep.stepData lp64 (.pending ⟨.add, .boolean, .int, 2, 1⟩) = none := by decide

theorem represented_step_retains_result_type :
    TypedIntegerStep.stepData lp64 (.pending ⟨.add, .int, .unsignedInt, -1, 1⟩) =
      some (.completed ⟨.unsignedInt, .value 0⟩) := by decide
theorem common_width_does_not_identify_types :
    (IntegerType.int.format ilp32 = signedLong.format ilp32) ∧
      (IntegerType.int : IntegerType IntegerExtension) ≠ signedLong := by decide
theorem representation_retains_type_identity :
    (TypedIntegerStep.ConfigurationData.pending ⟨.add, .int, .int, 1, 1⟩ :
      TypedIntegerStep.ConfigurationData IntegerExtension) ≠
      .pending ⟨.add, signedLong, .int, 1, 1⟩ := by decide

private def sample : TypedIntegerStep.Input lp64 :=
  ⟨.add, .unsignedInt, .int, ⟨4294967295, by decide⟩, ⟨1, by decide⟩⟩

theorem prefix_has_one_receipt :
    ((TypedIntegerStep.machine lp64).run 1 (.pending sample)).1.length = 1 := by decide
theorem resumed_result_does_not_repeat_receipt :
    ((TypedIntegerStep.machine lp64).run 1 (.completed (TypedIntegerStep.execute lp64 sample))).1 = [] := by decide
theorem completed_run_has_one_charge :
    (TypedIntegerStep.machine lp64).spent TypedIntegerStep.price 2 (.pending sample) = 1 := by decide

end Mettapedia.Languages.C11.TypedIntegerControls
