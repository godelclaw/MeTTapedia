import Mettapedia.Languages.C11.IntegerArithmetic

/-!
# Integer conversion and arithmetic controls

Narrow formats are conversion targets. Binary arithmetic examples use a
32-bit common operand type; a narrow character operand's promotion is not
silently omitted. Conversion signals, modular unsigned results, truncating
division and undefined signed arithmetic have distinct expected outcomes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerControls

def u8 : IntegerFormat := .unsigned 8 (by decide)
def s8 : IntegerFormat := .signed 7 (by decide) (.twosComplement true)
def trapMinimum8 : IntegerFormat := .signed 7 (by decide) (.twosComplement false)
def ones8 : IntegerFormat := .signed 7 (by decide) .onesComplement
def signMagnitude8 : IntegerFormat := .signed 7 (by decide) .signMagnitude
def u32 : IntegerFormat := .unsigned 32 (by decide)
def s32 : IntegerFormat := .signed 31 (by decide) (.twosComplement true)

def unsigned32 (integer : Nat) (bounded : integer < 4294967296) : IntegerValue u32 :=
  ⟨integer, by
    change 0 ≤ (integer : Int) ∧ (integer : Int) ≤ 4294967295
    omega⟩

def signed32 (integer : Int) (lower : -2147483648 ≤ integer)
    (upper : integer ≤ 2147483647) : IntegerValue s32 :=
  ⟨integer, by change -2147483648 ≤ integer ∧ integer ≤ 2147483647; exact ⟨lower, upper⟩⟩

theorem negative_to_unsigned_reduces_into_range :
    convertInteger intervalReductionPolicy (-1) (.integer u8) = .value 255 := rfl

theorem wide_to_unsigned_reduces_by_whole_modulus :
    convertInteger intervalReductionPolicy 257 (.integer u8) = .value 1 := rfl

theorem fitting_signed_value_is_preserved_before_policy :
    convertInteger (signalingPolicy 8) (-128) (.integer s8) = .value (-128) := rfl

theorem signed_narrowing_uses_the_declared_value_policy :
    convertInteger intervalReductionPolicy 128 (.integer s8) = .value (-128) := rfl

theorem signed_narrowing_can_raise_the_declared_signal :
    convertInteger (signalingPolicy 8) 128 (.integer s8) = .signal 8 := rfl

theorem two_permitted_signed_policies_have_different_observations :
    convertInteger intervalReductionPolicy 128 (.integer s8) ≠
      convertInteger (signalingPolicy 8) 128 (.integer s8) := by decide

theorem ones_complement_minimum_is_not_twos_complement_minimum :
    convertInteger (signalingPolicy 8) (-128) (.integer ones8) = .signal 8 := rfl

theorem trap_minimum_changes_the_signed_conversion_range :
    convertInteger (signalingPolicy 8) (-128) (.integer trapMinimum8) = .signal 8 := rfl

theorem trap_minimum_is_not_a_valid_integer_value : ¬ trapMinimum8.Represents (-128) := by decide

theorem sign_magnitude_minimum_uses_the_same_value_range :
    convertInteger (signalingPolicy 8) (-128) (.integer signMagnitude8) = .signal 8 := rfl

theorem zero_converts_to_false :
    convertInteger intervalReductionPolicy 0 .boolean = .value 0 := rfl

theorem nonzero_boolean_conversion_does_not_truncate_bits :
    convertInteger intervalReductionPolicy 256 .boolean = .value 1 ∧
      convertInteger intervalReductionPolicy 256 (.integer u8) = .value 0 := ⟨rfl, rfl⟩

theorem negative_boolean_conversion_is_true :
    convertInteger intervalReductionPolicy (-2) .boolean = .value 1 := rfl

theorem signed_division_truncates_toward_zero : divideIntegers (-7) 3 = some (-2, -1) := rfl

theorem negative_divisor_keeps_the_dividend_remainder_sign :
    divideIntegers 7 (-3) = some (-2, 1) := rfl

theorem two_negative_operands_give_a_positive_quotient :
    divideIntegers (-7) (-3) = some (2, -1) := rfl

theorem euclidean_division_is_a_different_observation :
    divideIntegers (-7) 3 ≠ some ((-7 : Int) / 3, (-7 : Int) % 3) := by decide

theorem zero_divisor_has_no_division_pair : divideIntegers 7 0 = none := rfl

theorem unsigned_addition_wraps_at_the_common_type :
    evaluateIntegerBinary u32 .add (unsigned32 4294967295 (by decide))
      (unsigned32 1 (by decide)) = .value 0 := rfl

theorem unsigned_subtraction_wraps :
    evaluateIntegerBinary u32 .subtract (unsigned32 0 (by decide))
      (unsigned32 1 (by decide)) = .value 4294967295 := rfl

theorem unsigned_multiplication_keeps_its_modulus :
    evaluateIntegerBinary u32 .multiply (unsigned32 2147483648 (by decide))
      (unsigned32 2 (by decide)) = .value 0 := rfl

theorem signed_addition_overflow_is_undefined :
    evaluateIntegerBinary s32 .add (signed32 2147483647 (by decide) (by decide))
      (signed32 1 (by decide) (by decide)) = .undefined .overflow := rfl

theorem ordinary_signed_addition_preserves_the_value :
    evaluateIntegerBinary s32 .add (signed32 (-7) (by decide) (by decide))
      (signed32 3 (by decide) (by decide)) = .value (-4) := rfl

theorem minimum_signed_divided_by_minus_one_is_undefined :
    evaluateIntegerBinary s32 .divide (signed32 (-2147483648) (by decide) (by decide))
      (signed32 (-1) (by decide) (by decide)) = .undefined .overflow := rfl

theorem remainder_checks_the_quotient_even_when_the_residue_fits :
    evaluateIntegerBinary s32 .remainder (signed32 (-2147483648) (by decide) (by decide))
      (signed32 (-1) (by decide) (by decide)) = .undefined .overflow ∧
      (-2147483648 : Int).tmod (-1) = 0 := ⟨rfl, rfl⟩

theorem ordinary_signed_remainder_keeps_its_sign :
    evaluateIntegerBinary s32 .remainder (signed32 (-7) (by decide) (by decide))
      (signed32 3 (by decide) (by decide)) = .value (-1) := rfl

theorem division_by_zero_is_distinct_from_overflow :
    evaluateIntegerBinary s32 .divide (signed32 7 (by decide) (by decide))
      (signed32 0 (by decide) (by decide)) = .undefined .divisionByZero := rfl

theorem signed_conversion_is_distinct_from_signed_arithmetic :
    convertInteger intervalReductionPolicy 2147483648 (.integer s32) = .value (-2147483648) ∧
      normalizeArithmetic s32 2147483648 = .undefined .overflow := ⟨rfl, rfl⟩

theorem ones_complement_minimum_division_fits :
    evaluateDivision ones8 (-127) (-1) false = .value 127 := rfl

theorem declaration_relation_rejects_the_wrong_unsigned_result :
    ¬ IntegerConverts intervalReductionPolicy (-1) (.integer u8) (.value 0) := by
  intro converted
  have computed := convertInteger_complete _ _ _ _ converted
  contradiction

theorem declaration_relation_rejects_floor_division :
    ¬ IntegerDivision (-7) 3 (-3) 2 := by
  intro division
  have computed := divideIntegers_complete _ _ _ _ division
  contradiction

end Mettapedia.Languages.C11.IntegerControls
