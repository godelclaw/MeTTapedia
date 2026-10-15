import Mettapedia.Languages.C11.IntegerOperators
import Mettapedia.Languages.C11.IntegerProfiles

/-!
# Promoted integer operator controls

Closed controls check promotions, distinct shift operand types, defined
unsigned reductions, exact undefined cases, all comparison operators and
the three signed value-bit representations. Normal negative zero is kept
apart from its normalized or unsupported outcomes. These are kernel checks,
not native compiler observations or source-expression adequacy proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerOperatorControls

open IntegerOperators

def parameters := integerValueProfile .lp64

def value (type : IntegerType IntegerExtension) (integer : Int)
    (valid : (type.format parameters).Represents integer) : IntegerScalar.Value parameters :=
  ⟨type, ⟨integer, valid⟩⟩

def intValue (integer : Int) (valid : (IntegerType.int.format parameters).Represents integer) :=
  value .int integer valid

def unsignedValue (integer : Int) (valid : (IntegerType.unsignedInt.format parameters).Represents integer) :=
  value .unsignedInt integer valid

def one := intValue 1 (by decide)
def zero := intValue 0 (by decide)
def minusOne := intValue (-1) (by decide)
def minusThree := intValue (-3) (by decide)
def intMinimum := intValue (-2147483648) (by decide)
def intMaximum := intValue 2147483647 (by decide)
def unsignedMaximum := unsignedValue 4294967295 (by decide)
def charMaximum := value (.unsigned (.standard .char)) 255 (by decide)
def signedCharMinimum := value (.signed (.standard .char)) (-128) (by decide)
def boolOne := value .boolean 1 (by decide)
def longMinusOne := value (.signed (.standard .long)) (-1) (by decide)
def unsignedLongCount := value (.unsigned (.standard .long)) 31 (by decide)

theorem unary_plus_promotes_character :
    (unary parameters .unsupported .plus charMaximum).raw = ⟨.int, .value 255 false⟩ := by cbv

theorem unary_minus_promotes_before_negation :
    (unary parameters .unsupported .minus charMaximum).raw = ⟨.int, .value (-255) false⟩ := by cbv

theorem unary_minus_signed_character_minimum :
    (unary parameters .unsupported .minus signedCharMinimum).raw = ⟨.int, .value 128 false⟩ := by cbv

theorem unary_minus_unsigned_wraps :
    (unary parameters .unsupported .minus (unsignedValue 1 (by decide))).raw =
      ⟨.unsignedInt, .value 4294967295 false⟩ := by cbv

theorem unary_minus_signed_minimum_undefined :
    (unary parameters .unsupported .minus intMinimum).raw = ⟨.int, .undefined .arithmeticOverflow⟩ := by cbv

theorem unary_complement_boolean_promotes :
    (unary parameters .unsupported .complement boolOne).raw = ⟨.int, .value (-2) false⟩ := by cbv

theorem unsigned_complement_maximum :
    (unary parameters .unsupported .complement unsignedMaximum).raw = ⟨.unsignedInt, .value 0 false⟩ := by cbv

theorem unary_complement_character_promotes :
    (unary parameters .unsupported .complement charMaximum).raw = ⟨.int, .value (-256) false⟩ := by cbv

theorem signed_shift_zero_valid :
    (shift parameters .arithmetic .left zero unsignedLongCount).raw = ⟨.int, .value 0 false⟩ := by cbv

theorem shift_type_is_promoted_left :
    (shift parameters .arithmetic .left one unsignedLongCount).raw =
      ⟨.int, .undefined .signedLeftOverflow⟩ := by cbv

theorem signed_left_shift_representable :
    (shift parameters .arithmetic .left one (intValue 30 (by decide))).raw =
      ⟨.int, .value 1073741824 false⟩ := by cbv

theorem signed_left_shift_into_sign_undefined :
    (shift parameters .arithmetic .left one (intValue 31 (by decide))).raw =
      ⟨.int, .undefined .signedLeftOverflow⟩ := by cbv

theorem negative_signed_left_shift_even_zero_count_undefined :
    (shift parameters .arithmetic .left minusOne zero).raw = ⟨.int, .undefined .negativeSignedLeft⟩ := by cbv

theorem negative_shift_count_undefined :
    (shift parameters .arithmetic .right one minusOne).raw = ⟨.int, .undefined .negativeShiftCount⟩ := by cbv

theorem count_equal_to_width_undefined :
    (shift parameters .arithmetic .right zero (intValue 32 (by decide))).raw =
      ⟨.int, .undefined .shiftCountTooLarge⟩ := by cbv

theorem unsigned_left_shift_reduces :
    (shift parameters .arithmetic .left (unsignedValue 2147483648 (by decide)) one).raw =
      ⟨.unsignedInt, .value 0 false⟩ := by cbv

theorem promoted_character_shift_uses_int_width :
    (shift parameters .arithmetic .right charMaximum (unsignedValue 8 (by decide))).raw =
      ⟨.int, .value 0 false⟩ := by cbv

theorem signed_right_shift_arithmetic :
    (shift parameters .arithmetic .right minusThree one).raw = ⟨.int, .value (-2) false⟩ := by cbv

theorem signed_right_shift_toward_zero :
    (shift parameters .towardZero .right minusThree one).raw = ⟨.int, .value (-1) false⟩ := by cbv

theorem signed_minimum_right_shift :
    (shift parameters .arithmetic .right intMinimum (intValue 31 (by decide))).raw =
      ⟨.int, .value (-1) false⟩ := by cbv

theorem unsigned_right_shift :
    (shift parameters .arithmetic .right unsignedMaximum (intValue 31 (by decide))).raw =
      ⟨.unsignedInt, .value 1 false⟩ := by cbv

theorem bitwise_and_usual_unsigned_conversion :
    (bitwise parameters .unsupported .and minusOne (unsignedValue 255 (by decide))).raw =
      ⟨.unsignedInt, .value 255 false⟩ := by cbv

theorem bitwise_or_signed :
    (bitwise parameters .unsupported .or (intValue 8 (by decide)) (intValue 3 (by decide))).raw =
      ⟨.int, .value 11 false⟩ := by cbv

theorem bitwise_xor_signed_negative :
    (bitwise parameters .unsupported .xor minusOne one).raw = ⟨.int, .value (-2) false⟩ := by cbv

theorem bitwise_character_promotions :
    (bitwise parameters .unsupported .xor charMaximum boolOne).raw = ⟨.int, .value 254 false⟩ := by cbv

theorem comparison_negative_to_unsigned_less_false :
    (comparison parameters .less minusOne (unsignedValue 1 (by decide))).integer.value = 0 := by cbv

theorem comparison_negative_to_unsigned_greater_true :
    (comparison parameters .greater minusOne (unsignedValue 1 (by decide))).integer.value = 1 := by cbv

theorem comparison_wider_signed_preserves_negative :
    (comparison parameters .less longMinusOne (unsignedValue 1 (by decide))).integer.value = 1 := by cbv

theorem comparison_equal_zero_one :
    (comparison parameters .equal zero one).integer.value = 0 := by cbv

theorem comparison_not_equal_zero_one :
    (comparison parameters .notEqual zero one).integer.value = 1 := by cbv

theorem comparison_less_equal_identical :
    (comparison parameters .lessEqual one one).integer.value = 1 := by cbv

theorem comparison_greater_equal_strictly_less :
    (comparison parameters .greaterEqual zero one).integer.value = 0 := by cbv

def signMagnitude : IntegerFormat := .signed 3 (by decide) .signMagnitude
def onesComplement : IntegerFormat := .signed 3 (by decide) .onesComplement
def twosComplementTrap : IntegerFormat := .signed 3 (by decide) (.twosComplement false)

def represented (format : IntegerFormat) (integer : Int) (valid : format.Represents integer) :=
  canonicalRepresentation format ⟨integer, valid⟩

theorem sign_magnitude_bitwise_or :
    bitwiseWord signMagnitude .preserve .or
      (represented signMagnitude (-3) (by decide)) (represented signMagnitude 4 (by decide)) =
      .value (-7) false := by cbv

theorem ones_complement_bitwise_or :
    bitwiseWord onesComplement .preserve .or
      (represented onesComplement (-3) (by decide)) (represented onesComplement 4 (by decide)) =
      .value (-3) false := by cbv

theorem sign_magnitude_complement :
    complementWord signMagnitude .preserve (represented signMagnitude 3 (by decide)) = .value (-4) false := by cbv

theorem ones_complement_complement :
    complementWord onesComplement .preserve (represented onesComplement 3 (by decide)) = .value (-3) false := by cbv

theorem ones_complement_zero_generates_negative_zero :
    complementWord onesComplement .preserve (represented onesComplement 0 (by decide)) = .value 0 true := by cbv

theorem ones_complement_zero_can_normalize :
    complementWord onesComplement .normalize (represented onesComplement 0 (by decide)) = .value 0 false := by cbv

theorem ones_complement_unsupported_negative_zero_undefined :
    complementWord onesComplement .unsupported (represented onesComplement 0 (by decide)) =
      .undefined .unsupportedNegativeZero := by cbv

theorem sign_magnitude_complement_maximum_negative_zero :
    complementWord signMagnitude .preserve (represented signMagnitude 7 (by decide)) = .value 0 true := by cbv

theorem twos_complement_trap_minimum :
    complementWord twosComplementTrap .unsupported (represented twosComplementTrap 7 (by decide)) =
      .undefined .minimumTrap := by cbv

def negativeZeroOperand : RepresentationValue onesComplement :=
  ⟨15, 0, true, .onesComplementZero 3 (by decide) .normal _ .normal⟩

theorem normal_negative_zero_operand_is_retained :
    bitwiseWord onesComplement .preserve .or negativeZeroOperand (represented onesComplement 0 (by decide)) =
      .value 0 true := by cbv

theorem canonical_positive_zero_is_distinct_from_negative_zero :
    (canonicalRepresentation onesComplement ⟨0, by decide⟩).word ≠ negativeZeroOperand.word := by decide

theorem unary_result_has_independent_derivation :
    TypedUnaryEvaluation parameters .unsupported .minus charMaximum
      (unary parameters .unsupported .minus charMaximum).raw :=
  (unary_iff parameters .unsupported .minus charMaximum _).mp rfl

theorem shifted_result_has_independent_derivation :
    TypedShiftEvaluation parameters .arithmetic .right minusThree one
      (shift parameters .arithmetic .right minusThree one).raw :=
  (shift_iff parameters .arithmetic .right minusThree one _).mp rfl

theorem bitwise_result_has_independent_derivation :
    TypedBitwiseEvaluation parameters (signalingPolicy 9) .unsupported .and minusOne (unsignedValue 255 (by decide))
      (bitwise parameters .unsupported .and minusOne (unsignedValue 255 (by decide))).raw :=
  (bitwise_iff parameters (signalingPolicy 9) .unsupported .and minusOne (unsignedValue 255 (by decide)) _).mp rfl

end Mettapedia.Languages.C11.IntegerOperatorControls
