import Mettapedia.Languages.C11.IntegerConversion
import Mettapedia.Languages.C11.IntegerDivision

/-!
# C11 arithmetic on already-promoted integer operands

N1570 6.2.5p9 gives unsigned arithmetic its target modulus. N1570 6.5p5
excludes unrepresentable signed results; 6.5.5 excludes a zero divisor and an
unrepresentable quotient for both division and remainder. These arithmetic
failures remain distinct from the implementation-defined signed conversion
policy of 6.3.1.3.

Operands retain their format and range proof. This layer covers addition,
subtraction, multiplication, division and remainder after integer promotions
and usual arithmetic conversions. Bitwise operations, shifts, floating and
complex arithmetic, object representations and expression sequencing remain
separate language obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11

inductive IntegerBinaryOperator where
  | add
  | subtract
  | multiply
  | divide
  | remainder
  deriving DecidableEq, Repr

inductive ArithmeticFault where
  | divisionByZero
  | overflow
  deriving DecidableEq, Repr

inductive IntegerArithmeticOutcome where
  | value (integer : Int)
  | undefined (reason : ArithmeticFault)
  deriving DecidableEq, Repr

def normalizeArithmetic (format : IntegerFormat) (integer : Int) : IntegerArithmeticOutcome :=
  match format with
  | .unsigned precision _ => .value (integer % powerOfTwo precision)
  | .signed _ _ _ =>
      if format.Represents integer then .value integer else .undefined .overflow

inductive ArithmeticReduction : IntegerFormat → Int → IntegerArithmeticOutcome → Prop where
  | unsigned (precision : Nat) (positive : 0 < precision) (integer result : Int)
      (inRange : (IntegerFormat.unsigned precision positive).Represents result)
      (adjusted : ∃ multiple : Int, result = integer + multiple * powerOfTwo precision) :
      ArithmeticReduction (.unsigned precision positive) integer (.value result)
  | signedWithin (precision : Nat) (positive : 0 < precision)
      (representation : SignedRepresentation) (integer : Int)
      (inRange : (IntegerFormat.signed precision positive representation).Represents integer) :
      ArithmeticReduction (.signed precision positive representation) integer (.value integer)
  | signedOverflow (precision : Nat) (positive : 0 < precision)
      (representation : SignedRepresentation) (integer : Int)
      (outside : ¬ (IntegerFormat.signed precision positive representation).Represents integer) :
      ArithmeticReduction (.signed precision positive representation) integer (.undefined .overflow)

theorem normalizeArithmetic_sound (format : IntegerFormat) (integer : Int) :
    ArithmeticReduction format integer (normalizeArithmetic format integer) := by
  cases format with
  | unsigned precision positive =>
      exact ArithmeticReduction.unsigned precision positive integer
        (integer % powerOfTwo precision)
        (unsigned_reduction_in_range precision positive integer)
        (unsigned_reduction_adjusts precision integer)
  | signed precision positive representation =>
      by_cases inRange : (IntegerFormat.signed precision positive representation).Represents integer
      · simpa only [normalizeArithmetic, if_pos inRange] using
          ArithmeticReduction.signedWithin precision positive representation integer inRange
      · simpa only [normalizeArithmetic, if_neg inRange] using
          ArithmeticReduction.signedOverflow precision positive representation integer inRange

theorem normalizeArithmetic_complete (format : IntegerFormat) (integer : Int)
    (outcome : IntegerArithmeticOutcome) (reduced : ArithmeticReduction format integer outcome) :
    normalizeArithmetic format integer = outcome := by
  cases reduced with
  | unsigned precision positive integer result inRange adjusted =>
      simp only [normalizeArithmetic,
        unsigned_reduction_unique precision positive integer result inRange adjusted]
  | signedWithin precision positive representation integer inRange =>
      simp only [normalizeArithmetic, if_pos inRange]
  | signedOverflow precision positive representation integer outside =>
      simp only [normalizeArithmetic, if_neg outside]

def evaluateDivision (format : IntegerFormat) (dividend divisor : Int)
    (remainder : Bool) : IntegerArithmeticOutcome :=
  match divideIntegers dividend divisor with
  | none => .undefined .divisionByZero
  | some (quotient, residue) =>
      if format.Represents quotient then
        normalizeArithmetic format (if remainder then residue else quotient)
      else .undefined .overflow

inductive DivisionEvaluation (format : IntegerFormat) (dividend divisor : Int)
    (remainder : Bool) : IntegerArithmeticOutcome → Prop where
  | zeroDivisor (zero : divisor = 0) : DivisionEvaluation format dividend divisor remainder
      (.undefined .divisionByZero)
  | computed (quotient residue : Int)
      (division : IntegerDivision dividend divisor quotient residue)
      (quotientFits : format.Represents quotient) (outcome : IntegerArithmeticOutcome)
      (reduced : ArithmeticReduction format (if remainder then residue else quotient) outcome) :
      DivisionEvaluation format dividend divisor remainder outcome
  | quotientOverflow (quotient residue : Int)
      (division : IntegerDivision dividend divisor quotient residue)
      (outside : ¬ format.Represents quotient) :
      DivisionEvaluation format dividend divisor remainder (.undefined .overflow)

theorem evaluateDivision_sound (format : IntegerFormat) (dividend divisor : Int) (remainder : Bool) :
    DivisionEvaluation format dividend divisor remainder
      (evaluateDivision format dividend divisor remainder) := by
  by_cases zero : divisor = 0
  · simpa only [evaluateDivision, divideIntegers, if_pos zero] using
      DivisionEvaluation.zeroDivisor (format := format) (dividend := dividend)
        (remainder := remainder) zero
  · have division := divideIntegers_sound dividend divisor (dividend.tdiv divisor)
      (dividend.tmod divisor) (by simp only [divideIntegers, if_neg zero])
    by_cases fits : format.Represents (dividend.tdiv divisor)
    · simpa only [evaluateDivision, divideIntegers, if_neg zero, if_pos fits] using
        DivisionEvaluation.computed (dividend.tdiv divisor) (dividend.tmod divisor)
          division fits _ (normalizeArithmetic_sound format _)
    · simpa only [evaluateDivision, divideIntegers, if_neg zero, if_neg fits] using
        DivisionEvaluation.quotientOverflow (remainder := remainder)
          (dividend.tdiv divisor) (dividend.tmod divisor) division fits

theorem evaluateDivision_complete (format : IntegerFormat) (dividend divisor : Int)
    (remainder : Bool) (outcome : IntegerArithmeticOutcome)
    (evaluated : DivisionEvaluation format dividend divisor remainder outcome) :
    evaluateDivision format dividend divisor remainder = outcome := by
  cases evaluated with
  | zeroDivisor zero => simp only [evaluateDivision, divideIntegers, if_pos zero]
  | computed quotient residue division quotientFits outcome reduced =>
      rw [evaluateDivision, divideIntegers_complete dividend divisor quotient residue division]
      simp only [if_pos quotientFits]
      exact normalizeArithmetic_complete format _ outcome reduced
  | quotientOverflow quotient residue division outside =>
      rw [evaluateDivision, divideIntegers_complete dividend divisor quotient residue division]
      simp only [if_neg outside]

def evaluateIntegerBinary (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) : IntegerArithmeticOutcome :=
  match operation with
  | .add => normalizeArithmetic format (left.value + right.value)
  | .subtract => normalizeArithmetic format (left.value - right.value)
  | .multiply => normalizeArithmetic format (left.value * right.value)
  | .divide => evaluateDivision format left.value right.value false
  | .remainder => evaluateDivision format left.value right.value true

inductive IntegerBinaryEvaluation (format : IntegerFormat) (left right : IntegerValue format) :
    IntegerBinaryOperator → IntegerArithmeticOutcome → Prop where
  | add (outcome : IntegerArithmeticOutcome)
      (reduced : ArithmeticReduction format (left.value + right.value) outcome) :
      IntegerBinaryEvaluation format left right .add outcome
  | subtract (outcome : IntegerArithmeticOutcome)
      (reduced : ArithmeticReduction format (left.value - right.value) outcome) :
      IntegerBinaryEvaluation format left right .subtract outcome
  | multiply (outcome : IntegerArithmeticOutcome)
      (reduced : ArithmeticReduction format (left.value * right.value) outcome) :
      IntegerBinaryEvaluation format left right .multiply outcome
  | divide (outcome : IntegerArithmeticOutcome)
      (evaluated : DivisionEvaluation format left.value right.value false outcome) :
      IntegerBinaryEvaluation format left right .divide outcome
  | remainder (outcome : IntegerArithmeticOutcome)
      (evaluated : DivisionEvaluation format left.value right.value true outcome) :
      IntegerBinaryEvaluation format left right .remainder outcome

theorem evaluateIntegerBinary_sound (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) :
    IntegerBinaryEvaluation format left right operation
      (evaluateIntegerBinary format operation left right) := by
  cases operation with
  | add => exact IntegerBinaryEvaluation.add _ (normalizeArithmetic_sound format _)
  | subtract => exact IntegerBinaryEvaluation.subtract _ (normalizeArithmetic_sound format _)
  | multiply => exact IntegerBinaryEvaluation.multiply _ (normalizeArithmetic_sound format _)
  | divide => exact IntegerBinaryEvaluation.divide _ (evaluateDivision_sound format _ _ false)
  | remainder => exact IntegerBinaryEvaluation.remainder _ (evaluateDivision_sound format _ _ true)

theorem evaluateIntegerBinary_complete (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) (outcome : IntegerArithmeticOutcome)
    (evaluated : IntegerBinaryEvaluation format left right operation outcome) :
    evaluateIntegerBinary format operation left right = outcome := by
  cases evaluated with
  | add outcome reduced => exact normalizeArithmetic_complete format _ outcome reduced
  | subtract outcome reduced => exact normalizeArithmetic_complete format _ outcome reduced
  | multiply outcome reduced => exact normalizeArithmetic_complete format _ outcome reduced
  | divide outcome evaluated => exact evaluateDivision_complete format _ _ false outcome evaluated
  | remainder outcome evaluated => exact evaluateDivision_complete format _ _ true outcome evaluated

theorem evaluateIntegerBinary_iff (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) (outcome : IntegerArithmeticOutcome) :
    evaluateIntegerBinary format operation left right = outcome ↔
      IntegerBinaryEvaluation format left right operation outcome := by
  constructor
  · intro equal
    rw [← equal]
    exact evaluateIntegerBinary_sound format operation left right
  · exact evaluateIntegerBinary_complete format operation left right outcome

theorem unsigned_quotient_representable (precision : Nat) (positive : 0 < precision)
    (left right : IntegerValue (.unsigned precision positive)) :
    (IntegerFormat.unsigned precision positive).Represents (left.value.tdiv right.value) := by
  have leftRange := left.valid
  have rightRange := right.valid
  simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper] at *
  exact ⟨Int.tdiv_nonneg leftRange.1 rightRange.1,
    le_trans (Int.tdiv_le_self right.value leftRange.1) leftRange.2⟩

theorem remainder_representable (format : IntegerFormat) (left right : IntegerValue format)
    (quotient residue : Int) (division : IntegerDivision left.value right.value quotient residue) :
    format.Represents residue := by
  have leftRange := left.valid
  have rightRange := right.valid
  cases format with
  | unsigned precision positive =>
      simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper] at *
      have bounds := division.nonnegative leftRange.1
      rw [Int.natAbs_of_nonneg rightRange.1] at bounds
      omega
  | signed precision positive representation =>
      have balance := IntegerFormat.signed_range_balance precision positive representation
      have zero := (IntegerFormat.signed precision positive representation).zero_representable
      simp only [IntegerFormat.Represents] at leftRange rightRange zero ⊢
      by_cases leftNonnegative : 0 ≤ left.value
      · have bounds := division.nonnegative leftNonnegative
        by_cases rightNonnegative : 0 ≤ right.value
        · rw [Int.natAbs_of_nonneg rightNonnegative] at bounds
          omega
        · rw [Int.ofNat_natAbs_of_nonpos (by omega)] at bounds
          omega
      · have bounds := division.nonpositive (by omega)
        by_cases rightNonnegative : 0 ≤ right.value
        · rw [Int.natAbs_of_nonneg rightNonnegative] at bounds
          omega
        · rw [Int.ofNat_natAbs_of_nonpos (by omega)] at bounds
          omega

end Mettapedia.Languages.C11

namespace Mettapedia.Languages.C11

/-- Unsigned remainder is justified by C's independent quotient/remainder
judgment, including representability of the quotient. -/
theorem unsigned_remainder_c11 (width : Nat) (positive : 0 < width)
    (left right : IntegerValue (.unsigned width positive))
    (nonzero : right.value ≠ 0) :
    IntegerBinaryEvaluation (.unsigned width positive) left right .remainder
      (.value (left.value.tmod right.value)) := by
  have division : IntegerDivision left.value right.value
      (left.value.tdiv right.value) (left.value.tmod right.value) :=
    divideIntegers_sound _ _ _ _ (by simp only [divideIntegers, if_neg nonzero])
  refine .remainder _ (.computed _ _ division
    (unsigned_quotient_representable width positive left right) _ ?_)
  exact .unsigned width positive _ _
    (remainder_representable _ left right _ _ division) ⟨0, by simp⟩

theorem unsigned_remainder_zero_c11 (width : Nat) (positive : 0 < width)
    (left right : IntegerValue (.unsigned width positive)) (zero : right.value = 0) :
    IntegerBinaryEvaluation (.unsigned width positive) left right .remainder
      (.undefined .divisionByZero) :=
  .remainder _ (.zeroDivisor zero)

end Mettapedia.Languages.C11
