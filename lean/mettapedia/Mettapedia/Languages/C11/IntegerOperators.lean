import Mettapedia.Languages.C11.IntegerScalar
import Mettapedia.Languages.C11.IntegerBits
import Mathlib.Data.Nat.Bitwise

/-!
# C11 promoted integer operators

Unary operators and shifts use integer promotions; bitwise and comparison
operators use the usual arithmetic conversions. Bit operations are specified
by their individual value/sign bits, independently of the executable word
operations. All three signed representations are retained. Negative-zero
generation and negative signed right shifts have named policies.

These operations consume evaluated canonical integer operands. The scalar
adapter chooses their canonical representations. The word interface also
retains noncanonical normal negative zeros. Padding, operand evaluation,
sequencing, plain-char/enum/bit-field elaboration and compiler correspondence
remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerOperators

universe u

inductive Unary where
  | plus
  | minus
  | complement
  deriving DecidableEq, Repr

inductive Shift where
  | left
  | right
  deriving DecidableEq, Repr

inductive Bitwise where
  | and
  | or
  | xor
  deriving DecidableEq, Repr

inductive Comparison where
  | less
  | lessEqual
  | greater
  | greaterEqual
  | equal
  | notEqual
  deriving DecidableEq, Repr

inductive Fault where
  | arithmeticOverflow
  | negativeShiftCount
  | shiftCountTooLarge
  | negativeSignedLeft
  | signedLeftOverflow
  | unsupportedNegativeZero
  | minimumTrap
  deriving DecidableEq, Repr

inductive RawResult where
  | value (integer : Int) (negativeZero : Bool)
  | undefined (reason : Fault)
  deriving DecidableEq, Repr

inductive NegativeZeroPolicy where
  | preserve
  | normalize
  | unsupported
  deriving DecidableEq, Repr

def bit (operation : Bitwise) (left right : Bool) : Bool := match operation with
  | .and => left && right
  | .or => left || right
  | .xor => bne left right

def wordBinary (operation : Bitwise) (left right : Nat) : Nat := match operation with
  | .and => left &&& right
  | .or => left ||| right
  | .xor => left ^^^ right

/-- The clause specifies every bit; it does not invoke the word evaluator. -/
def WordBinary (operation : Bitwise) (left right result : Nat) : Prop :=
  ∀ index, result.testBit index = bit operation (left.testBit index) (right.testBit index)

theorem wordBinary_sound (operation : Bitwise) (left right : Nat) :
    WordBinary operation left right (wordBinary operation left right) := by
  intro index
  cases operation <;> simp [wordBinary, bit]

theorem wordBinary_complete (operation : Bitwise) (left right result : Nat)
    (related : WordBinary operation left right result) : wordBinary operation left right = result := by
  apply Nat.eq_of_testBit_eq
  intro index
  exact (wordBinary_sound operation left right index).trans (related index).symm

theorem wordBinary_bound (operation : Bitwise) (width left right : Nat)
    (leftBound : left < 2 ^ width) (rightBound : right < 2 ^ width) :
    wordBinary operation left right < 2 ^ width := by
  cases operation
  · exact Nat.bitwise_lt_two_pow leftBound rightBound
  · exact Nat.bitwise_lt_two_pow leftBound rightBound
  · exact Nat.xor_lt_two_pow leftBound rightBound

def wordComplement (width word : Nat) : Nat := (2 ^ width - 1) ^^^ word

def WordComplement (width word result : Nat) : Prop :=
  ∀ index, result.testBit index = if index < width then !(word.testBit index) else false

theorem wordComplement_sound (width word : Nat) (bounded : word < 2 ^ width) :
    WordComplement width word (wordComplement width word) := by
  intro index
  by_cases below : index < width
  · simp [wordComplement, below]
  · have above := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le bounded (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : width ≤ index)))
    simp [wordComplement, below, above]

theorem wordComplement_complete (width word result : Nat) (bounded : word < 2 ^ width)
    (related : WordComplement width word result) : wordComplement width word = result := by
  apply Nat.eq_of_testBit_eq
  intro index
  exact (wordComplement_sound width word bounded index).trans (related index).symm

theorem wordComplement_bound (width word : Nat) (bounded : word < 2 ^ width) :
    wordComplement width word < 2 ^ width := by
  apply Nat.xor_lt_two_pow
  · have positive := Nat.two_pow_pos width
    omega
  · exact bounded

def interpretBits (policy : NegativeZeroPolicy) (input : IntegerBits.Outcome) : RawResult := match input with
  | .value integer false => .value integer false
  | .value integer true => match policy with
      | .preserve => .value integer true
      | .normalize => .value integer false
      | .unsupported => .undefined .unsupportedNegativeZero
  | .trap .minimum => .undefined .minimumTrap
  | .trap .negativeZero => .undefined .unsupportedNegativeZero

inductive BitInterpretation (policy : NegativeZeroPolicy) : IntegerBits.Outcome → RawResult → Prop where
  | ordinary (integer : Int) : BitInterpretation policy (.value integer false) (.value integer false)
  | preserve (integer : Int) (selected : policy = .preserve) :
      BitInterpretation policy (.value integer true) (.value integer true)
  | normalize (integer : Int) (selected : policy = .normalize) :
      BitInterpretation policy (.value integer true) (.value integer false)
  | unsupported (integer : Int) (selected : policy = .unsupported) :
      BitInterpretation policy (.value integer true) (.undefined .unsupportedNegativeZero)
  | minimum : BitInterpretation policy (.trap .minimum) (.undefined .minimumTrap)
  | negativeZeroTrap : BitInterpretation policy (.trap .negativeZero) (.undefined .unsupportedNegativeZero)

theorem interpretBits_sound (policy : NegativeZeroPolicy) (input : IntegerBits.Outcome) :
    BitInterpretation policy input (interpretBits policy input) := by
  cases input with
  | value integer negativeZero =>
      cases negativeZero with
      | false => exact .ordinary integer
      | true =>
          cases policy with
          | preserve => exact .preserve integer rfl
          | normalize => exact .normalize integer rfl
          | unsupported => exact .unsupported integer rfl
  | trap reason => cases reason <;> constructor

theorem interpretBits_complete (policy : NegativeZeroPolicy) (input : IntegerBits.Outcome)
    (result : RawResult) (interpreted : BitInterpretation policy input result) :
    interpretBits policy input = result := by
  cases interpreted <;> subst_vars <;> rfl

def readWord (format : IntegerFormat) (policy : NegativeZeroPolicy) (word : Nat) : Option RawResult :=
  (IntegerBits.read format .normal word).map (interpretBits policy)

inductive WordReading (format : IntegerFormat) (policy : NegativeZeroPolicy) (word : Nat) :
    RawResult → Prop where
  | read (outcome : IntegerBits.Outcome) (result : RawResult)
      (reading : IntegerBits.Reading format .normal word outcome)
      (interpretation : BitInterpretation policy outcome result) : WordReading format policy word result

theorem readWord_sound (format : IntegerFormat) (policy : NegativeZeroPolicy) (word : Nat)
    (result : RawResult) (computed : readWord format policy word = some result) :
    WordReading format policy word result := by
  unfold readWord at computed
  cases observed : IntegerBits.read format .normal word with
  | none => simp [observed] at computed
  | some outcome =>
      simp only [observed, Option.map_some, Option.some.injEq] at computed
      rw [← computed]
      exact .read outcome _ (IntegerBits.read_sound format .normal word outcome observed)
        (interpretBits_sound policy outcome)

theorem readWord_complete (format : IntegerFormat) (policy : NegativeZeroPolicy) (word : Nat)
    (result : RawResult) (reading : WordReading format policy word result) :
    readWord format policy word = some result := by
  cases reading with
  | read outcome result reading interpretation =>
      simp only [readWord, IntegerBits.read_complete format .normal word outcome reading,
        Option.map_some, interpretBits_complete policy outcome result interpretation]

theorem WordReading.value_range {format : IntegerFormat} {policy : NegativeZeroPolicy}
    {word : Nat} {integer : Int} {negativeZero : Bool}
    (reading : WordReading format policy word (.value integer negativeZero)) :
    format.Represents integer := by
  cases reading with
  | read outcome result reading interpretation =>
      cases interpretation <;>
        exact IntegerBits.Reading.value_in_range format .normal word _ reading _ _ rfl

theorem readWord_exists (format : IntegerFormat) (policy : NegativeZeroPolicy) (word : Nat)
    (bounded : word < 2 ^ IntegerBits.width format) :
    ∃ result, readWord format policy word = some result := by
  unfold readWord IntegerBits.read
  rw [if_pos bounded]
  exact ⟨_, rfl⟩

structure RepresentationValue (format : IntegerFormat) where
  word : Nat
  integer : Int
  negativeZero : Bool
  reading : IntegerBits.Reading format .normal word (.value integer negativeZero)

theorem RepresentationValue.bound {format : IntegerFormat} (value : RepresentationValue format) :
    value.word < 2 ^ IntegerBits.width format :=
  IntegerBits.read_defined_bound format .normal value.word _
    (IntegerBits.read_complete format .normal value.word _ value.reading)

def canonicalRepresentation (format : IntegerFormat) (value : IntegerValue format) :
    RepresentationValue format :=
  ⟨IntegerBits.canonicalWord format value.value, value.value, false,
    IntegerBits.canonicalWord_reading format .normal value.value value.valid⟩

def readBits (format : IntegerFormat) (policy : NegativeZeroPolicy) (word : Nat) : RawResult :=
  interpretBits policy (match format with
    | .unsigned _ _ => .value word false
    | .signed _ _ representation =>
        IntegerBits.readSigned .normal representation (IntegerBits.capacity format) word)

theorem readBits_readWord (format : IntegerFormat) (policy : NegativeZeroPolicy) (word : Nat)
    (bounded : word < 2 ^ IntegerBits.width format) :
    readWord format policy word = some (readBits format policy word) := by
  simp only [readWord, IntegerBits.read, if_pos bounded, Option.map_some, readBits]
  rfl

theorem readBits_sound (format : IntegerFormat) (policy : NegativeZeroPolicy) (word : Nat)
    (bounded : word < 2 ^ IntegerBits.width format) :
    WordReading format policy word (readBits format policy word) :=
  readWord_sound format policy word _ (readBits_readWord format policy word bounded)

theorem readBits_complete (format : IntegerFormat) (policy : NegativeZeroPolicy) (word : Nat)
    (bounded : word < 2 ^ IntegerBits.width format) (result : RawResult)
    (reading : WordReading format policy word result) : readBits format policy word = result :=
  Option.some.inj ((readBits_readWord format policy word bounded).symm.trans
    (readWord_complete format policy word result reading))

def bitwiseWord (format : IntegerFormat) (policy : NegativeZeroPolicy) (operation : Bitwise)
    (left right : RepresentationValue format) : RawResult :=
  readBits format policy (wordBinary operation left.word right.word)

inductive BitwiseEvaluation (format : IntegerFormat) (policy : NegativeZeroPolicy)
    (operation : Bitwise) (left right : RepresentationValue format) : RawResult → Prop where
  | bits (word : Nat) (result : RawResult) (bitRelation : WordBinary operation left.word right.word word)
      (reading : WordReading format policy word result) :
      BitwiseEvaluation format policy operation left right result

theorem bitwiseWord_sound (format : IntegerFormat) (policy : NegativeZeroPolicy) (operation : Bitwise)
    (left right : RepresentationValue format) :
    BitwiseEvaluation format policy operation left right (bitwiseWord format policy operation left right) :=
  .bits _ _ (wordBinary_sound operation left.word right.word)
    (readBits_sound format policy _ (wordBinary_bound operation _ _ _ left.bound right.bound))

theorem bitwiseWord_complete (format : IntegerFormat) (policy : NegativeZeroPolicy) (operation : Bitwise)
    (left right : RepresentationValue format) (result : RawResult)
    (evaluated : BitwiseEvaluation format policy operation left right result) :
    bitwiseWord format policy operation left right = result := by
  cases evaluated with
  | bits word result relation reading =>
      have same := wordBinary_complete operation left.word right.word word relation
      unfold bitwiseWord
      rw [same]
      exact readBits_complete format policy word (same ▸
        wordBinary_bound operation _ _ _ left.bound right.bound) result reading

def complementWord (format : IntegerFormat) (policy : NegativeZeroPolicy)
    (input : RepresentationValue format) : RawResult :=
  readBits format policy (wordComplement (IntegerBits.width format) input.word)

inductive ComplementEvaluation (format : IntegerFormat) (policy : NegativeZeroPolicy)
    (input : RepresentationValue format) : RawResult → Prop where
  | bits (word : Nat) (result : RawResult)
      (bitRelation : WordComplement (IntegerBits.width format) input.word word)
      (reading : WordReading format policy word result) : ComplementEvaluation format policy input result

theorem complementWord_sound (format : IntegerFormat) (policy : NegativeZeroPolicy)
    (input : RepresentationValue format) :
    ComplementEvaluation format policy input (complementWord format policy input) :=
  .bits _ _ (wordComplement_sound _ _ input.bound)
    (readBits_sound format policy _ (wordComplement_bound _ _ input.bound))

theorem complementWord_complete (format : IntegerFormat) (policy : NegativeZeroPolicy)
    (input : RepresentationValue format) (result : RawResult)
    (evaluated : ComplementEvaluation format policy input result) :
    complementWord format policy input = result := by
  cases evaluated with
  | bits word result relation reading =>
      have same := wordComplement_complete _ input.word word input.bound relation
      unfold complementWord
      rw [same]
      exact readBits_complete format policy word (same ▸ wordComplement_bound _ _ input.bound) result reading

def reduceNumeric (format : IntegerFormat) (input : Int) : RawResult := match format with
  | .unsigned bits _ => .value (input % powerOfTwo bits) false
  | .signed _ _ _ =>
      if format.Represents input then .value input false else .undefined .arithmeticOverflow

inductive NumericReduction : IntegerFormat → Int → RawResult → Prop where
  | unsigned (bits : Nat) (positive : 0 < bits) (input result : Int)
      (bounded : (IntegerFormat.unsigned bits positive).Represents result)
      (adjusted : ∃ multiple : Int, result = input + multiple * powerOfTwo bits) :
      NumericReduction (.unsigned bits positive) input (.value result false)
  | signed (bits : Nat) (positive : 0 < bits) (representation : SignedRepresentation) (input : Int)
      (bounded : (IntegerFormat.signed bits positive representation).Represents input) :
      NumericReduction (.signed bits positive representation) input (.value input false)
  | overflow (bits : Nat) (positive : 0 < bits) (representation : SignedRepresentation) (input : Int)
      (outside : ¬ (IntegerFormat.signed bits positive representation).Represents input) :
      NumericReduction (.signed bits positive representation) input (.undefined .arithmeticOverflow)

theorem reduceNumeric_sound (format : IntegerFormat) (input : Int) :
    NumericReduction format input (reduceNumeric format input) := by
  cases format with
  | unsigned bits positive =>
      exact .unsigned bits positive input _ (unsigned_reduction_in_range bits positive input)
        (unsigned_reduction_adjusts bits input)
  | signed bits positive representation =>
      by_cases bounded : (IntegerFormat.signed bits positive representation).Represents input
      · simpa only [reduceNumeric, if_pos bounded] using NumericReduction.signed bits positive representation input bounded
      · simpa only [reduceNumeric, if_neg bounded] using NumericReduction.overflow bits positive representation input bounded

theorem reduceNumeric_complete (format : IntegerFormat) (input : Int) (result : RawResult)
    (reduced : NumericReduction format input result) : reduceNumeric format input = result := by
  cases reduced with
  | unsigned bits positive input result bounded adjusted =>
      simp only [reduceNumeric, unsigned_reduction_unique bits positive input result bounded adjusted]
  | signed bits positive representation input bounded => simp only [reduceNumeric, if_pos bounded]
  | overflow bits positive representation input outside => simp only [reduceNumeric, if_neg outside]

theorem NumericReduction.value_range {format : IntegerFormat} {input result : Int} {negativeZero : Bool}
    (reduced : NumericReduction format input (.value result negativeZero)) : format.Represents result := by
  cases reduced <;> assumption

inductive RightShiftPolicy where
  | arithmetic
  | towardZero
  deriving DecidableEq, Repr

def negativeRightShift (policy : RightShiftPolicy) (input : Int) (count : Nat) : Int := match policy with
  | .arithmetic => input / powerOfTwo count
  | .towardZero => -((-input) / powerOfTwo count)

theorem negativeRightShift_range (format : IntegerFormat) (policy : RightShiftPolicy)
    (input : IntegerValue format) (negative : input.value < 0) (count : Nat) :
    format.Represents (negativeRightShift policy input.value count) := by
  have power := powerOfTwo_positive count
  have low := input.valid.1
  have high := format.zero_representable.2
  cases policy with
  | arithmetic =>
      have lower := Int.self_le_ediv_of_nonpos_of_nonneg (le_of_lt negative) (le_of_lt power)
      have upper : input.value / powerOfTwo count < 0 := Int.ediv_neg_of_neg_of_pos negative power
      exact ⟨le_trans low lower, le_trans (le_of_lt upper) high⟩
  | towardZero =>
      have quotientLow := Int.ediv_nonneg (by omega : 0 ≤ -input.value) (le_of_lt power)
      have quotientHigh := Int.ediv_le_self (powerOfTwo count) (by omega : 0 ≤ -input.value)
      change format.lower ≤ -((-input.value) / powerOfTwo count) ∧
        -((-input.value) / powerOfTwo count) ≤ format.upper
      omega

def validShiftCount (format : IntegerFormat) (count : Int) : Prop :=
  0 ≤ count ∧ count < (IntegerBits.width format : Int)

instance (format : IntegerFormat) (count : Int) : Decidable (validShiftCount format count) :=
  inferInstanceAs (Decidable (0 ≤ count ∧ count < (IntegerBits.width format : Int)))

def shiftValue (format : IntegerFormat) (policy : RightShiftPolicy) (operation : Shift)
    (input : IntegerValue format) (count : Int) : RawResult :=
  if count < 0 then .undefined .negativeShiftCount
  else if (IntegerBits.width format : Int) ≤ count then .undefined .shiftCountTooLarge
  else match operation with
    | .left => match format with
        | .unsigned _ _ => reduceNumeric format (input.value * powerOfTwo count.toNat)
        | .signed _ _ _ =>
            if input.value < 0 then .undefined .negativeSignedLeft
            else if format.Represents (input.value * powerOfTwo count.toNat)
            then .value (input.value * powerOfTwo count.toNat) false
            else .undefined .signedLeftOverflow
    | .right =>
        if input.value < 0 then .value (negativeRightShift policy input.value count.toNat) false
        else .value (input.value / powerOfTwo count.toNat) false

inductive ShiftEvaluation (format : IntegerFormat) (policy : RightShiftPolicy)
    (operation : Shift) (input : IntegerValue format) (count : Int) : RawResult → Prop where
  | negativeCount (negative : count < 0) :
      ShiftEvaluation format policy operation input count (.undefined .negativeShiftCount)
  | excessiveCount (nonnegative : 0 ≤ count) (excessive : (IntegerBits.width format : Int) ≤ count) :
      ShiftEvaluation format policy operation input count (.undefined .shiftCountTooLarge)
  | unsignedLeft (bits : Nat) (positive : 0 < bits) (same : format = .unsigned bits positive)
      (permitted : validShiftCount format count) (result : RawResult)
      (reduced : NumericReduction format (input.value * powerOfTwo count.toNat) result)
      (left : operation = .left) : ShiftEvaluation format policy operation input count result
  | signedNegativeLeft (bits : Nat) (positive : 0 < bits) (representation : SignedRepresentation)
      (same : format = .signed bits positive representation) (permitted : validShiftCount format count)
      (negative : input.value < 0) (left : operation = .left) :
      ShiftEvaluation format policy operation input count (.undefined .negativeSignedLeft)
  | signedLeft (bits : Nat) (positive : 0 < bits) (representation : SignedRepresentation)
      (same : format = .signed bits positive representation) (permitted : validShiftCount format count)
      (nonnegative : 0 ≤ input.value) (fits : format.Represents (input.value * powerOfTwo count.toNat))
      (left : operation = .left) :
      ShiftEvaluation format policy operation input count (.value (input.value * powerOfTwo count.toNat) false)
  | signedOverflow (bits : Nat) (positive : 0 < bits) (representation : SignedRepresentation)
      (same : format = .signed bits positive representation) (permitted : validShiftCount format count)
      (nonnegative : 0 ≤ input.value) (outside : ¬ format.Represents (input.value * powerOfTwo count.toNat))
      (left : operation = .left) :
      ShiftEvaluation format policy operation input count (.undefined .signedLeftOverflow)
  | rightNonnegative (permitted : validShiftCount format count) (nonnegative : 0 ≤ input.value)
      (right : operation = .right) :
      ShiftEvaluation format policy operation input count (.value (input.value / powerOfTwo count.toNat) false)
  | rightNegative (permitted : validShiftCount format count) (negative : input.value < 0)
      (right : operation = .right) :
      ShiftEvaluation format policy operation input count
        (.value (negativeRightShift policy input.value count.toNat) false)

theorem shiftValue_sound (format : IntegerFormat) (policy : RightShiftPolicy) (operation : Shift)
    (input : IntegerValue format) (count : Int) :
    ShiftEvaluation format policy operation input count (shiftValue format policy operation input count) := by
  by_cases negative : count < 0
  · simpa only [shiftValue, if_pos negative] using ShiftEvaluation.negativeCount (policy := policy)
      (operation := operation) (input := input) negative
  · by_cases excessive : (IntegerBits.width format : Int) ≤ count
    · simpa only [shiftValue, if_neg negative, if_pos excessive] using
        ShiftEvaluation.excessiveCount (policy := policy) (operation := operation)
          (input := input) (by omega) excessive
    · have permitted : validShiftCount format count := ⟨by omega, by omega⟩
      simp only [shiftValue, if_neg negative, if_neg excessive]
      cases operation with
      | left =>
          cases format with
          | unsigned bits positive =>
              exact .unsignedLeft bits positive rfl permitted _ (reduceNumeric_sound _ _) rfl
          | signed bits positive representation =>
              by_cases inputNegative : input.value < 0
              · simpa only [if_pos inputNegative] using
                  ShiftEvaluation.signedNegativeLeft bits positive representation rfl permitted inputNegative rfl
              · by_cases fits : (IntegerFormat.signed bits positive representation).Represents
                    (input.value * powerOfTwo count.toNat)
                · simpa only [if_neg inputNegative, if_pos fits] using
                    ShiftEvaluation.signedLeft bits positive representation rfl permitted (by omega) fits rfl
                · simpa only [if_neg inputNegative, if_neg fits] using
                    ShiftEvaluation.signedOverflow bits positive representation rfl permitted (by omega) fits rfl
      | right =>
          by_cases inputNegative : input.value < 0
          · simpa only [if_pos inputNegative] using ShiftEvaluation.rightNegative permitted inputNegative rfl
          · simpa only [if_neg inputNegative] using ShiftEvaluation.rightNonnegative permitted (by omega) rfl

theorem shiftValue_complete (format : IntegerFormat) (policy : RightShiftPolicy) (operation : Shift)
    (input : IntegerValue format) (count : Int) (result : RawResult)
    (evaluated : ShiftEvaluation format policy operation input count result) :
    shiftValue format policy operation input count = result := by
  cases evaluated with
  | negativeCount negative => simp only [shiftValue, if_pos negative]
  | excessiveCount nonnegative excessive => simp only [shiftValue, if_neg (by omega : ¬ count < 0), if_pos excessive]
  | unsignedLeft bits positive same permitted result reduced left =>
      subst format operation
      obtain ⟨countNonnegative, countBelow⟩ := permitted
      simpa only [shiftValue, if_neg (by omega : ¬ count < 0), if_neg (by omega :
        ¬ (IntegerBits.width (.unsigned bits positive) : Int) ≤ count)] using
        reduceNumeric_complete _ _ result reduced
  | signedNegativeLeft bits positive representation same permitted negative left =>
      subst format operation
      obtain ⟨countNonnegative, countBelow⟩ := permitted
      simp only [shiftValue, if_neg (by omega : ¬ count < 0), if_neg (by omega :
        ¬ (IntegerBits.width (.signed bits positive representation) : Int) ≤ count), if_pos negative]
  | signedLeft bits positive representation same permitted nonnegative fits left =>
      subst format operation
      obtain ⟨countNonnegative, countBelow⟩ := permitted
      simp only [shiftValue, if_neg (by omega : ¬ count < 0), if_neg (by omega :
        ¬ (IntegerBits.width (.signed bits positive representation) : Int) ≤ count),
        if_neg (by omega : ¬ input.value < 0), if_pos fits]
  | signedOverflow bits positive representation same permitted nonnegative outside left =>
      subst format operation
      obtain ⟨countNonnegative, countBelow⟩ := permitted
      simp only [shiftValue, if_neg (by omega : ¬ count < 0), if_neg (by omega :
        ¬ (IntegerBits.width (.signed bits positive representation) : Int) ≤ count),
        if_neg (by omega : ¬ input.value < 0), if_neg outside]
  | rightNonnegative permitted nonnegative right =>
      subst operation
      obtain ⟨countNonnegative, countBelow⟩ := permitted
      simp only [shiftValue, if_neg (by omega : ¬ count < 0), if_neg (by omega :
        ¬ (IntegerBits.width format : Int) ≤ count), if_neg (by omega : ¬ input.value < 0)]
  | rightNegative permitted negative right =>
      subst operation
      obtain ⟨countNonnegative, countBelow⟩ := permitted
      simp only [shiftValue, if_neg (by omega : ¬ count < 0), if_neg (by omega :
        ¬ (IntegerBits.width format : Int) ≤ count), if_pos negative]

theorem ShiftEvaluation.value_range {format : IntegerFormat} {policy : RightShiftPolicy}
    {operation : Shift} {input : IntegerValue format} {count result : Int} {negativeZero : Bool}
    (evaluated : ShiftEvaluation format policy operation input count (.value result negativeZero)) :
    format.Represents result := by
  cases evaluated with
  | unsignedLeft _ _ _ _ _ reduced _ => exact reduced.value_range
  | signedLeft _ _ _ _ _ _ fits _ => exact fits
  | rightNonnegative _ nonnegative _ =>
      have lower := format.zero_representable.1
      have high := input.valid.2
      have quotientLow := Int.ediv_nonneg nonnegative (le_of_lt (powerOfTwo_positive count.toNat))
      have quotientHigh := Int.ediv_le_self (powerOfTwo count.toNat) nonnegative
      exact ⟨le_trans lower quotientLow, le_trans quotientHigh high⟩
  | rightNegative _ negative _ => exact negativeRightShift_range format policy input negative count.toNat

def unaryValue (format : IntegerFormat) (policy : NegativeZeroPolicy) (operation : Unary)
    (input : IntegerValue format) : RawResult := match operation with
  | .plus => .value input.value false
  | .minus => reduceNumeric format (-input.value)
  | .complement => complementWord format policy (canonicalRepresentation format input)

inductive UnaryEvaluation (format : IntegerFormat) (policy : NegativeZeroPolicy)
    (operation : Unary) (input : IntegerValue format) : RawResult → Prop where
  | plus (selected : operation = .plus) : UnaryEvaluation format policy operation input (.value input.value false)
  | minus (selected : operation = .minus) (result : RawResult)
      (reduced : NumericReduction format (-input.value) result) : UnaryEvaluation format policy operation input result
  | complement (selected : operation = .complement) (result : RawResult)
      (evaluated : ComplementEvaluation format policy (canonicalRepresentation format input) result) :
      UnaryEvaluation format policy operation input result

theorem unaryValue_sound (format : IntegerFormat) (policy : NegativeZeroPolicy) (operation : Unary)
    (input : IntegerValue format) : UnaryEvaluation format policy operation input (unaryValue format policy operation input) := by
  cases operation with
  | plus => exact .plus rfl
  | minus => exact .minus rfl _ (reduceNumeric_sound format (-input.value))
  | complement => exact .complement rfl _ (complementWord_sound format policy _)

theorem unaryValue_complete (format : IntegerFormat) (policy : NegativeZeroPolicy) (operation : Unary)
    (input : IntegerValue format) (result : RawResult)
    (evaluated : UnaryEvaluation format policy operation input result) : unaryValue format policy operation input = result := by
  cases evaluated with
  | plus selected => subst operation; rfl
  | minus selected result reduced => subst operation; exact reduceNumeric_complete format _ result reduced
  | complement selected result evaluated => subst operation; exact complementWord_complete format policy _ result evaluated

theorem UnaryEvaluation.value_range {format : IntegerFormat} {policy : NegativeZeroPolicy}
    {operation : Unary} {input : IntegerValue format} {result : Int} {negativeZero : Bool}
    (evaluated : UnaryEvaluation format policy operation input (.value result negativeZero)) : format.Represents result := by
  cases evaluated with
  | plus _ => exact input.valid
  | minus _ _ reduced => exact reduced.value_range
  | complement _ _ evaluated => cases evaluated; exact WordReading.value_range (by assumption)

def Compared (operation : Comparison) (left right : Int) : Prop := match operation with
  | .less => left < right
  | .lessEqual => left ≤ right
  | .greater => right < left
  | .greaterEqual => right ≤ left
  | .equal => left = right
  | .notEqual => left ≠ right

instance (operation : Comparison) (left right : Int) : Decidable (Compared operation left right) := by
  cases operation <;> dsimp [Compared] <;> infer_instance

def compareValue (operation : Comparison) (left right : Int) : Bool := decide (Compared operation left right)

inductive ComparisonEvaluation (operation : Comparison) (left right : Int) : Bool → Prop where
  | holds (trueRelation : Compared operation left right) : ComparisonEvaluation operation left right true
  | fails (falseRelation : ¬ Compared operation left right) : ComparisonEvaluation operation left right false

theorem compareValue_sound (operation : Comparison) (left right : Int) :
    ComparisonEvaluation operation left right (compareValue operation left right) := by
  by_cases holds : Compared operation left right
  · simpa only [compareValue, decide_eq_true holds] using ComparisonEvaluation.holds holds
  · simpa only [compareValue, decide_eq_false holds] using ComparisonEvaluation.fails holds

theorem compareValue_complete (operation : Comparison) (left right : Int) (result : Bool)
    (evaluated : ComparisonEvaluation operation left right result) : compareValue operation left right = result := by
  cases evaluated with
  | holds relation => exact decide_eq_true relation
  | fails relation => exact decide_eq_false relation

def promote {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (input : IntegerScalar.Value parameters) : IntegerScalar.Value parameters :=
  ⟨promoteIntegerType parameters input.type,
    ⟨input.integer.value, (promoteIntegerType_range parameters input.type).represents input.integer.valid⟩⟩

inductive PromotionEvaluation {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (input : IntegerScalar.Value parameters) : IntegerScalar.Value parameters → Prop where
  | promoted (output : IntegerScalar.Value parameters)
      (type : IntegerPromotion parameters input.type output.type)
      (value : output.integer.value = input.integer.value) : PromotionEvaluation parameters input output

theorem promote_sound {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (input : IntegerScalar.Value parameters) : PromotionEvaluation parameters input (promote parameters input) :=
  .promoted _ (promoteIntegerType_sound parameters input.type) rfl

theorem promote_complete {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (input output : IntegerScalar.Value parameters) (evaluated : PromotionEvaluation parameters input output) :
    promote parameters input = output := by
  cases evaluated with
  | promoted type value =>
      exact IntegerScalar.Value.ext _ output
        (promoteIntegerType_complete parameters input.type output.type type) value.symm

structure TypedRaw (Extension : Type u) where
  type : IntegerType Extension
  result : RawResult
  deriving DecidableEq, Repr

def unaryRaw {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : NegativeZeroPolicy) (operation : Unary) (input : IntegerScalar.Value parameters) : TypedRaw Extension :=
  let converted := promote parameters input
  ⟨converted.type, unaryValue (converted.type.format parameters) policy operation converted.integer⟩

inductive TypedUnaryEvaluation {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (policy : NegativeZeroPolicy) (operation : Unary) (input : IntegerScalar.Value parameters) :
    TypedRaw Extension → Prop where
  | promoted (converted : IntegerScalar.Value parameters) (result : RawResult)
      (promotion : PromotionEvaluation parameters input converted)
      (evaluation : UnaryEvaluation (converted.type.format parameters) policy operation converted.integer result) :
      TypedUnaryEvaluation parameters policy operation input ⟨converted.type, result⟩

theorem unaryRaw_sound {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : NegativeZeroPolicy) (operation : Unary) (input : IntegerScalar.Value parameters) :
    TypedUnaryEvaluation parameters policy operation input (unaryRaw parameters policy operation input) :=
  .promoted _ _ (promote_sound parameters input) (unaryValue_sound _ policy operation _)

theorem unaryRaw_complete {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : NegativeZeroPolicy) (operation : Unary) (input : IntegerScalar.Value parameters)
    (result : TypedRaw Extension) (evaluated : TypedUnaryEvaluation parameters policy operation input result) :
    unaryRaw parameters policy operation input = result := by
  cases evaluated with
  | promoted converted result promotion evaluation =>
      unfold unaryRaw
      dsimp only
      rw [promote_complete parameters input converted promotion, unaryValue_complete _ policy operation _ result evaluation]

theorem TypedUnaryEvaluation.value_range {Extension : Type u} {parameters : IntegerTypeParameters Extension}
    {policy : NegativeZeroPolicy} {operation : Unary} {input : IntegerScalar.Value parameters}
    {type : IntegerType Extension} {result : Int} {negativeZero : Bool}
    (evaluated : TypedUnaryEvaluation parameters policy operation input ⟨type, .value result negativeZero⟩) :
    (type.format parameters).Represents result := by
  cases evaluated with
  | promoted converted _ _ evaluation => exact evaluation.value_range

def shiftRaw {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : RightShiftPolicy) (operation : Shift)
    (left right : IntegerScalar.Value parameters) : TypedRaw Extension :=
  let first := promote parameters left
  let second := promote parameters right
  ⟨first.type, shiftValue (first.type.format parameters) policy operation first.integer second.integer.value⟩

inductive TypedShiftEvaluation {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (policy : RightShiftPolicy) (operation : Shift) (left right : IntegerScalar.Value parameters) :
    TypedRaw Extension → Prop where
  | promoted (first second : IntegerScalar.Value parameters) (result : RawResult)
      (leftPromotion : PromotionEvaluation parameters left first)
      (rightPromotion : PromotionEvaluation parameters right second)
      (evaluation : ShiftEvaluation (first.type.format parameters) policy operation first.integer second.integer.value result) :
      TypedShiftEvaluation parameters policy operation left right ⟨first.type, result⟩

theorem shiftRaw_sound {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : RightShiftPolicy) (operation : Shift) (left right : IntegerScalar.Value parameters) :
    TypedShiftEvaluation parameters policy operation left right (shiftRaw parameters policy operation left right) :=
  .promoted _ _ _ (promote_sound parameters left) (promote_sound parameters right)
    (shiftValue_sound _ policy operation _ _)

theorem shiftRaw_complete {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : RightShiftPolicy) (operation : Shift) (left right : IntegerScalar.Value parameters)
    (result : TypedRaw Extension) (evaluated : TypedShiftEvaluation parameters policy operation left right result) :
    shiftRaw parameters policy operation left right = result := by
  cases evaluated with
  | promoted first second result leftPromotion rightPromotion evaluation =>
      unfold shiftRaw
      dsimp only
      rw [promote_complete parameters left first leftPromotion, promote_complete parameters right second rightPromotion,
        shiftValue_complete _ policy operation _ _ result evaluation]

theorem TypedShiftEvaluation.value_range {Extension : Type u} {parameters : IntegerTypeParameters Extension}
    {policy : RightShiftPolicy} {operation : Shift} {left right : IntegerScalar.Value parameters}
    {type : IntegerType Extension} {result : Int} {negativeZero : Bool}
    (evaluated : TypedShiftEvaluation parameters policy operation left right ⟨type, .value result negativeZero⟩) :
    (type.format parameters).Represents result := by
  cases evaluated with
  | promoted first _ _ _ _ evaluation => exact evaluation.value_range

def bitwiseRaw {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : NegativeZeroPolicy) (operation : Bitwise)
    (left right : IntegerScalar.Value parameters) : TypedRaw Extension :=
  let prepared := prepareIntegerOperands parameters left.type right.type left.integer right.integer
  let format := prepared.target.format parameters
  ⟨prepared.target, bitwiseWord format policy operation (canonicalRepresentation format prepared.left)
    (canonicalRepresentation format prepared.right)⟩

inductive TypedBitwiseEvaluation {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (conversionPolicy : SignedConversionPolicy) (policy : NegativeZeroPolicy) (operation : Bitwise)
    (left right : IntegerScalar.Value parameters) : TypedRaw Extension → Prop where
  | converted (prepared : PreparedIntegerOperands parameters) (result : RawResult)
      (conversions : IntegerOperandsPrepared parameters conversionPolicy left.type right.type left.integer right.integer prepared)
      (evaluation : BitwiseEvaluation (prepared.target.format parameters) policy operation
        (canonicalRepresentation _ prepared.left) (canonicalRepresentation _ prepared.right) result) :
      TypedBitwiseEvaluation parameters conversionPolicy policy operation left right ⟨prepared.target, result⟩

theorem bitwiseRaw_sound {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (conversionPolicy : SignedConversionPolicy) (policy : NegativeZeroPolicy) (operation : Bitwise)
    (left right : IntegerScalar.Value parameters) :
    TypedBitwiseEvaluation parameters conversionPolicy policy operation left right (bitwiseRaw parameters policy operation left right) :=
  .converted _ _ (prepareIntegerOperands_sound parameters conversionPolicy left.type right.type left.integer right.integer)
    (bitwiseWord_sound _ policy operation _ _)

theorem bitwiseRaw_complete {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (conversionPolicy : SignedConversionPolicy) (policy : NegativeZeroPolicy) (operation : Bitwise)
    (left right : IntegerScalar.Value parameters) (result : TypedRaw Extension)
    (evaluated : TypedBitwiseEvaluation parameters conversionPolicy policy operation left right result) :
    bitwiseRaw parameters policy operation left right = result := by
  cases evaluated with
  | converted prepared result conversions evaluation =>
      unfold bitwiseRaw
      dsimp only
      rw [prepareIntegerOperands_complete parameters conversionPolicy left.type right.type left.integer right.integer prepared conversions]
      rw [bitwiseWord_complete _ policy operation _ _ result evaluation]

theorem TypedBitwiseEvaluation.value_range {Extension : Type u} {parameters : IntegerTypeParameters Extension}
    {conversionPolicy : SignedConversionPolicy} {policy : NegativeZeroPolicy} {operation : Bitwise}
    {left right : IntegerScalar.Value parameters} {type : IntegerType Extension} {result : Int} {negativeZero : Bool}
    (evaluated : TypedBitwiseEvaluation parameters conversionPolicy policy operation left right ⟨type, .value result negativeZero⟩) :
    (type.format parameters).Represents result := by
  cases evaluated with
  | converted _ _ _ evaluation => cases evaluation; exact WordReading.value_range (by assumption)

def comparison {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (operation : Comparison) (left right : IntegerScalar.Value parameters) : IntegerScalar.Value parameters :=
  let prepared := prepareIntegerOperands parameters left.type right.type left.integer right.integer
  IntegerScalar.logicalValue parameters (compareValue operation prepared.left.value prepared.right.value)

inductive TypedComparisonEvaluation {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (conversionPolicy : SignedConversionPolicy) (operation : Comparison) (left right : IntegerScalar.Value parameters) :
    IntegerScalar.Value parameters → Prop where
  | converted (prepared : PreparedIntegerOperands parameters) (truth : Bool)
      (conversions : IntegerOperandsPrepared parameters conversionPolicy left.type right.type left.integer right.integer prepared)
      (evaluation : ComparisonEvaluation operation prepared.left.value prepared.right.value truth) :
      TypedComparisonEvaluation parameters conversionPolicy operation left right (IntegerScalar.logicalValue parameters truth)

theorem comparison_sound {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (conversionPolicy : SignedConversionPolicy) (operation : Comparison) (left right : IntegerScalar.Value parameters) :
    TypedComparisonEvaluation parameters conversionPolicy operation left right (comparison parameters operation left right) :=
  .converted _ _ (prepareIntegerOperands_sound parameters conversionPolicy left.type right.type left.integer right.integer)
    (compareValue_sound operation _ _)

theorem comparison_complete {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (conversionPolicy : SignedConversionPolicy) (operation : Comparison) (left right : IntegerScalar.Value parameters)
    (result : IntegerScalar.Value parameters)
    (evaluated : TypedComparisonEvaluation parameters conversionPolicy operation left right result) :
    comparison parameters operation left right = result := by
  cases evaluated with
  | converted prepared truth conversions evaluation =>
      unfold comparison
      dsimp only
      rw [prepareIntegerOperands_complete parameters conversionPolicy left.type right.type left.integer right.integer prepared conversions]
      rw [compareValue_complete operation _ _ truth evaluation]

theorem comparison_type {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (operation : Comparison) (left right : IntegerScalar.Value parameters) :
    (comparison parameters operation left right).type = .int := rfl

theorem comparison_zero_or_one {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (operation : Comparison) (left right : IntegerScalar.Value parameters) :
    (comparison parameters operation left right).integer.value = 0 ∨
      (comparison parameters operation left right).integer.value = 1 := by
  unfold comparison
  dsimp only
  rw [IntegerScalar.logicalValue_integer]
  split <;> simp

inductive Result {Extension : Type u} (parameters : IntegerTypeParameters Extension) where
  | value (scalar : IntegerScalar.Value parameters) (negativeZero : Bool)
  | undefined (type : IntegerType Extension) (reason : Fault)
  deriving DecidableEq, Repr

def Result.raw {Extension : Type u} {parameters : IntegerTypeParameters Extension} :
    Result parameters → TypedRaw Extension
  | .value scalar negativeZero => ⟨scalar.type, .value scalar.integer.value negativeZero⟩
  | .undefined type reason => ⟨type, .undefined reason⟩

theorem Result.raw_injective {Extension : Type u} (parameters : IntegerTypeParameters Extension) :
    Function.Injective (@Result.raw Extension parameters) := by
  intro first second same
  cases first with
  | value first flag =>
      cases second with
      | value second otherFlag =>
          have type := congrArg TypedRaw.type same
          have value := RawResult.value.inj (congrArg TypedRaw.result same)
          cases value.2
          exact congrArg (fun scalar => Result.value scalar flag)
            (IntegerScalar.Value.ext first second type value.1)
      | undefined type reason => cases congrArg TypedRaw.result same
  | undefined type reason =>
      cases second with
      | value scalar flag => cases congrArg TypedRaw.result same
      | undefined otherType otherReason =>
          have typeSame := congrArg TypedRaw.type same
          have reasonSame := RawResult.undefined.inj (congrArg TypedRaw.result same)
          cases typeSame
          cases reasonSame
          rfl

def TypedRaw.Valid {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (result : TypedRaw Extension) : Prop :=
  ∀ integer negativeZero, result.result = .value integer negativeZero →
    (result.type.format parameters).Represents integer

def pack {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (result : TypedRaw Extension) (valid : result.Valid parameters) : Result parameters :=
  match computed : result.result with
  | .value integer negativeZero => .value ⟨result.type, ⟨integer, valid integer negativeZero computed⟩⟩ negativeZero
  | .undefined reason => .undefined result.type reason

theorem pack_raw {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (result : TypedRaw Extension) (valid : result.Valid parameters) : (pack parameters result valid).raw = result := by
  cases result with
  | mk type value => cases value <;> rfl

theorem unaryRaw_valid {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : NegativeZeroPolicy) (operation : Unary) (input : IntegerScalar.Value parameters) :
    (unaryRaw parameters policy operation input).Valid parameters := by
  intro integer negativeZero same
  have evaluated := unaryRaw_sound parameters policy operation input
  generalize unaryRaw parameters policy operation input = outcome at *
  cases outcome with
  | mk type result => cases same; exact evaluated.value_range

theorem shiftRaw_valid {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : RightShiftPolicy) (operation : Shift) (left right : IntegerScalar.Value parameters) :
    (shiftRaw parameters policy operation left right).Valid parameters := by
  intro integer negativeZero same
  have evaluated := shiftRaw_sound parameters policy operation left right
  generalize shiftRaw parameters policy operation left right = outcome at *
  cases outcome with
  | mk type result => cases same; exact evaluated.value_range

theorem bitwiseRaw_valid {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : NegativeZeroPolicy) (operation : Bitwise) (left right : IntegerScalar.Value parameters) :
    (bitwiseRaw parameters policy operation left right).Valid parameters := by
  intro integer negativeZero same
  have evaluated := bitwiseRaw_sound parameters intervalReductionPolicy policy operation left right
  generalize bitwiseRaw parameters policy operation left right = outcome at *
  cases outcome with
  | mk type result => cases same; exact evaluated.value_range

def unary {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : NegativeZeroPolicy) (operation : Unary) (input : IntegerScalar.Value parameters) : Result parameters :=
  pack parameters (unaryRaw parameters policy operation input) (unaryRaw_valid parameters policy operation input)

def shift {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : RightShiftPolicy) (operation : Shift) (left right : IntegerScalar.Value parameters) : Result parameters :=
  pack parameters (shiftRaw parameters policy operation left right) (shiftRaw_valid parameters policy operation left right)

def bitwise {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : NegativeZeroPolicy) (operation : Bitwise) (left right : IntegerScalar.Value parameters) : Result parameters :=
  pack parameters (bitwiseRaw parameters policy operation left right) (bitwiseRaw_valid parameters policy operation left right)

theorem unary_iff {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : NegativeZeroPolicy) (operation : Unary) (input : IntegerScalar.Value parameters) (result : Result parameters) :
    unary parameters policy operation input = result ↔ TypedUnaryEvaluation parameters policy operation input result.raw := by
  constructor
  · intro same
    have raw := pack_raw parameters (unaryRaw parameters policy operation input) (unaryRaw_valid parameters policy operation input)
    change (unary parameters policy operation input).raw = _ at raw
    rw [same] at raw
    rw [raw]
    exact unaryRaw_sound parameters policy operation input
  · intro evaluated
    apply Result.raw_injective parameters
    exact (pack_raw parameters _ _).trans (unaryRaw_complete parameters policy operation input result.raw evaluated)

theorem shift_iff {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (policy : RightShiftPolicy) (operation : Shift) (left right : IntegerScalar.Value parameters) (result : Result parameters) :
    shift parameters policy operation left right = result ↔
      TypedShiftEvaluation parameters policy operation left right result.raw := by
  constructor
  · intro same
    have raw := pack_raw parameters (shiftRaw parameters policy operation left right) (shiftRaw_valid parameters policy operation left right)
    change (shift parameters policy operation left right).raw = _ at raw
    rw [same] at raw
    rw [raw]
    exact shiftRaw_sound parameters policy operation left right
  · intro evaluated
    apply Result.raw_injective parameters
    exact (pack_raw parameters _ _).trans (shiftRaw_complete parameters policy operation left right result.raw evaluated)

theorem bitwise_iff {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (conversionPolicy : SignedConversionPolicy) (policy : NegativeZeroPolicy) (operation : Bitwise)
    (left right : IntegerScalar.Value parameters) (result : Result parameters) :
    bitwise parameters policy operation left right = result ↔
      TypedBitwiseEvaluation parameters conversionPolicy policy operation left right result.raw := by
  constructor
  · intro same
    have raw := pack_raw parameters (bitwiseRaw parameters policy operation left right) (bitwiseRaw_valid parameters policy operation left right)
    change (bitwise parameters policy operation left right).raw = _ at raw
    rw [same] at raw
    rw [raw]
    exact bitwiseRaw_sound parameters conversionPolicy policy operation left right
  · intro evaluated
    apply Result.raw_injective parameters
    exact (pack_raw parameters _ _).trans (bitwiseRaw_complete parameters conversionPolicy policy operation left right result.raw evaluated)

theorem comparison_iff {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (conversionPolicy : SignedConversionPolicy) (operation : Comparison) (left right : IntegerScalar.Value parameters)
    (result : IntegerScalar.Value parameters) : comparison parameters operation left right = result ↔
      TypedComparisonEvaluation parameters conversionPolicy operation left right result := by
  constructor
  · rintro rfl
    exact comparison_sound parameters conversionPolicy operation left right
  · exact comparison_complete parameters conversionPolicy operation left right result

end Mettapedia.Languages.C11.IntegerOperators
