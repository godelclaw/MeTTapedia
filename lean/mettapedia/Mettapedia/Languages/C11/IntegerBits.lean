import Mettapedia.Languages.C11.BytePacking
import Mettapedia.Languages.C11.IntegerConversion

/-!
# C11 integer value-bit and sign-bit interpretation

The executable reader distinguishes an invalid finite-word encoding from a
valid-width trap representation. All three signed representations are
retained. Negative zero has a named normal/trap policy and remains distinct
from positive zero in representation observations. Two's-complement minimum
uses the minimum policy of the integer format.

The independent reading rules use value bits and their sign-bit weights;
the executable reader inspects a finite word. Correspondence is proved for
every precision and word. Physical bit positions, padding traps, byte order,
effective types and rules that generate/store negative zero belong to the
object profile. A mathematical zero does not authorize every negative-zero
operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerBits

inductive NegativeZero where
  | normal
  | trap
  deriving DecidableEq, Repr

inductive Trap where
  | negativeZero
  | minimum
  deriving DecidableEq, Repr

inductive Outcome where
  | value (integer : Int) (negativeZero : Bool)
  | trap (reason : Trap)
  deriving DecidableEq, Repr

def zeroOutcome : NegativeZero → Outcome
  | .normal => .value 0 true
  | .trap => .trap .negativeZero

def precision : IntegerFormat → Nat
  | .unsigned bits _ | .signed bits _ _ => bits

def width : IntegerFormat → Nat
  | .unsigned bits _ => bits
  | .signed bits _ _ => bits + 1

def capacity (format : IntegerFormat) : Nat := 2 ^ precision format

theorem capacity_positive (format : IntegerFormat) : 0 < capacity format := Nat.two_pow_pos _

def readSigned (mode : NegativeZero) (representation : SignedRepresentation)
    (maximum word : Nat) : Outcome :=
  if word < maximum then .value word false
  else match representation with
    | .signMagnitude =>
        if word = maximum then zeroOutcome mode
        else .value ((maximum : Int) - word) false
    | .onesComplement =>
        if word + 1 = 2 * maximum then zeroOutcome mode
        else .value ((word : Int) - (2 * maximum - 1 : Int)) false
    | .twosComplement minimumIsNormal =>
        if minimumIsNormal = false ∧ word = maximum then .trap .minimum
        else .value ((word : Int) - 2 * maximum) false

def read (format : IntegerFormat) (mode : NegativeZero) (word : Nat) : Option Outcome :=
  if word < 2 ^ width format then
    some (match format with
      | .unsigned _ _ => .value word false
      | .signed _ _ representation => readSigned mode representation (capacity format) word)
  else none

inductive ZeroReading : NegativeZero → Outcome → Prop where
  | normal : ZeroReading .normal (.value 0 true)
  | trap : ZeroReading .trap (.trap .negativeZero)

theorem zeroOutcome_reading (mode : NegativeZero) : ZeroReading mode (zeroOutcome mode) := by
  cases mode with
  | normal => exact .normal
  | trap => exact .trap

theorem zeroReading_outcome (mode : NegativeZero) (outcome : Outcome)
    (reading : ZeroReading mode outcome) : zeroOutcome mode = outcome := by
  cases reading <;> rfl

inductive Reading : IntegerFormat → NegativeZero → Nat → Outcome → Prop where
  | unsigned (bits : Nat) (positive : 0 < bits) (mode : NegativeZero) (valueBits : Nat)
      (bounded : valueBits < 2 ^ bits) :
      Reading (.unsigned bits positive) mode valueBits (.value valueBits false)
  | positive (bits : Nat) (positive : 0 < bits) (representation : SignedRepresentation)
      (mode : NegativeZero) (valueBits : Nat) (bounded : valueBits < 2 ^ bits) :
      Reading (.signed bits positive representation) mode valueBits (.value valueBits false)
  | signMagnitude (bits : Nat) (positive : 0 < bits) (mode : NegativeZero) (valueBits : Nat)
      (nonzero : 0 < valueBits) (bounded : valueBits < 2 ^ bits) :
      Reading (.signed bits positive .signMagnitude) mode (2 ^ bits + valueBits) (.value (-(valueBits : Int)) false)
  | signMagnitudeZero (bits : Nat) (positive : 0 < bits) (mode : NegativeZero)
      (outcome : Outcome) (zero : ZeroReading mode outcome) :
      Reading (.signed bits positive .signMagnitude) mode (2 ^ bits) outcome
  | onesComplement (bits : Nat) (positive : 0 < bits) (mode : NegativeZero) (valueBits : Nat)
      (bounded : valueBits + 1 < 2 ^ bits) :
      Reading (.signed bits positive .onesComplement) mode (2 ^ bits + valueBits)
        (.value ((valueBits : Int) - (2 ^ bits - 1 : Int)) false)
  | onesComplementZero (bits : Nat) (positive : 0 < bits) (mode : NegativeZero)
      (outcome : Outcome) (zero : ZeroReading mode outcome) :
      Reading (.signed bits positive .onesComplement) mode (2 ^ bits + (2 ^ bits - 1)) outcome
  | twosComplement (bits : Nat) (positive : 0 < bits) (mode : NegativeZero) (normal : Bool)
      (valueBits : Nat) (bounded : valueBits < 2 ^ bits) (permitted : normal = true ∨ valueBits ≠ 0) :
      Reading (.signed bits positive (.twosComplement normal)) mode (2 ^ bits + valueBits)
        (.value ((valueBits : Int) - 2 ^ bits) false)
  | minimumTrap (bits : Nat) (positive : 0 < bits) (mode : NegativeZero) :
      Reading (.signed bits positive (.twosComplement false)) mode (2 ^ bits) (.trap .minimum)

theorem read_sound (format : IntegerFormat) (mode : NegativeZero) (word : Nat) (outcome : Outcome)
    (computed : read format mode word = some outcome) : Reading format mode word outcome := by
  cases format with
  | unsigned bits positive =>
      by_cases bounded : word < 2 ^ bits
      · simp only [read, width, bounded, ↓reduceIte, Option.some.injEq] at computed
        subst outcome
        exact .unsigned bits positive mode word bounded
      · simp [read, width, bounded] at computed
  | signed bits positive representation =>
      let maximum := 2 ^ bits
      have maximumPositive : 0 < maximum := Nat.two_pow_pos _
      have maximumCast : (maximum : Int) = (2 ^ bits : Int) := by simp [maximum]
      by_cases bounded : word < 2 * maximum
      · have fullBound : word < 2 ^ (bits + 1) := by simpa [maximum, pow_succ, Nat.mul_comm] using bounded
        simp only [read, width, fullBound, ↓reduceIte, capacity, precision, Option.some.injEq] at computed
        change readSigned mode representation maximum word = outcome at computed
        by_cases low : word < maximum
        · have value : outcome = .value word false := by
            rw [← computed]
            simp [readSigned, low, maximum]
          rw [value]
          exact .positive bits positive representation mode word low
        · have valueBound : word - maximum < maximum := by omega
          have splitWord : maximum + (word - maximum) = word := by omega
          change 2 ^ bits + (word - maximum) = word at splitWord
          cases representation with
          | signMagnitude =>
              by_cases zero : word = maximum
              · have value : outcome = zeroOutcome mode := by rw [← computed]; simp [readSigned, zero, maximum]
                rw [value]
                simpa only [zero] using Reading.signMagnitudeZero bits positive mode (zeroOutcome mode) (zeroOutcome_reading mode)
              · have nonzero : 0 < word - maximum := by omega
                have value : outcome = .value (-((word - maximum : Nat) : Int)) false := by
                  rw [← computed]
                  simp only [readSigned, low, ↓reduceIte, zero]
                  congr 1
                  omega
                rw [value]
                simpa only [splitWord] using Reading.signMagnitude bits positive mode (word - maximum) nonzero valueBound
          | onesComplement =>
              by_cases zero : word + 1 = 2 * maximum
              · have value : outcome = zeroOutcome mode := by rw [← computed]; simp [readSigned, low, zero, maximum]
                rw [value]
                have position : word = 2 ^ bits + (2 ^ bits - 1) := by change word = maximum + (maximum - 1); omega
                rw [position]
                exact .onesComplementZero bits positive mode (zeroOutcome mode) (zeroOutcome_reading mode)
              · have bitsBound : word - maximum + 1 < 2 ^ bits := by change word - maximum + 1 < maximum; omega
                have value : outcome = .value ((word - maximum : Nat) - (2 ^ bits - 1 : Int)) false := by
                  rw [← computed]
                  simp only [readSigned, low, ↓reduceIte, zero]
                  congr 1
                  change (word : Int) - (2 * maximum - 1 : Int) = (word - maximum : Nat) - (maximum - 1 : Int)
                  omega
                rw [value]
                simpa only [splitWord] using Reading.onesComplement bits positive mode (word - maximum) bitsBound
          | twosComplement normal =>
              by_cases trap : normal = false ∧ word = maximum
              · have value : outcome = .trap .minimum := by rw [← computed]; simp [readSigned, trap, maximum]
                rw [value]
                rcases trap with ⟨rfl, rfl⟩
                exact .minimumTrap bits positive mode
              · have permitted : normal = true ∨ word - maximum ≠ 0 := by
                  cases normal <;> simp_all
                  omega
                have value : outcome = .value ((word - maximum : Nat) - (2 ^ bits : Int)) false := by
                  rw [← computed]
                  simp only [readSigned, low, ↓reduceIte, trap]
                  congr 1
                  change (word : Int) - 2 * maximum = (word - maximum : Nat) - (maximum : Int)
                  omega
                rw [value]
                simpa only [splitWord] using Reading.twosComplement bits positive mode normal (word - maximum) valueBound permitted
      · have fullBound : ¬ word < 2 ^ (bits + 1) := by simpa [maximum, pow_succ, Nat.mul_comm] using bounded
        simp [read, width, fullBound] at computed

theorem read_complete (format : IntegerFormat) (mode : NegativeZero) (word : Nat) (outcome : Outcome)
    (reading : Reading format mode word outcome) : read format mode word = some outcome := by
  cases reading with
  | unsigned bits positive mode valueBits bounded => simp [read, width, bounded]
  | positive bits positive representation _ _ bounded =>
      have fullBound : word < 2 ^ (bits + 1) := by rw [pow_succ]; omega
      simp [read, width, fullBound, readSigned, capacity, precision, bounded]
  | signMagnitude bits positive mode valueBits nonzero bounded =>
      have fullBound : 2 ^ bits + valueBits < 2 ^ (bits + 1) := by rw [pow_succ]; omega
      have low : ¬ 2 ^ bits + valueBits < 2 ^ bits := by omega
      have zero : 2 ^ bits + valueBits ≠ 2 ^ bits := by omega
      simp only [read, width, fullBound, ↓reduceIte, capacity, precision, readSigned, low, zero]
      congr 2
      simp
  | signMagnitudeZero bits positive mode outcome zero =>
      have fullBound : 2 ^ bits < 2 ^ (bits + 1) := by rw [pow_succ]; have h := Nat.two_pow_pos bits; omega
      simp [read, width, fullBound, readSigned, capacity, precision, zeroReading_outcome mode outcome zero]
  | onesComplement bits positive mode valueBits bounded =>
      have fullBound : 2 ^ bits + valueBits < 2 ^ (bits + 1) := by rw [pow_succ]; omega
      have low : ¬ 2 ^ bits + valueBits < 2 ^ bits := by omega
      have zero : 2 ^ bits + valueBits + 1 ≠ 2 * 2 ^ bits := by omega
      simp only [read, width, fullBound, ↓reduceIte, capacity, precision, readSigned, low, zero]
      congr 2
      simp only [Int.natCast_add]
      have powerCast : ((2 ^ bits : Nat) : Int) = (2 ^ bits : Int) := by simp
      omega
  | onesComplementZero bits positive mode outcome zero =>
      have maximumPositive := Nat.two_pow_pos bits
      have fullBound : 2 ^ bits + (2 ^ bits - 1) < 2 ^ (bits + 1) := by rw [pow_succ]; omega
      have low : ¬ 2 ^ bits + (2 ^ bits - 1) < 2 ^ bits := by omega
      have last : 2 ^ bits + (2 ^ bits - 1) + 1 = 2 * 2 ^ bits := by omega
      simp [read, width, fullBound, readSigned, capacity, precision, low, last, zeroReading_outcome mode outcome zero]
  | twosComplement bits positive mode normal valueBits bounded permitted =>
      have fullBound : 2 ^ bits + valueBits < 2 ^ (bits + 1) := by rw [pow_succ]; omega
      have low : ¬ 2 ^ bits + valueBits < 2 ^ bits := by omega
      have noTrap : ¬ (normal = false ∧ 2 ^ bits + valueBits = 2 ^ bits) := by
        rcases permitted with normal | nonzero
        · simp [normal]
        · intro both; exact nonzero (by omega)
      simp only [read, width, fullBound, ↓reduceIte, capacity, precision, readSigned, low, noTrap]
      congr 2
      simp only [Int.natCast_add]
      have powerCast : ((2 ^ bits : Nat) : Int) = (2 ^ bits : Int) := by simp
      omega
  | minimumTrap bits positive mode =>
      have fullBound : 2 ^ bits < 2 ^ (bits + 1) := by rw [pow_succ]; have h := Nat.two_pow_pos bits; omega
      simp [read, width, fullBound, readSigned, capacity, precision]

theorem read_iff (format : IntegerFormat) (mode : NegativeZero) (word : Nat) (outcome : Outcome) :
    read format mode word = some outcome ↔ Reading format mode word outcome :=
  ⟨read_sound format mode word outcome, read_complete format mode word outcome⟩

theorem Reading.value_in_range (format : IntegerFormat) (mode : NegativeZero) (word : Nat)
    (outcome : Outcome) (reading : Reading format mode word outcome) :
    ∀ integer negativeZero, outcome = .value integer negativeZero → format.Represents integer := by
  cases reading with
  | unsigned bits positive _ _ bounded =>
      intro integer negativeZero equal
      cases equal
      have powerCast : ((2 ^ bits : Nat) : Int) = (2 ^ bits : Int) := by simp
      simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper, powerOfTwo]
      omega
  | positive bits positive representation _ _ bounded =>
      intro integer negativeZero equal
      cases equal
      have powerCast : ((2 ^ bits : Nat) : Int) = (2 ^ bits : Int) := by simp
      have positivePower := Nat.two_pow_pos bits
      cases representation with
      | signMagnitude | onesComplement =>
          simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper, powerOfTwo]
          omega
      | twosComplement normal =>
          cases normal <;>
            simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper, powerOfTwo] <;> omega
  | signMagnitude bits positive _ valueBits nonzero bounded =>
      intro integer negativeZero equal
      cases equal
      have powerCast : ((2 ^ bits : Nat) : Int) = (2 ^ bits : Int) := by simp
      simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper, powerOfTwo]
      omega
  | signMagnitudeZero bits positive _ outcome zero =>
      intro integer negativeZero equal
      cases zero with
      | normal => cases equal; exact IntegerFormat.zero_representable _
      | trap => cases equal
  | onesComplement bits positive _ valueBits bounded =>
      intro integer negativeZero equal
      cases equal
      have powerCast : ((2 ^ bits : Nat) : Int) = (2 ^ bits : Int) := by simp
      simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper, powerOfTwo]
      omega
  | onesComplementZero bits positive _ outcome zero =>
      intro integer negativeZero equal
      cases zero with
      | normal => cases equal; exact IntegerFormat.zero_representable _
      | trap => cases equal
  | twosComplement bits positive _ normal valueBits bounded permitted =>
      intro integer negativeZero equal
      cases equal
      have powerCast : ((2 ^ bits : Nat) : Int) = (2 ^ bits : Int) := by simp
      cases normal with
      | true =>
          simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper, powerOfTwo]
          omega
      | false =>
          have nonzero : valueBits ≠ 0 := by simpa using permitted
          simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper, powerOfTwo]
          omega
  | minimumTrap bits positive mode => intro integer negativeZero equal; cases equal

theorem read_value_in_range (format : IntegerFormat) (mode : NegativeZero) (word : Nat)
    (integer : Int) (negativeZero : Bool) (computed : read format mode word = some (.value integer negativeZero)) :
    format.Represents integer :=
  Reading.value_in_range format mode word _ (read_sound format mode word _ computed) integer negativeZero rfl

theorem read_defined_bound (format : IntegerFormat) (mode : NegativeZero) (word : Nat)
    (outcome : Outcome) (computed : read format mode word = some outcome) : word < 2 ^ width format := by
  by_cases bounded : word < 2 ^ width format
  · exact bounded
  · simp [read, bounded] at computed

/-- A constructed ordinary store representation. Zero is stored as positive
zero; padding and optional negative-zero stores are handled by the object
layer. This is not an out-of-range value conversion. -/
def canonicalWord (format : IntegerFormat) (integer : Int) : Nat := match format with
  | .unsigned _ _ => integer.toNat
  | .signed bits _ representation =>
      if 0 ≤ integer then integer.toNat
      else match representation with
        | .signMagnitude => (powerOfTwo bits - integer).toNat
        | .onesComplement => (2 * powerOfTwo bits - 1 + integer).toNat
        | .twosComplement _ => (2 * powerOfTwo bits + integer).toNat

theorem canonicalWord_reading (format : IntegerFormat) (mode : NegativeZero) (integer : Int)
    (valid : format.Represents integer) : Reading format mode (canonicalWord format integer) (.value integer false) := by
  cases format with
  | unsigned bits positive =>
      simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper] at valid
      have powerCast : ((2 ^ bits : Nat) : Int) = powerOfTwo bits := by simp [powerOfTwo]
      have back : (integer.toNat : Int) = integer := Int.toNat_of_nonneg valid.1
      have bounded : integer.toNat < 2 ^ bits := by omega
      simpa only [canonicalWord, back] using Reading.unsigned bits positive mode integer.toNat bounded
  | signed bits positive representation =>
      let maximum := 2 ^ bits
      have maximumCast : (maximum : Int) = powerOfTwo bits := by simp [maximum, powerOfTwo]
      have maximumPositive : 0 < maximum := Nat.two_pow_pos _
      have upper : integer < (maximum : Int) := by
        have bound := valid.2
        simp only [IntegerFormat.upper] at bound
        omega
      by_cases nonnegative : 0 ≤ integer
      · have back : (integer.toNat : Int) = integer := Int.toNat_of_nonneg nonnegative
        have bounded : integer.toNat < 2 ^ bits := by change integer.toNat < maximum; omega
        simpa only [canonicalWord, nonnegative, ↓reduceIte, back] using
          Reading.positive bits positive representation mode integer.toNat bounded
      · have negative : integer < 0 := by omega
        cases representation with
        | signMagnitude =>
            have lower := valid.1
            simp only [IntegerFormat.lower] at lower
            let valueBits := (-integer).toNat
            have bitsCast : (valueBits : Int) = -integer := Int.toNat_of_nonneg (by omega)
            have nonzero : 0 < valueBits := by omega
            have bounded : valueBits < 2 ^ bits := by change valueBits < maximum; omega
            have wordNonnegative : 0 ≤ powerOfTwo bits - integer := by omega
            have wordCast := Int.toNat_of_nonneg wordNonnegative
            have position : (powerOfTwo bits - integer).toNat = 2 ^ bits + valueBits := by
              change (powerOfTwo bits - integer).toNat = maximum + valueBits
              omega
            simpa only [canonicalWord, nonnegative, ↓reduceIte, position, bitsCast, neg_neg] using
              Reading.signMagnitude bits positive mode valueBits nonzero bounded
        | onesComplement =>
            have lower := valid.1
            simp only [IntegerFormat.lower] at lower
            let valueBits := (powerOfTwo bits - 1 + integer).toNat
            have bitsNonnegative : 0 ≤ powerOfTwo bits - 1 + integer := by omega
            have bitsCast : (valueBits : Int) = powerOfTwo bits - 1 + integer := Int.toNat_of_nonneg bitsNonnegative
            have bounded : valueBits + 1 < 2 ^ bits := by change valueBits + 1 < maximum; omega
            have wordNonnegative : 0 ≤ 2 * powerOfTwo bits - 1 + integer := by omega
            have wordCast := Int.toNat_of_nonneg wordNonnegative
            have position : (2 * powerOfTwo bits - 1 + integer).toNat = 2 ^ bits + valueBits := by
              change (2 * powerOfTwo bits - 1 + integer).toNat = maximum + valueBits
              omega
            have represented := Reading.onesComplement bits positive mode valueBits bounded
            have value : (valueBits : Int) - (2 ^ bits - 1 : Int) = integer := by
              simp only [powerOfTwo] at bitsCast
              omega
            simpa only [canonicalWord, nonnegative, ↓reduceIte, position, value] using represented
        | twosComplement normal =>
            have lower := valid.1
            have bitsNonnegative : 0 ≤ powerOfTwo bits + integer := by
              cases normal <;> simp only [IntegerFormat.lower] at lower <;> omega
            let valueBits := (powerOfTwo bits + integer).toNat
            have bitsCast : (valueBits : Int) = powerOfTwo bits + integer := Int.toNat_of_nonneg bitsNonnegative
            have bounded : valueBits < 2 ^ bits := by change valueBits < maximum; omega
            have permitted : normal = true ∨ valueBits ≠ 0 := by
              cases normal with
              | true => exact Or.inl rfl
              | false =>
                  simp only [IntegerFormat.lower] at lower
                  exact Or.inr (by omega)
            have wordNonnegative : 0 ≤ 2 * powerOfTwo bits + integer := by omega
            have wordCast := Int.toNat_of_nonneg wordNonnegative
            have position : (2 * powerOfTwo bits + integer).toNat = 2 ^ bits + valueBits := by
              change (2 * powerOfTwo bits + integer).toNat = maximum + valueBits
              omega
            have represented := Reading.twosComplement bits positive mode normal valueBits bounded permitted
            have value : (valueBits : Int) - (2 ^ bits : Int) = integer := by
              simp only [powerOfTwo] at bitsCast
              omega
            simpa only [canonicalWord, nonnegative, ↓reduceIte, position, value] using represented

theorem read_canonicalWord (format : IntegerFormat) (mode : NegativeZero) (integer : Int)
    (valid : format.Represents integer) : read format mode (canonicalWord format integer) = some (.value integer false) :=
  read_complete format mode _ _ (canonicalWord_reading format mode integer valid)

theorem canonicalWord_bound (format : IntegerFormat) (integer : Int) (valid : format.Represents integer) :
    canonicalWord format integer < 2 ^ width format :=
  read_defined_bound format .normal _ _ (read_canonicalWord format .normal integer valid)

end Mettapedia.Languages.C11.IntegerBits
