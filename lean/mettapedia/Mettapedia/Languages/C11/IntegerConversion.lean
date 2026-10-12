import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# C11 integer value conversions

N1570 6.3.1.2 and 6.3.1.3 specify conversions on mathematical values.
Unsigned conversion adds or subtracts multiples of the target modulus until
the result is in range. Signed out-of-range conversion uses a declared
implementation policy: a representable value or an implementation-defined
signal. It is not identified with signed arithmetic overflow.

The signed precision counts value bits, excluding the sign and padding bits.
All three C11 signed representations are retained, including the choice of a
normal or trap minimum encoding for two's complement. Negative zero, padding,
trap representations, integer ranks and native byte layout belong to the
object and type profiles; they are not collapsed into this value conversion.
The declarative conversion relation uses ranges and integer multiples. The
executable converter uses Euclidean remainder, with both directions proved.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11

inductive SignedRepresentation where
  | signMagnitude
  | onesComplement
  | twosComplement (minimumIsNormal : Bool)
  deriving DecidableEq, Repr

inductive IntegerFormat where
  | unsigned (precision : Nat) (positive : 0 < precision)
  | signed (precision : Nat) (positive : 0 < precision)
      (representation : SignedRepresentation)
  deriving DecidableEq, Repr

def powerOfTwo (precision : Nat) : Int := 2 ^ precision

theorem powerOfTwo_positive (precision : Nat) : 0 < powerOfTwo precision := by
  exact pow_pos (by decide) precision

def IntegerFormat.lower : IntegerFormat → Int
  | .unsigned _ _ => 0
  | .signed precision _ (.twosComplement true) => -powerOfTwo precision
  | .signed precision _ (.twosComplement false) => 1 - powerOfTwo precision
  | .signed precision _ .signMagnitude
  | .signed precision _ .onesComplement => 1 - powerOfTwo precision

def IntegerFormat.upper : IntegerFormat → Int
  | .unsigned precision _ | .signed precision _ _ => powerOfTwo precision - 1

def IntegerFormat.Represents (format : IntegerFormat) (value : Int) : Prop :=
  format.lower ≤ value ∧ value ≤ format.upper

instance (format : IntegerFormat) (value : Int) : Decidable (format.Represents value) :=
  inferInstanceAs (Decidable (format.lower ≤ value ∧ value ≤ format.upper))

theorem IntegerFormat.zero_representable (format : IntegerFormat) :
    format.Represents 0 := by
  cases format with
  | unsigned precision positive =>
      have bound := powerOfTwo_positive precision
      simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper]
      omega
  | signed precision positive representation =>
      have bound := powerOfTwo_positive precision
      cases representation with
      | signMagnitude =>
          simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper]
          omega
      | onesComplement =>
          simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper]
          omega
      | twosComplement minimumIsNormal =>
          cases minimumIsNormal <;>
            simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper] <;>
            omega

theorem IntegerFormat.signed_range_balance (precision : Nat) (positive : 0 < precision)
    (representation : SignedRepresentation) :
    let format := IntegerFormat.signed precision positive representation
    format.upper ≤ -format.lower ∧ -format.lower ≤ format.upper + 1 := by
  cases representation with
  | signMagnitude => simp [IntegerFormat.lower, IntegerFormat.upper]
  | onesComplement => simp [IntegerFormat.lower, IntegerFormat.upper]
  | twosComplement minimumIsNormal =>
      cases minimumIsNormal <;> simp [IntegerFormat.lower, IntegerFormat.upper]

def IntegerFormat.span (format : IntegerFormat) : Int := format.upper - format.lower + 1

theorem IntegerFormat.span_positive (format : IntegerFormat) : 0 < format.span := by
  have range := format.zero_representable
  simp only [IntegerFormat.Represents, IntegerFormat.span] at *
  omega

structure IntegerValue (format : IntegerFormat) where
  value : Int
  valid : format.Represents value
  deriving DecidableEq, Repr

inductive ConversionDestination where
  | boolean
  | integer (format : IntegerFormat)
  deriving DecidableEq, Repr

inductive ConversionOutcome where
  | value (value : Int)
  | signal (identifier : Nat)
  deriving DecidableEq, Repr

inductive SignedDisposition (precision : Nat) (positive : 0 < precision)
    (representation : SignedRepresentation) where
  | value (value : Int)
      (valid : (IntegerFormat.signed precision positive representation).Represents value)
  | signal (identifier : Nat)

def SignedDisposition.outcome {precision : Nat} {positive : 0 < precision}
    {representation : SignedRepresentation} :
    SignedDisposition precision positive representation → ConversionOutcome
  | .value integer _ => .value integer
  | .signal identifier => .signal identifier

/-- A named implementation supplies this function. Its value branch carries
the required target range; no correspondence with a native cast is assumed. -/
abbrev SignedConversionPolicy := (precision : Nat) → (positive : 0 < precision) →
  (representation : SignedRepresentation) → Int →
    SignedDisposition precision positive representation

/-- One admissible value policy normalizes into the signed interval. This is
an explicit policy, not a claim about every implementation or representation. -/
def intervalReductionPolicy : SignedConversionPolicy := fun precision positive representation input =>
  let format := IntegerFormat.signed precision positive representation
  .value (format.lower + (input - format.lower) % format.span) (by
    have nonnegative := Int.emod_nonneg (input - format.lower)
      (ne_of_gt format.span_positive)
    have below := Int.emod_lt_of_pos (input - format.lower) format.span_positive
    change format.lower ≤ format.lower + (input - format.lower) % format.span ∧
      format.lower + (input - format.lower) % format.span ≤ format.upper
    have span := format.span_positive
    simp only [IntegerFormat.span] at *
    omega)

def signalingPolicy (identifier : Nat) : SignedConversionPolicy :=
  fun _ _ _ _ => .signal identifier

def convertInteger (policy : SignedConversionPolicy) (input : Int) :
    ConversionDestination → ConversionOutcome
  | .boolean => .value (if input = 0 then 0 else 1)
  | .integer (.unsigned precision _) => .value (input % powerOfTwo precision)
  | .integer (.signed precision positive representation) =>
      let format := IntegerFormat.signed precision positive representation
      if format.Represents input then .value input
      else (policy precision positive representation input).outcome

/-- The clauses state value preservation, bounded repeated modulus adjustment
and the selected signed implementation policy independently of the converter. -/
inductive IntegerConverts (policy : SignedConversionPolicy) :
    Int → ConversionDestination → ConversionOutcome → Prop where
  | booleanZero : IntegerConverts policy 0 .boolean (.value 0)
  | booleanNonzero (input : Int) (nonzero : input ≠ 0) :
      IntegerConverts policy input .boolean (.value 1)
  | unchanged (format : IntegerFormat) (input : Int)
      (representable : format.Represents input) :
      IntegerConverts policy input (.integer format) (.value input)
  | unsignedReduction (precision : Nat) (positive : 0 < precision) (input result : Int)
      (outside : ¬ (IntegerFormat.unsigned precision positive).Represents input)
      (inRange : (IntegerFormat.unsigned precision positive).Represents result)
      (adjusted : ∃ multiple : Int, result = input + multiple * powerOfTwo precision) :
      IntegerConverts policy input (.integer (.unsigned precision positive)) (.value result)
  | signedOutside (precision : Nat) (positive : 0 < precision)
      (representation : SignedRepresentation) (input : Int)
      (outside : ¬ (IntegerFormat.signed precision positive representation).Represents input) :
      IntegerConverts policy input (.integer (.signed precision positive representation))
        (policy precision positive representation input).outcome

theorem unsigned_reduction_in_range (precision : Nat) (positive : 0 < precision) (input : Int) :
    (IntegerFormat.unsigned precision positive).Represents (input % powerOfTwo precision) := by
  have nonnegative := Int.emod_nonneg input (ne_of_gt (powerOfTwo_positive precision))
  have below := Int.emod_lt_of_pos input (powerOfTwo_positive precision)
  simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper]
  omega

theorem unsigned_reduction_adjusts (precision : Nat) (input : Int) :
    ∃ multiple : Int, input % powerOfTwo precision = input + multiple * powerOfTwo precision := by
  refine ⟨-(input / powerOfTwo precision), ?_⟩
  have decomposition := Int.emod_add_mul_ediv input (powerOfTwo precision)
  rw [Int.mul_comm (powerOfTwo precision)] at decomposition
  simp only [neg_mul]
  omega

theorem unsigned_reduction_unique (precision : Nat) (positive : 0 < precision)
    (input result : Int)
    (inRange : (IntegerFormat.unsigned precision positive).Represents result)
    (adjusted : ∃ multiple : Int, result = input + multiple * powerOfTwo precision) :
    input % powerOfTwo precision = result := by
  obtain ⟨multiple, equality⟩ := adjusted
  have congruence : result % powerOfTwo precision = input % powerOfTwo precision := by
    rw [equality]
    simp
  have range : 0 ≤ result ∧ result < powerOfTwo precision := by
    simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper] at inRange
    omega
  rw [Int.emod_eq_of_lt range.1 range.2] at congruence
  exact congruence.symm

theorem convertInteger_preserves_representable (policy : SignedConversionPolicy)
    (format : IntegerFormat) (input : Int) (representable : format.Represents input) :
    convertInteger policy input (.integer format) = .value input := by
  cases format with
  | unsigned precision positive =>
      have range : 0 ≤ input ∧ input < powerOfTwo precision := by
        simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper] at representable
        omega
      simp only [convertInteger, Int.emod_eq_of_lt range.1 range.2]
  | signed precision positive representation =>
      simp only [convertInteger, if_pos representable]

theorem convertInteger_sound (policy : SignedConversionPolicy) (input : Int)
    (destination : ConversionDestination) :
    IntegerConverts policy input destination (convertInteger policy input destination) := by
  cases destination with
  | boolean =>
      by_cases zero : input = 0
      · subst input
        exact IntegerConverts.booleanZero
      · simpa only [convertInteger, if_neg zero] using IntegerConverts.booleanNonzero input zero
  | integer format =>
      by_cases representable : format.Represents input
      · rw [convertInteger_preserves_representable policy format input representable]
        exact IntegerConverts.unchanged format input representable
      · cases format with
        | unsigned precision positive =>
            exact IntegerConverts.unsignedReduction precision positive input
              (input % powerOfTwo precision) representable
              (unsigned_reduction_in_range precision positive input)
              (unsigned_reduction_adjusts precision input)
        | signed precision positive representation =>
            simpa only [convertInteger, if_neg representable] using
              IntegerConverts.signedOutside precision positive representation input representable

theorem convertInteger_complete (policy : SignedConversionPolicy) (input : Int)
    (destination : ConversionDestination) (outcome : ConversionOutcome)
    (converted : IntegerConverts policy input destination outcome) :
    convertInteger policy input destination = outcome := by
  cases converted with
  | booleanZero => rfl
  | booleanNonzero input nonzero => simp only [convertInteger, if_neg nonzero]
  | unchanged format input representable =>
      exact convertInteger_preserves_representable policy format input representable
  | unsignedReduction precision positive input result outside inRange adjusted =>
      simp only [convertInteger, unsigned_reduction_unique precision positive input result inRange adjusted]
  | signedOutside precision positive representation input outside =>
      simp only [convertInteger, if_neg outside]

theorem convertInteger_iff (policy : SignedConversionPolicy) (input : Int)
    (destination : ConversionDestination) (outcome : ConversionOutcome) :
    convertInteger policy input destination = outcome ↔
      IntegerConverts policy input destination outcome := by
  constructor
  · intro equal
    rw [← equal]
    exact convertInteger_sound policy input destination
  · exact convertInteger_complete policy input destination outcome

theorem converted_value_representable (policy : SignedConversionPolicy) (input result : Int)
    (format : IntegerFormat) (converted :
      convertInteger policy input (.integer format) = .value result) :
    format.Represents result := by
  cases format with
  | unsigned precision positive =>
      have equal : input % powerOfTwo precision = result := ConversionOutcome.value.inj converted
      rw [← equal]
      exact unsigned_reduction_in_range precision positive input
  | signed precision positive representation =>
      by_cases inRange : (IntegerFormat.signed precision positive representation).Represents input
      · simp only [convertInteger, if_pos inRange] at converted
        cases converted
        exact inRange
      · simp only [convertInteger, if_neg inRange] at converted
        generalize choice : policy precision positive representation input = disposition at converted
        cases disposition with
        | value value valid => cases converted; exact valid
        | signal identifier => cases converted

end Mettapedia.Languages.C11
