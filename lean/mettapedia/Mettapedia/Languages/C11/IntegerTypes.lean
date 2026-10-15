import Mettapedia.Languages.C11.IntegerConversion

/-!
# C11 integer ranks and promotions

Canonical integer types retain `_Bool`, the five standard signed/unsigned
families, and an explicit family of extensions. A value-parameter profile
supplies precisions, signed representations, distinct family ranks and range
inclusions. These are implementation parameters required by N1570 6.2.5 and
6.3.1.1, rather than correspondence assumptions about an evaluator.

This profile places `_Bool` below the admitted extension families as well as
the standard families. Extensions with another rank policy require a separate
profile. Object width, padding, trap encodings and layout are not determined
by these value parameters. Plain `char`, enum compatibility and width-limited
bit-fields require source-type adapters; they are not silently identified
with canonical integer types here.

Promotion has separate rule clauses and an executable selector. Both
directions, range preservation and agreement with the value converter are
proved for all types and values in a profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11

universe u

inductive StandardIntegerFamily where
  | char
  | short
  | int
  | long
  | longLong
  deriving DecidableEq, Repr

inductive IntegerFamily (Extension : Type u) where
  | standard (family : StandardIntegerFamily)
  | extended (extension : Extension)
  deriving DecidableEq, Repr

inductive IntegerType (Extension : Type u) where
  | boolean
  | signed (family : IntegerFamily Extension)
  | unsigned (family : IntegerFamily Extension)
  deriving DecidableEq, Repr

def ValueRangeIncludes (target source : IntegerFormat) : Prop :=
  target.lower ≤ source.lower ∧ source.upper ≤ target.upper

instance (target source : IntegerFormat) : Decidable (ValueRangeIncludes target source) :=
  inferInstanceAs (Decidable (target.lower ≤ source.lower ∧ source.upper ≤ target.upper))

theorem ValueRangeIncludes.refl (format : IntegerFormat) : ValueRangeIncludes format format :=
  ⟨le_refl _, le_refl _⟩

theorem ValueRangeIncludes.trans {first second third : IntegerFormat}
    (one : ValueRangeIncludes first second) (two : ValueRangeIncludes second third) :
    ValueRangeIncludes first third := ⟨le_trans one.1 two.1, le_trans two.2 one.2⟩

theorem ValueRangeIncludes.represents {target source : IntegerFormat} {value : Int}
    (included : ValueRangeIncludes target source) (valid : source.Represents value) :
    target.Represents value := ⟨le_trans included.1 valid.1, le_trans valid.2 included.2⟩

theorem IntegerFormat.one_representable (format : IntegerFormat) : format.Represents 1 := by
  have zero := format.zero_representable
  cases format with
  | unsigned precision positive =>
      cases precision with
      | zero => omega
      | succ precision =>
          have power := powerOfTwo_positive precision
          simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper,
            powerOfTwo, pow_succ] at *
          omega
  | signed precision positive representation =>
      cases precision with
      | zero => omega
      | succ precision =>
          have power := powerOfTwo_positive precision
          change _ ≤ 1 ∧ 1 ≤ powerOfTwo (precision + 1) - 1
          have lower := zero.1
          simp only [powerOfTwo, pow_succ] at *
          omega

structure IntegerTypeParameters (Extension : Type u) where
  name : String
  signedPrecision : IntegerFamily Extension → Nat
  unsignedPrecision : IntegerFamily Extension → Nat
  signedPositive : ∀ family, 0 < signedPrecision family
  unsignedPositive : ∀ family, 0 < unsignedPrecision family
  representation : IntegerFamily Extension → SignedRepresentation
  rank : IntegerFamily Extension → Nat
  rankPositive : ∀ family, 0 < rank family
  rankInjective : Function.Injective rank
  standardRanks :
    rank (.standard .char) < rank (.standard .short) ∧
    rank (.standard .short) < rank (.standard .int) ∧
    rank (.standard .int) < rank (.standard .long) ∧
    rank (.standard .long) < rank (.standard .longLong)
  standardMinimum :
    7 ≤ signedPrecision (.standard .char) ∧
    15 ≤ signedPrecision (.standard .short) ∧
    15 ≤ signedPrecision (.standard .int) ∧
    31 ≤ signedPrecision (.standard .long) ∧
    63 ≤ signedPrecision (.standard .longLong)
  signedRanges : ∀ first second, rank first ≤ rank second →
    ValueRangeIncludes
      (.signed (signedPrecision second) (signedPositive second) (representation second))
      (.signed (signedPrecision first) (signedPositive first) (representation first))
  unsignedRanges : ∀ first second, rank first ≤ rank second →
    ValueRangeIncludes
      (.unsigned (unsignedPrecision second) (unsignedPositive second))
      (.unsigned (unsignedPrecision first) (unsignedPositive first))
  correspondingRange : ∀ family,
    (IntegerFormat.signed (signedPrecision family) (signedPositive family) (representation family)).upper ≤
      (IntegerFormat.unsigned (unsignedPrecision family) (unsignedPositive family)).upper

def IntegerType.format {Extension : Type u} (parameters : IntegerTypeParameters Extension) :
    IntegerType Extension → IntegerFormat
  | .boolean => .unsigned 1 (by decide)
  | .signed family => .signed (parameters.signedPrecision family)
      (parameters.signedPositive family) (parameters.representation family)
  | .unsigned family => .unsigned (parameters.unsignedPrecision family)
      (parameters.unsignedPositive family)

def IntegerType.rank {Extension : Type u} (parameters : IntegerTypeParameters Extension) :
    IntegerType Extension → Nat
  | .boolean => 0
  | .signed family | .unsigned family => parameters.rank family

def IntegerType.isSigned {Extension : Type u} : IntegerType Extension → Bool
  | .signed _ => true
  | .boolean | .unsigned _ => false

def IntegerType.unsignedCounterpart {Extension : Type u} :
    IntegerType Extension → IntegerType Extension
  | .signed family | .unsigned family => .unsigned family
  | .boolean => .boolean

def IntegerType.int {Extension : Type u} : IntegerType Extension := .signed (.standard .int)

def IntegerType.unsignedInt {Extension : Type u} : IntegerType Extension :=
  .unsigned (.standard .int)

theorem boolean_range_included {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (target : IntegerType Extension) :
    ValueRangeIncludes (target.format parameters) (IntegerType.boolean.format parameters) := by
  have zero := (target.format parameters).zero_representable
  have one := (target.format parameters).one_representable
  change (target.format parameters).lower ≤ 0 ∧ 1 ≤ (target.format parameters).upper
  exact ⟨zero.1, one.2⟩

def PromotionEligible {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (source : IntegerType Extension) : Prop :=
  source ≠ .int ∧ source ≠ .unsignedInt ∧ source.rank parameters ≤ IntegerType.int.rank parameters

instance {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (source : IntegerType Extension) :
    Decidable (PromotionEligible parameters source) :=
  inferInstanceAs (Decidable (source ≠ .int ∧ source ≠ .unsignedInt ∧
    source.rank parameters ≤ IntegerType.int.rank parameters))

def promoteIntegerType {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (source : IntegerType Extension) :
    IntegerType Extension :=
  if PromotionEligible parameters source then
    if ValueRangeIncludes (IntegerType.int.format parameters) (source.format parameters)
    then .int else .unsignedInt
  else source

inductive IntegerPromotion {Extension : Type u} (parameters : IntegerTypeParameters Extension) :
    IntegerType Extension → IntegerType Extension → Prop where
  | unchanged (source : IntegerType Extension)
      (ineligible : ¬ PromotionEligible parameters source) : IntegerPromotion parameters source source
  | toInt (source : IntegerType Extension) (eligible : PromotionEligible parameters source)
      (included : ValueRangeIncludes (IntegerType.int.format parameters) (source.format parameters)) :
      IntegerPromotion parameters source .int
  | toUnsignedInt (source : IntegerType Extension) (eligible : PromotionEligible parameters source)
      (notIncluded : ¬ ValueRangeIncludes (IntegerType.int.format parameters) (source.format parameters)) :
      IntegerPromotion parameters source .unsignedInt

theorem promoteIntegerType_sound {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (source : IntegerType Extension) :
    IntegerPromotion parameters source (promoteIntegerType parameters source) := by
  by_cases eligible : PromotionEligible parameters source
  · by_cases included : ValueRangeIncludes (IntegerType.int.format parameters) (source.format parameters)
    · simpa only [promoteIntegerType, if_pos eligible, if_pos included] using
        IntegerPromotion.toInt source eligible included
    · simpa only [promoteIntegerType, if_pos eligible, if_neg included] using
        IntegerPromotion.toUnsignedInt source eligible included
  · simpa only [promoteIntegerType, if_neg eligible] using IntegerPromotion.unchanged source eligible

theorem promoteIntegerType_complete {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (source target : IntegerType Extension)
    (promoted : IntegerPromotion parameters source target) :
    promoteIntegerType parameters source = target := by
  cases promoted with
  | unchanged ineligible => simp only [promoteIntegerType, if_neg ineligible]
  | toInt eligible included => simp only [promoteIntegerType, if_pos eligible, if_pos included]
  | toUnsignedInt eligible notIncluded =>
      simp only [promoteIntegerType, if_pos eligible, if_neg notIncluded]

theorem promoteIntegerType_iff {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (source target : IntegerType Extension) :
    promoteIntegerType parameters source = target ↔ IntegerPromotion parameters source target := by
  constructor
  · intro equal
    rw [← equal]
    exact promoteIntegerType_sound parameters source
  · exact promoteIntegerType_complete parameters source target

theorem integerPromotion_range {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (source target : IntegerType Extension) (promoted : IntegerPromotion parameters source target) :
    ValueRangeIncludes (target.format parameters) (source.format parameters) := by
  cases promoted with
  | unchanged _ => exact .refl _
  | toInt _ included => exact included
  | toUnsignedInt eligible notIncluded =>
      cases source with
      | boolean => exact False.elim (notIncluded (boolean_range_included parameters .int))
      | signed family =>
          exact False.elim (notIncluded (parameters.signedRanges family (.standard .int) eligible.2.2))
      | unsigned family => exact parameters.unsignedRanges family (.standard .int) eligible.2.2

theorem promoteIntegerType_range {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (source : IntegerType Extension) :
    ValueRangeIncludes ((promoteIntegerType parameters source).format parameters) (source.format parameters) :=
  integerPromotion_range parameters source _ (promoteIntegerType_sound parameters source)

theorem promoted_value_preserved {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (source : IntegerType Extension) (value : IntegerValue (source.format parameters)) :
    convertInteger policy value.value (.integer ((promoteIntegerType parameters source).format parameters)) =
      .value value.value :=
  convertInteger_preserves_representable policy _ _
    ((promoteIntegerType_range parameters source).represents value.valid)

theorem promoteIntegerType_ineligible {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (source : IntegerType Extension) :
    ¬ PromotionEligible parameters (promoteIntegerType parameters source) := by
  by_cases eligible : PromotionEligible parameters source
  · by_cases included : ValueRangeIncludes (IntegerType.int.format parameters) (source.format parameters)
    · rw [promoteIntegerType, if_pos eligible, if_pos included]
      intro impossible
      exact impossible.1 rfl
    · rw [promoteIntegerType, if_pos eligible, if_neg included]
      intro impossible
      exact impossible.2.1 rfl
  · simpa only [promoteIntegerType, if_neg eligible] using eligible

theorem promoteIntegerType_idempotent {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (source : IntegerType Extension) :
    promoteIntegerType parameters (promoteIntegerType parameters source) = promoteIntegerType parameters source := by
  rw [promoteIntegerType, if_neg (promoteIntegerType_ineligible parameters source)]

end Mettapedia.Languages.C11
