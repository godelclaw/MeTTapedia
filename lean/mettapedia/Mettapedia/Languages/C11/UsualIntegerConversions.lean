import Mettapedia.Languages.C11.IntegerTypes

/-!
# C11 usual arithmetic conversions for integer operands

N1570 6.3.1.8 first promotes both operands, then chooses their common type
using signedness, rank and range. A higher-rank signed type is selected only
when it covers the unsigned operand's entire range. Otherwise its unsigned
counterpart is selected. Equal widths do not identify different ranks.

The rule relations are separate from the executable selectors. Their
correspondence is proved for arbitrary canonical types in an admitted
integer value profile. Signed common types cover both source ranges, so
these conversions cannot invoke a signed out-of-range policy or signal.
Unsigned common types may change mathematical values by modulus reduction.
This integer layer does not select floating or complex common types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11

universe u

theorem sameSignedness_rank_injective {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (first second : IntegerType Extension)
    (signedness : first.isSigned = second.isSigned)
    (rank : first.rank parameters = second.rank parameters) : first = second := by
  cases first with
  | boolean =>
      cases second with
      | boolean => rfl
      | signed family => cases signedness
      | unsigned family =>
          have positive := parameters.rankPositive family
          simp only [IntegerType.rank] at rank
          omega
  | signed first =>
      cases second with
      | boolean => cases signedness
      | signed second => exact congrArg IntegerType.signed (parameters.rankInjective rank)
      | unsigned second => cases signedness
  | unsigned first =>
      cases second with
      | boolean =>
          have positive := parameters.rankPositive first
          simp only [IntegerType.rank] at rank
          omega
      | signed second => cases signedness
      | unsigned second => exact congrArg IntegerType.unsigned (parameters.rankInjective rank)

theorem sameSignedness_rank_range {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (source target : IntegerType Extension)
    (signedness : source.isSigned = target.isSigned)
    (rank : source.rank parameters ≤ target.rank parameters) :
    ValueRangeIncludes (target.format parameters) (source.format parameters) := by
  cases source with
  | boolean => exact boolean_range_included parameters target
  | signed family =>
      cases target with
      | boolean => cases signedness
      | signed target => exact parameters.signedRanges family target rank
      | unsigned target => cases signedness
  | unsigned family =>
      cases target with
      | boolean =>
          have positive := parameters.rankPositive family
          simp only [IntegerType.rank] at rank
          omega
      | signed target => cases signedness
      | unsigned target => exact parameters.unsignedRanges family target rank

theorem unsignedCounterpart_isSigned {Extension : Type u} (type : IntegerType Extension) :
    type.unsignedCounterpart.isSigned = false := by cases type <;> rfl

def selectSameSignednessType {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (left right : IntegerType Extension) : IntegerType Extension :=
  if right.rank parameters ≤ left.rank parameters then left else right

def selectMixedIntegerType {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (unsigned signed : IntegerType Extension) : IntegerType Extension :=
  if signed.rank parameters ≤ unsigned.rank parameters then unsigned
  else if ValueRangeIncludes (signed.format parameters) (unsigned.format parameters)
    then signed else signed.unsignedCounterpart

def selectCommonIntegerType {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (left right : IntegerType Extension) : IntegerType Extension :=
  if left.isSigned = right.isSigned then selectSameSignednessType parameters left right
  else if left.isSigned = true then selectMixedIntegerType parameters right left
  else selectMixedIntegerType parameters left right

inductive SameSignednessType {Extension : Type u} (parameters : IntegerTypeParameters Extension) :
    IntegerType Extension → IntegerType Extension → IntegerType Extension → Prop where
  | same (type : IntegerType Extension) : SameSignednessType parameters type type type
  | leftHigher (left right : IntegerType Extension)
      (rank : right.rank parameters < left.rank parameters) : SameSignednessType parameters left right left
  | rightHigher (left right : IntegerType Extension)
      (rank : left.rank parameters < right.rank parameters) : SameSignednessType parameters left right right

inductive MixedIntegerType {Extension : Type u} (parameters : IntegerTypeParameters Extension) :
    IntegerType Extension → IntegerType Extension → IntegerType Extension → Prop where
  | unsignedRank (unsigned signed : IntegerType Extension)
      (rank : signed.rank parameters ≤ unsigned.rank parameters) :
      MixedIntegerType parameters unsigned signed unsigned
  | signedRange (unsigned signed : IntegerType Extension)
      (rank : unsigned.rank parameters < signed.rank parameters)
      (covered : ValueRangeIncludes (signed.format parameters) (unsigned.format parameters)) :
      MixedIntegerType parameters unsigned signed signed
  | unsignedCounterpart (unsigned signed : IntegerType Extension)
      (rank : unsigned.rank parameters < signed.rank parameters)
      (notCovered : ¬ ValueRangeIncludes (signed.format parameters) (unsigned.format parameters)) :
      MixedIntegerType parameters unsigned signed signed.unsignedCounterpart

inductive CommonIntegerType {Extension : Type u} (parameters : IntegerTypeParameters Extension) :
    IntegerType Extension → IntegerType Extension → IntegerType Extension → Prop where
  | sameSignedness (left right target : IntegerType Extension)
      (signedness : left.isSigned = right.isSigned)
      (choice : SameSignednessType parameters left right target) :
      CommonIntegerType parameters left right target
  | unsignedLeft (left right target : IntegerType Extension)
      (leftUnsigned : left.isSigned = false) (rightSigned : right.isSigned = true)
      (choice : MixedIntegerType parameters left right target) :
      CommonIntegerType parameters left right target
  | unsignedRight (left right target : IntegerType Extension)
      (leftSigned : left.isSigned = true) (rightUnsigned : right.isSigned = false)
      (choice : MixedIntegerType parameters right left target) :
      CommonIntegerType parameters left right target

theorem selectSameSignednessType_sound {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (left right : IntegerType Extension)
    (signedness : left.isSigned = right.isSigned) :
    SameSignednessType parameters left right (selectSameSignednessType parameters left right) := by
  by_cases rank : right.rank parameters ≤ left.rank parameters
  · rw [selectSameSignednessType, if_pos rank]
    by_cases equal : left.rank parameters = right.rank parameters
    · have same := sameSignedness_rank_injective parameters left right signedness equal
      subst right
      exact .same left
    · exact .leftHigher left right (by omega)
  · rw [selectSameSignednessType, if_neg rank]
    exact .rightHigher left right (by omega)

theorem selectSameSignednessType_complete {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (left right target : IntegerType Extension)
    (chosen : SameSignednessType parameters left right target) :
    selectSameSignednessType parameters left right = target := by
  cases chosen with
  | same => simp only [selectSameSignednessType, le_refl, if_true]
  | leftHigher _ rank => simp only [selectSameSignednessType, if_pos (le_of_lt rank)]
  | rightHigher _ rank => simp only [selectSameSignednessType, if_neg (not_le_of_gt rank)]

theorem selectMixedIntegerType_sound {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (unsigned signed : IntegerType Extension) :
    MixedIntegerType parameters unsigned signed (selectMixedIntegerType parameters unsigned signed) := by
  by_cases rank : signed.rank parameters ≤ unsigned.rank parameters
  · rw [selectMixedIntegerType, if_pos rank]
    exact .unsignedRank unsigned signed rank
  · rw [selectMixedIntegerType, if_neg rank]
    by_cases covered : ValueRangeIncludes (signed.format parameters) (unsigned.format parameters)
    · rw [if_pos covered]
      exact .signedRange unsigned signed (by omega) covered
    · rw [if_neg covered]
      exact .unsignedCounterpart unsigned signed (by omega) covered

theorem selectMixedIntegerType_complete {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (unsigned signed target : IntegerType Extension)
    (chosen : MixedIntegerType parameters unsigned signed target) :
    selectMixedIntegerType parameters unsigned signed = target := by
  cases chosen with
  | unsignedRank rank => simp only [selectMixedIntegerType, if_pos rank]
  | signedRange rank covered =>
      simp only [selectMixedIntegerType, if_neg (not_le_of_gt rank), if_pos covered]
  | unsignedCounterpart rank notCovered =>
      simp only [selectMixedIntegerType, if_neg (not_le_of_gt rank), if_neg notCovered]

theorem selectCommonIntegerType_sound {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (left right : IntegerType Extension) :
    CommonIntegerType parameters left right (selectCommonIntegerType parameters left right) := by
  by_cases signedness : left.isSigned = right.isSigned
  · rw [selectCommonIntegerType, if_pos signedness]
    exact .sameSignedness left right _ signedness
      (selectSameSignednessType_sound parameters left right signedness)
  · rw [selectCommonIntegerType, if_neg signedness]
    by_cases leftSigned : left.isSigned = true
    · rw [if_pos leftSigned]
      have rightUnsigned : right.isSigned = false := by
        cases rightSign : right.isSigned <;> simp_all
      exact .unsignedRight left right _ leftSigned rightUnsigned
        (selectMixedIntegerType_sound parameters right left)
    · rw [if_neg leftSigned]
      have leftUnsigned : left.isSigned = false := Bool.eq_false_iff.mpr leftSigned
      have rightSigned : right.isSigned = true := by
        cases rightSign : right.isSigned <;> simp_all
      exact .unsignedLeft left right _ leftUnsigned rightSigned
        (selectMixedIntegerType_sound parameters left right)

theorem selectCommonIntegerType_complete {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (left right target : IntegerType Extension)
    (chosen : CommonIntegerType parameters left right target) :
    selectCommonIntegerType parameters left right = target := by
  cases chosen with
  | sameSignedness signedness choice =>
      rw [selectCommonIntegerType, if_pos signedness]
      exact selectSameSignednessType_complete parameters left right target choice
  | unsignedLeft leftUnsigned rightSigned choice =>
      have different : left.isSigned ≠ right.isSigned := by simp only [leftUnsigned, rightSigned]; decide
      rw [selectCommonIntegerType, if_neg different, if_neg (by simp only [leftUnsigned]; decide)]
      exact selectMixedIntegerType_complete parameters left right target choice
  | unsignedRight leftSigned rightUnsigned choice =>
      have different : left.isSigned ≠ right.isSigned := by simp only [leftSigned, rightUnsigned]; decide
      rw [selectCommonIntegerType, if_neg different, if_pos leftSigned]
      exact selectMixedIntegerType_complete parameters right left target choice

theorem selectCommonIntegerType_iff {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (left right target : IntegerType Extension) :
    selectCommonIntegerType parameters left right = target ↔ CommonIntegerType parameters left right target := by
  constructor
  · intro equal
    rw [← equal]
    exact selectCommonIntegerType_sound parameters left right
  · exact selectCommonIntegerType_complete parameters left right target

theorem SameSignednessType.symm {Extension : Type u} {parameters : IntegerTypeParameters Extension}
    {left right target : IntegerType Extension} (chosen : SameSignednessType parameters left right target) :
    SameSignednessType parameters right left target := by
  cases chosen with
  | same => exact .same _
  | leftHigher _ rank => exact .rightHigher _ _ rank
  | rightHigher _ rank => exact .leftHigher _ _ rank

theorem CommonIntegerType.symm {Extension : Type u} {parameters : IntegerTypeParameters Extension}
    {left right target : IntegerType Extension} (chosen : CommonIntegerType parameters left right target) :
    CommonIntegerType parameters right left target := by
  cases chosen with
  | sameSignedness signedness choice => exact .sameSignedness _ _ _ signedness.symm choice.symm
  | unsignedLeft unsigned signed choice => exact .unsignedRight _ _ _ signed unsigned choice
  | unsignedRight signed unsigned choice => exact .unsignedLeft _ _ _ unsigned signed choice

theorem selectCommonIntegerType_commutative {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (left right : IntegerType Extension) :
    selectCommonIntegerType parameters left right = selectCommonIntegerType parameters right left :=
  (selectCommonIntegerType_complete parameters right left _
    (selectCommonIntegerType_sound parameters left right).symm).symm

theorem sameSignednessType_range {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (left right target : IntegerType Extension) (signedness : left.isSigned = right.isSigned)
    (chosen : SameSignednessType parameters left right target) :
    ValueRangeIncludes (target.format parameters) (left.format parameters) ∧
      ValueRangeIncludes (target.format parameters) (right.format parameters) := by
  cases chosen with
  | same => exact ⟨.refl _, .refl _⟩
  | leftHigher _ rank => exact ⟨.refl _,
      sameSignedness_rank_range parameters right left signedness.symm (le_of_lt rank)⟩
  | rightHigher _ rank => exact ⟨
      sameSignedness_rank_range parameters left right signedness (le_of_lt rank), .refl _⟩

theorem mixedIntegerType_signed_range {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (unsigned signed target : IntegerType Extension) (unsignedType : unsigned.isSigned = false)
    (chosen : MixedIntegerType parameters unsigned signed target) (signedTarget : target.isSigned = true) :
    ValueRangeIncludes (target.format parameters) (unsigned.format parameters) ∧
      ValueRangeIncludes (target.format parameters) (signed.format parameters) := by
  cases chosen with
  | unsignedRank _ => rw [unsignedType] at signedTarget; cases signedTarget
  | signedRange _ covered => exact ⟨covered, .refl _⟩
  | unsignedCounterpart _ _ => rw [unsignedCounterpart_isSigned] at signedTarget; cases signedTarget

theorem commonIntegerType_signed_range {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (left right target : IntegerType Extension) (chosen : CommonIntegerType parameters left right target)
    (signedTarget : target.isSigned = true) :
    ValueRangeIncludes (target.format parameters) (left.format parameters) ∧
      ValueRangeIncludes (target.format parameters) (right.format parameters) := by
  cases chosen with
  | sameSignedness signedness choice => exact sameSignednessType_range parameters left right target signedness choice
  | unsignedLeft unsigned _ choice =>
      exact mixedIntegerType_signed_range parameters left right target unsigned choice signedTarget
  | unsignedRight _ unsigned choice =>
      exact (mixedIntegerType_signed_range parameters right left target unsigned choice signedTarget).symm

def usualIntegerType {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (left right : IntegerType Extension) : IntegerType Extension :=
  selectCommonIntegerType parameters (promoteIntegerType parameters left) (promoteIntegerType parameters right)

inductive UsualIntegerType {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (left right target : IntegerType Extension) : Prop where
  | promoted (first second : IntegerType Extension)
      (promoteLeft : IntegerPromotion parameters left first)
      (promoteRight : IntegerPromotion parameters right second)
      (common : CommonIntegerType parameters first second target) : UsualIntegerType parameters left right target

theorem usualIntegerType_sound {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (left right : IntegerType Extension) :
    UsualIntegerType parameters left right (usualIntegerType parameters left right) :=
  .promoted _ _ (promoteIntegerType_sound parameters left) (promoteIntegerType_sound parameters right)
    (selectCommonIntegerType_sound parameters _ _)

theorem usualIntegerType_complete {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (left right target : IntegerType Extension)
    (chosen : UsualIntegerType parameters left right target) : usualIntegerType parameters left right = target := by
  cases chosen with
  | promoted first second promoteLeft promoteRight common =>
      rw [usualIntegerType, promoteIntegerType_complete parameters left first promoteLeft,
        promoteIntegerType_complete parameters right second promoteRight]
      exact selectCommonIntegerType_complete parameters first second target common

theorem usualIntegerType_iff {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (left right target : IntegerType Extension) :
    usualIntegerType parameters left right = target ↔ UsualIntegerType parameters left right target := by
  constructor
  · intro equal
    rw [← equal]
    exact usualIntegerType_sound parameters left right
  · exact usualIntegerType_complete parameters left right target

theorem usualIntegerType_commutative {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (left right : IntegerType Extension) :
    usualIntegerType parameters left right = usualIntegerType parameters right left :=
  selectCommonIntegerType_commutative parameters _ _

theorem usualIntegerType_signed_range {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (left right : IntegerType Extension)
    (signedTarget : (usualIntegerType parameters left right).isSigned = true) :
    ValueRangeIncludes ((usualIntegerType parameters left right).format parameters) (left.format parameters) ∧
      ValueRangeIncludes ((usualIntegerType parameters left right).format parameters) (right.format parameters) := by
  have common := commonIntegerType_signed_range parameters _ _ _
    (selectCommonIntegerType_sound parameters (promoteIntegerType parameters left)
      (promoteIntegerType parameters right)) signedTarget
  exact ⟨common.1.trans (promoteIntegerType_range parameters left),
    common.2.trans (promoteIntegerType_range parameters right)⟩

end Mettapedia.Languages.C11
