import Mettapedia.Languages.C11.UsualIntegerConversions
import Mettapedia.Languages.C11.IntegerArithmetic

/-!
# Integer arithmetic with operand type conversion

Operands enter with their own canonical types and mathematical values.
Preparation constructs the common type and both converted values. Its
independent relation requires the usual-conversion judgment and the two
value-conversion judgments. Soundness and completeness join this relation to
the executable preparation. The arithmetic relation then composes those
conversions with the existing five-operator arithmetic semantics.

These are numeric reductions inside C expressions. Lvalue conversion,
source-type compatibility, operand evaluation, sequencing, objects and
floating/complex arithmetic remain separate obligations. No native compiler
or whole-program correspondence is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11

universe u

def castCoveredInteger {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (target : IntegerType Extension) (input : Int)
    (covered : target.isSigned = true → (target.format parameters).Represents input) :
    IntegerValue (target.format parameters) :=
  match target with
  | .boolean => ⟨input % powerOfTwo 1, unsigned_reduction_in_range 1 (by decide) input⟩
  | .unsigned family => ⟨input % powerOfTwo (parameters.unsignedPrecision family),
      unsigned_reduction_in_range _ (parameters.unsignedPositive family) input⟩
  | .signed family => ⟨input, covered rfl⟩

theorem castCoveredInteger_converts {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (policy : SignedConversionPolicy) (target : IntegerType Extension) (input : Int)
    (covered : target.isSigned = true → (target.format parameters).Represents input) :
    convertInteger policy input (.integer (target.format parameters)) =
      .value (castCoveredInteger parameters target input covered).value := by
  cases target with
  | boolean => rfl
  | unsigned family => rfl
  | signed family => exact convertInteger_preserves_representable policy _ input (covered rfl)

structure PreparedIntegerOperands {Extension : Type u} (parameters : IntegerTypeParameters Extension) where
  target : IntegerType Extension
  left : IntegerValue (target.format parameters)
  right : IntegerValue (target.format parameters)

theorem PreparedIntegerOperands.ext {Extension : Type u} {parameters : IntegerTypeParameters Extension}
    (first second : PreparedIntegerOperands parameters) (target : first.target = second.target)
    (left : first.left.value = second.left.value) (right : first.right.value = second.right.value) :
    first = second := by
  cases first with
  | mk firstType firstLeft firstRight =>
      cases second with
      | mk secondType secondLeft secondRight =>
          cases target
          cases firstLeft
          cases secondLeft
          cases firstRight
          cases secondRight
          cases left
          cases right
          rfl

def prepareIntegerOperands {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (leftType rightType : IntegerType Extension)
    (left : IntegerValue (leftType.format parameters)) (right : IntegerValue (rightType.format parameters)) :
    PreparedIntegerOperands parameters :=
  let target := usualIntegerType parameters leftType rightType
  { target := target
    left := castCoveredInteger parameters target left.value (fun signed =>
      ((usualIntegerType_signed_range parameters leftType rightType signed).1).represents left.valid)
    right := castCoveredInteger parameters target right.value (fun signed =>
      ((usualIntegerType_signed_range parameters leftType rightType signed).2).represents right.valid) }

theorem prepared_left_conversion {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (leftType rightType : IntegerType Extension) (left : IntegerValue (leftType.format parameters))
    (right : IntegerValue (rightType.format parameters)) :
    let prepared := prepareIntegerOperands parameters leftType rightType left right
    convertInteger policy left.value (.integer (prepared.target.format parameters)) = .value prepared.left.value :=
  castCoveredInteger_converts parameters policy _ left.value _

theorem prepared_right_conversion {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (leftType rightType : IntegerType Extension) (left : IntegerValue (leftType.format parameters))
    (right : IntegerValue (rightType.format parameters)) :
    let prepared := prepareIntegerOperands parameters leftType rightType left right
    convertInteger policy right.value (.integer (prepared.target.format parameters)) = .value prepared.right.value :=
  castCoveredInteger_converts parameters policy _ right.value _

inductive IntegerOperandsPrepared {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (leftType rightType : IntegerType Extension) (left : IntegerValue (leftType.format parameters))
    (right : IntegerValue (rightType.format parameters)) : PreparedIntegerOperands parameters → Prop where
  | converted (prepared : PreparedIntegerOperands parameters)
      (chosen : UsualIntegerType parameters leftType rightType prepared.target)
      (leftConversion : IntegerConverts policy left.value (.integer (prepared.target.format parameters))
        (.value prepared.left.value))
      (rightConversion : IntegerConverts policy right.value (.integer (prepared.target.format parameters))
        (.value prepared.right.value)) : IntegerOperandsPrepared parameters policy leftType rightType left right prepared

theorem prepareIntegerOperands_sound {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (leftType rightType : IntegerType Extension) (left : IntegerValue (leftType.format parameters))
    (right : IntegerValue (rightType.format parameters)) :
    IntegerOperandsPrepared parameters policy leftType rightType left right
      (prepareIntegerOperands parameters leftType rightType left right) :=
  .converted _ (usualIntegerType_sound parameters leftType rightType)
    ((convertInteger_iff policy _ _ _).mp (prepared_left_conversion parameters policy leftType rightType left right))
    ((convertInteger_iff policy _ _ _).mp (prepared_right_conversion parameters policy leftType rightType left right))

theorem prepareIntegerOperands_complete {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (leftType rightType : IntegerType Extension) (left : IntegerValue (leftType.format parameters))
    (right : IntegerValue (rightType.format parameters)) (prepared : PreparedIntegerOperands parameters)
    (correct : IntegerOperandsPrepared parameters policy leftType rightType left right prepared) :
    prepareIntegerOperands parameters leftType rightType left right = prepared := by
  cases correct with
  | converted chosen leftConversion rightConversion =>
      have target : (prepareIntegerOperands parameters leftType rightType left right).target = prepared.target :=
        usualIntegerType_complete parameters leftType rightType prepared.target chosen
      have first := prepared_left_conversion parameters policy leftType rightType left right
      have second := prepared_right_conversion parameters policy leftType rightType left right
      dsimp only at first second
      have firstTarget := congrArg
        (fun type : IntegerType Extension => convertInteger policy left.value (.integer (type.format parameters))) target
      have secondTarget := congrArg
        (fun type : IntegerType Extension => convertInteger policy right.value (.integer (type.format parameters))) target
      exact PreparedIntegerOperands.ext _ _ target
        (ConversionOutcome.value.inj (first.symm.trans
          (firstTarget.trans (convertInteger_complete policy _ _ _ leftConversion))))
        (ConversionOutcome.value.inj (second.symm.trans
          (secondTarget.trans (convertInteger_complete policy _ _ _ rightConversion))))

theorem prepareIntegerOperands_iff {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (leftType rightType : IntegerType Extension) (left : IntegerValue (leftType.format parameters))
    (right : IntegerValue (rightType.format parameters)) (prepared : PreparedIntegerOperands parameters) :
    prepareIntegerOperands parameters leftType rightType left right = prepared ↔
      IntegerOperandsPrepared parameters policy leftType rightType left right prepared := by
  constructor
  · intro equal
    rw [← equal]
    exact prepareIntegerOperands_sound parameters policy leftType rightType left right
  · exact prepareIntegerOperands_complete parameters policy leftType rightType left right prepared

structure TypedIntegerOutcome (Extension : Type u) where
  type : IntegerType Extension
  outcome : IntegerArithmeticOutcome
  deriving DecidableEq, Repr

def evaluateTypedIntegerBinary {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (operation : IntegerBinaryOperator)
    (leftType rightType : IntegerType Extension) (left : IntegerValue (leftType.format parameters))
    (right : IntegerValue (rightType.format parameters)) : TypedIntegerOutcome Extension :=
  let prepared := prepareIntegerOperands parameters leftType rightType left right
  ⟨prepared.target, evaluateIntegerBinary (prepared.target.format parameters) operation prepared.left prepared.right⟩

inductive TypedIntegerBinaryEvaluation {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (operation : IntegerBinaryOperator) (leftType rightType : IntegerType Extension)
    (left : IntegerValue (leftType.format parameters)) (right : IntegerValue (rightType.format parameters)) :
    TypedIntegerOutcome Extension → Prop where
  | evaluated (prepared : PreparedIntegerOperands parameters) (outcome : IntegerArithmeticOutcome)
      (conversions : IntegerOperandsPrepared parameters policy leftType rightType left right prepared)
      (arithmetic : IntegerBinaryEvaluation (prepared.target.format parameters)
        prepared.left prepared.right operation outcome) :
      TypedIntegerBinaryEvaluation parameters policy operation leftType rightType left right ⟨prepared.target, outcome⟩

theorem evaluateTypedIntegerBinary_sound {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (operation : IntegerBinaryOperator) (leftType rightType : IntegerType Extension)
    (left : IntegerValue (leftType.format parameters)) (right : IntegerValue (rightType.format parameters)) :
    TypedIntegerBinaryEvaluation parameters policy operation leftType rightType left right
      (evaluateTypedIntegerBinary parameters operation leftType rightType left right) :=
  .evaluated _ _ (prepareIntegerOperands_sound parameters policy leftType rightType left right)
    (evaluateIntegerBinary_sound _ operation _ _)

theorem evaluateTypedIntegerBinary_complete {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (operation : IntegerBinaryOperator) (leftType rightType : IntegerType Extension)
    (left : IntegerValue (leftType.format parameters)) (right : IntegerValue (rightType.format parameters))
    (outcome : TypedIntegerOutcome Extension)
    (evaluated : TypedIntegerBinaryEvaluation parameters policy operation leftType rightType left right outcome) :
    evaluateTypedIntegerBinary parameters operation leftType rightType left right = outcome := by
  cases evaluated with
  | evaluated prepared result conversions arithmetic =>
      have preparation := prepareIntegerOperands_complete parameters policy leftType rightType left right prepared conversions
      unfold evaluateTypedIntegerBinary
      dsimp only
      rw [preparation, evaluateIntegerBinary_complete _ operation _ _ result arithmetic]

theorem evaluateTypedIntegerBinary_iff {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (operation : IntegerBinaryOperator) (leftType rightType : IntegerType Extension)
    (left : IntegerValue (leftType.format parameters)) (right : IntegerValue (rightType.format parameters))
    (outcome : TypedIntegerOutcome Extension) :
    evaluateTypedIntegerBinary parameters operation leftType rightType left right = outcome ↔
      TypedIntegerBinaryEvaluation parameters policy operation leftType rightType left right outcome := by
  constructor
  · intro equal
    rw [← equal]
    exact evaluateTypedIntegerBinary_sound parameters policy operation leftType rightType left right
  · exact evaluateTypedIntegerBinary_complete parameters policy operation leftType rightType left right outcome

end Mettapedia.Languages.C11
