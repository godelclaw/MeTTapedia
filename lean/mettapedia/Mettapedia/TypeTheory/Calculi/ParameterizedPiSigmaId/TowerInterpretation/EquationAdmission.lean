import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.EquationAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ConversionQuotient

/-!
# Material values of checked computation equations

The finite equation check supplies the equality derivation used by annotation
lifting. A selected set model then equates the actual values at every satisfying
environment. Existing independently typed annotations keep their own values;
the theorem does not replace them by arbitrary semantic representatives.

The selected rule package already includes the definition's checked witness.
This comparison does not infer termination from equality or identify the native
C elaborator with the symbolic checker.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace EquationAdmission

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization
open UniverseLevel (LevelOrder)

universe u

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}
  [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (headSteps : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R)
  {P : ChurchRules S.R} (lifting : LiftingFacts P)
  {heads : Head → ZFSet.{u}} {constants : DeclName → ZFSet.{u}}
  (model : SetModel heads constants P)

include facts roots headSteps algebra declared choices reducer lifting in
theorem annotation {fuel : Nat}
    {equations : List (Normalization.EquationAdmission.Equation Head)}
    (accepted : Normalization.EquationAdmission.check S.R choices reducer fuel equations = true)
    {equation : Normalization.EquationAdmission.Equation Head} (member : equation ∈ equations)
    {context : CCtx Head equation.arity} (formed : CCtxFormed P context)
    (erases : context.erase = equation.context) :
    ∃ left right type : CTm Head equation.arity,
      left.erase = equation.left ∧ right.erase = equation.right ∧ type.erase = equation.type ∧
      CEqual P context left right type := by
  have equal := (Normalization.EquationAdmission.sound facts roots headSteps algebra declared
    choices reducer accepted member).2.2
  exact lifts S.levels lifting equal formed erases

include facts roots headSteps algebra declared choices reducer lifting model in
theorem existing_values {fuel : Nat}
    {equations : List (Normalization.EquationAdmission.Equation Head)}
    (accepted : Normalization.EquationAdmission.check S.R choices reducer fuel equations = true)
    {equation : Normalization.EquationAdmission.Equation Head} (member : equation ∈ equations)
    {context : CCtx Head equation.arity} (formed : CCtxFormed P context)
    (erases : context.erase = equation.context)
    {left right leftType rightType : CTm Head equation.arity}
    (leftTyped : CTyped P context left leftType) (rightTyped : CTyped P context right rightType)
    (leftErases : left.erase = equation.left) (rightErases : right.erase = equation.right)
    (leftTypeErases : leftType.erase = equation.type) (rightTypeErases : rightType.erase = equation.type)
    (environment : Env.{u} equation.arity) (satisfies : Sat heads constants context environment) :
    ev heads constants left environment = ev heads constants right environment := by
  obtain ⟨first, second, type, ef, es, et, equal⟩ :=
    annotation facts roots headSteps algebra declared choices reducer lifting
      accepted member formed erases
  obtain ⟨firstTyped, secondTyped⟩ := CEqual.typed S.levels equal formed
  have firstAgrees := ConversionQuotient.annotationValue_independent lifting model formed
    leftTyped firstTyped (leftErases.trans ef.symm) (leftTypeErases.trans et.symm)
  have secondAgrees := ConversionQuotient.annotationValue_independent lifting model formed
    rightTyped secondTyped (rightErases.trans es.symm) (rightTypeErases.trans et.symm)
  exact (congrFun firstAgrees ⟨environment, satisfies⟩).trans
    ((CDerivable.sound_equality model equal environment satisfies).trans
      (congrFun secondAgrees ⟨environment, satisfies⟩).symm)

end EquationAdmission
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
