import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableEvaluation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ConversionQuotient

/-!
# Actual set values of checked evaluation results

Successful execution by the existing finite procedures constructs typed
equality. The existing annotation-lifting theorem reconstructs annotated
representatives, and the independent set model identifies their actual values.
The final theorem compares independently supplied, typed annotations too.

The qualification is local to the selected rule package, formed telescope and
set model. It asserts neither an ambient foundation for Prime nor native-C
refinement. Universe assumptions belong to the construction of the supplied
model, rather than being inferred as necessary from this comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace ExecutableEvaluation

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
/-- The output equality is lifted from the computed derivation. No annotated
source or output proof is requested by the execution procedure. -/
theorem run_annotation {n fuel : Nat} {context : Ctx Head n}
    {annotatedContext : CCtx Head n} (formed : CCtxFormed P annotatedContext)
    (contextErases : annotatedContext.erase = context)
    (readback : Normalization.ExecutableEvaluation.Readback Head)
    {source value type : Tm Head n}
    (returned : Normalization.ExecutableEvaluation.run S.R choices reducer readback fuel
      context source = some (value, type)) :
    ∃ left right domain : CTm Head n,
      left.erase = source ∧ right.erase = value ∧ domain.erase = type ∧
        CEqual P annotatedContext left right domain := by
  have equal := (Normalization.ExecutableEvaluation.run_sound facts roots headSteps algebra
    declared choices reducer readback returned).2.2
  exact lifts S.levels lifting equal formed contextErases

include facts roots headSteps algebra declared choices reducer lifting model in
/-- Equality of actual set values and membership of the returned value in
its interpreted type, at every satisfying context environment. -/
theorem run_material {n fuel : Nat} {context : Ctx Head n}
    {annotatedContext : CCtx Head n} (formed : CCtxFormed P annotatedContext)
    (contextErases : annotatedContext.erase = context)
    (readback : Normalization.ExecutableEvaluation.Readback Head)
    {source value type : Tm Head n}
    (returned : Normalization.ExecutableEvaluation.run S.R choices reducer readback fuel
      context source = some (value, type)) :
    ∃ left right domain : CTm Head n,
      left.erase = source ∧ right.erase = value ∧ domain.erase = type ∧
      CTyped P annotatedContext left domain ∧ CTyped P annotatedContext right domain ∧
      ∀ environment, Sat heads constants annotatedContext environment →
        ev heads constants left environment = ev heads constants right environment ∧
        ev heads constants right environment ∈ ev heads constants domain environment := by
  obtain ⟨left, right, domain, el, er, ed, equal⟩ :=
    run_annotation facts roots headSteps algebra declared choices reducer lifting
      formed contextErases readback returned
  obtain ⟨typedLeft, typedRight⟩ := CEqual.typed S.levels equal formed
  exact ⟨left, right, domain, el, er, ed, typedLeft, typedRight,
    fun environment satisfies => ⟨CDerivable.sound_equality model equal environment satisfies,
      CDerivable.sound model typedRight environment satisfies⟩⟩

include facts roots headSteps algebra declared choices reducer lifting model in
/-- Existing annotations retain their own values. The result is not merely
existence of some equal model representatives. -/
theorem run_existing_values {n fuel : Nat} {context : Ctx Head n}
    {annotatedContext : CCtx Head n} (formed : CCtxFormed P annotatedContext)
    (contextErases : annotatedContext.erase = context)
    (readback : Normalization.ExecutableEvaluation.Readback Head)
    {source value type : Tm Head n}
    (returned : Normalization.ExecutableEvaluation.run S.R choices reducer readback fuel
      context source = some (value, type))
    {sourceCode valueCode sourceType valueType : CTm Head n}
    (sourceTyped : CTyped P annotatedContext sourceCode sourceType)
    (valueTyped : CTyped P annotatedContext valueCode valueType)
    (sourceErases : sourceCode.erase = source) (valueErases : valueCode.erase = value)
    (sourceTypeErases : sourceType.erase = type) (valueTypeErases : valueType.erase = type)
    (environment : Env.{u} n) (satisfies : Sat heads constants annotatedContext environment) :
    ev heads constants sourceCode environment = ev heads constants valueCode environment := by
  obtain ⟨left, right, domain, el, er, ed, equal⟩ :=
    run_annotation facts roots headSteps algebra declared choices reducer lifting
      formed contextErases readback returned
  obtain ⟨typedLeft, typedRight⟩ := CEqual.typed S.levels equal formed
  have leftAgrees := ConversionQuotient.annotationValue_independent lifting model formed
    sourceTyped typedLeft (sourceErases.trans el.symm) (sourceTypeErases.trans ed.symm)
  have rightAgrees := ConversionQuotient.annotationValue_independent lifting model formed
    valueTyped typedRight (valueErases.trans er.symm) (valueTypeErases.trans ed.symm)
  have leftValue := congrFun leftAgrees ⟨environment, satisfies⟩
  have rightValue := congrFun rightAgrees ⟨environment, satisfies⟩
  exact leftValue.trans ((CDerivable.sound_equality model equal environment satisfies).trans rightValue.symm)

end ExecutableEvaluation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
