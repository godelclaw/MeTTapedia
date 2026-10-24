import Mettapedia.OSLF.Framework.GeneralCanonicalCongruenceAgreement
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations

/-!
# The general typed semantics is the reference relation on first-order profiles

Three agreements compose:
- on a first-order profile the general typed semantics relates the same well-sorted terms as the
  canonical relation (`FirstOrderProfile.general_step_iff_canonical`);
- without equations the canonical relation is the least contextual one
  (`langSemanticReducesUsing_iff_langReducesUsing_of_equation_free`);
- on an aligned language the least contextual relation is the reference relation
  (`ReferenceStep.contextualStep_iff_step`).

So on a first-order profile whose rules are aligned, the general typed semantics is the reference
relation (`FirstOrderProfile.general_step_iff_reference`). With equations, the canonical operational
theory of a language (`langGSLTUsing`) is the reference relation modulo equations when the rules and
equations are aligned (`langGSLT_step_iff_stepModulo`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}

/-- **On an aligned first-order profile the general typed semantics is the reference relation.** -/
theorem FirstOrderProfile.general_step_iff_reference (profile : FirstOrderProfile language provider)
    (aligned : ReferenceStep.ReferenceProfile language)
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv provider) (bound : List TypeExpr) (type : TypeExpr)
    {source target : Pattern}
    (typed : OpenPatternWellSorted (rootPlan language provider).snapshot.language
      (rootPlan language provider).snapshot.free bound type source) :
    (GeneralOccurrenceSemantics.gslt (rootPlan language provider) bound type).Step source target ↔
      ReferenceStep.Step relEnv language source target :=
  (profile.general_step_iff_canonical relEnv reads bound type typed).trans
    ((TypeSynthesis.langSemanticReducesUsing_iff_langReducesUsing_of_equation_free relEnv profile.equationFree
      source target).trans (ReferenceStep.contextualStep_iff_step relEnv language aligned))

/-- **The canonical operational theory is the reference relation modulo equations**, when the rules and
the equations are aligned. -/
theorem langGSLT_step_iff_stepModulo (relEnv : Engine.RelationEnv) (aligned : ReferenceStep.ReferenceProfile language)
    (equations : ReferenceStep.EquationsAligned language) {source target : Pattern} :
    (TypeSynthesis.langGSLTUsing relEnv language).Step source target ↔
      ReferenceStep.StepModulo relEnv language source target :=
  ReferenceStep.stepModuloEquations_iff aligned equations

end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
