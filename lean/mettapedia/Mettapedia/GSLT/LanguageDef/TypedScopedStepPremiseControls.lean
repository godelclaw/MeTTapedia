import Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise
import Mettapedia.OSLF.Framework.LambdaInstance

/-!
# Controls for sorted step premises on the lambda calculus

`lambdaBodyStep` checked against the authored lambda calculus, and a concrete `LamCong` rule
whose premise is a step under the lambda's binder; negative controls for an index outside the
binder and a false endpoint sort.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

example : check Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty [] lambdaBodyStep = true := by decide

example : HasType Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty [] lambdaBodyStep := by
  exact check_sound (by decide)

/-- The local binder does not license an index in the absent ambient context. -/
example : check Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty []
      { lambdaBodyStep with target := .bvar 1 } = false := by decide

/-- A false endpoint sort cannot be repaired by the matching source shape. -/
example : check Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty []
      { lambdaBodyStep with resultType := .base "Name" } = false := by decide

/-- A concrete LamCong instance: its recursive child is checked in the
context of the lambda binder, while the authored rule endpoints are closed. -/
def lambdaCongRule : RewriteRule where
  name := "LamCongConcrete"
  typeContext := []
  premises := [.scopedStep lambdaBodyStep]
  left := .apply "Lam" [.lambda none lambdaBodyStep.source]
  right := .apply "Lam" [.lambda none lambdaBodyStep.target]

def lambdaWithCongruence : LanguageDef :=
  { Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc with
    rewrites :=
      Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc.rewrites ++
        [lambdaCongRule] }

theorem lambdaWithCongruence_valid : lambdaWithCongruence.validate = [] := by
  simp [LanguageDef.validate, lambdaWithCongruence, lambdaCongRule,
    Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc,
    LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors, LanguageDef.premisePatterns,
    LanguageDef.premiseLocallyScoped, LanguageDef.premiseStepTypeExprs,
    LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
    LanguageDef.premiseForAllParams, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, Pattern.constructorRefs,
    Pattern.constructorRefsList, Pattern.freeFvarNames,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, LanguageDef.typeNames,
    lambdaBodyStep, term, TypeDecl.plain, TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr]

/-- The same authored rule is rejected if its premise refers to a variable
outside the one binder it declares. -/
def escapingLambdaCongruence : LanguageDef :=
  { lambdaWithCongruence with
    rewrites := [
      { lambdaCongRule with
        premises := [.scopedStep { lambdaBodyStep with target := .bvar 1 }] }
    ] }

theorem escapingLambdaCongruence_invalid :
    escapingLambdaCongruence.validate ≠ [] := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise
