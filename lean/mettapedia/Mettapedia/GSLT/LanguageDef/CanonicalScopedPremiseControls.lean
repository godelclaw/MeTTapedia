import Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
import Mettapedia.OSLF.Framework.LambdaInstance

/-!
# Controls for canonical scoped premises on the lambda calculus

Root premises elaborate only when their sorts are declared; lambda congruence under its binder
uses the explicit scoped form, and an escaping local variable fails elaboration.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise

private def lambdaTerm : TypeExpr := .base "Term"

private def lambdaFree : FreeTypeContext :=
  fun name => if name == "source" || name == "target" then some lambdaTerm else none

/-- The old root form elaborates when its two variables have one sort. -/
example : inferRootSort?
    Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc lambdaFree []
    (.fvar "source") (.fvar "target") = some lambdaTerm := by decide

/-- A missing sort declaration never gets guessed from the first occurrence. -/
example : inferRootSort?
    Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc FreeTypeContext.empty []
    (.fvar "source") (.fvar "target") = none := by decide

/-- Lambda congruence under its local binder uses the explicit form. -/
example : compile?
    Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty []
    (.scopedStep TypedScopedStepPremise.lambdaBodyStep) =
      some (.step TypedScopedStepPremise.lambdaBodyStep) := by decide

/-- An escaping local variable fails canonical elaboration. -/
example : compile?
    Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty []
    (.scopedStep { TypedScopedStepPremise.lambdaBodyStep with target := .bvar 1 }) =
      none := by decide

end Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
