import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalTemplates
import Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralRhoBinding

/-!
# Canonical-template admission for the operational consumers

These checks range over the whole authored presentations and the actual
compiled declarations. They do not restrict object terms to a custom finite
decoder or chosen ground examples.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalTemplates

theorem guarded_language_canonical :
    checkLanguage EquationFrontierBinderProfile.language = true := by cbv

theorem guarded_plan_canonical (allowed : List EquationFrontierBinderProfile.Token) :
    checkPlan (GeneralExecutionAdmission.compile
      (GeneralGuardedBinderAdmission.snapshot allowed) GeneralGuardedBinderAdmission.permissions) = true :=
  compiled_plan_canonical _ _

theorem rho_language_canonical : checkLanguage GeneralRho.language = true := by cbv

theorem rho_plan_canonical : checkPlan GeneralRho.plan = true := by
  exact compiled_plan_canonical _ _

end Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalTemplates
