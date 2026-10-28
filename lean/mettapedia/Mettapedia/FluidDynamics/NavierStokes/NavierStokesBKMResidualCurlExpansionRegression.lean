import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMResidualCurlExpansion

/-!
# Regression checks for the BKM residual-curl expansion defect layer
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace Regression

theorem bkm_residual_curl_expansion_to_standard_equation_regression
    {ν T : ℝ} {u : NSVelocityField}
    (hCurl : vorticityResidualCurlEquationOn ν u T)
    (hExpand : residualCurlExpansionClosedOn ν u T) :
    concreteVorticityEquationOn ν u T :=
  concreteVorticityEquationOn_of_residualCurlExpansionClosedOn hCurl hExpand

theorem bkm_residual_curl_expansion_algebra_closed_regression :
    BKMResidualCurlExpansionAlgebraClosed :=
  BKMResidualCurlExpansionAlgebraClosed_proved

theorem finite_time_witness_standard_vorticity_equation_from_defect_regression
    (hDefect : BKMResidualCurlExpansionDefectVanishes)
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) :
    concreteVorticityEquationOn ν W.velocity T :=
  W.concreteVorticityEquationOn_of_residualCurlExpansionDefectVanishes hDefect

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
