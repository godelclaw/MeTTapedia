import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityEquation

/-!
# Regression checks for the BKM vorticity-equation surface
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace Regression

theorem finite_time_witness_vorticity_residual_curl_equation_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) :
    vorticityResidualCurlEquationOn ν W.velocity T :=
  W.vorticityResidualCurlEquationOn

theorem finite_time_witness_bkm_data_vorticity_residual_packet_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hBKM : ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn W.velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B) :
    vorticityResidualCurlEquationOn ν W.velocity T ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialVorticity (momentumPressureResidual ν W.velocity) t x = 0) :=
  finiteTimeWitness_BKMData_vorticityResidualCurl_packet W hBKM

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
