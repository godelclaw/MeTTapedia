import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxHeatParity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousWorkCertificate

/-!
# The raw-flux obstruction does not obstruct the heat-integrated balance

The same admissible field has positive raw NS work and zero nonlinear
work in the heat-integrated functional. The latter retains its exact
viscous loss. Neither assertion says the parity condition persists.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousHeatComparison

open TwoShearViscousData StretchingFluxHorizontalParity StretchingFluxHeatParity
open StretchingFluxSpectralEvolution ExchangedFluxSeriesBudget StretchingFluxHeatWork

theorem raw_growth_and_zero_gram_work {ν : ℝ} (hν : 0 < ν) :
    0 < spectralRHSWork ν velocity ∧ fullGramWork ν velocity = 0 :=
  ⟨TwoShearViscousWorkCertificate.full_ns_work_pos ν hν,
    fullGramWork_eq_zero hν _ (all_moments 3) transverse reality twoShear_parity⟩

theorem material_heat_work_zero {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ) :
    materialHeatWork ν σ velocity = 0 :=
  materialHeatWork_eq_zero hν hσ _ (all_moments 3) transverse reality twoShear_parity

end Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousHeatComparison
