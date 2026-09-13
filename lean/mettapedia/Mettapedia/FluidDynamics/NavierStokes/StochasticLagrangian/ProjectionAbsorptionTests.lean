import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionAbsorption

/-! # Zero-radius and sign regression tests for projection absorption -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ProjectionAbsorptionTests

open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open LocalProjectionCurvatureBudget LocalVorticityEighthMoment FiniteBandProjectionAbsorption

theorem normalization_zero : normalization 0 = 1 := by simp [normalization]

theorem curvatureCost_zero_radius (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ 0) :
    curvatureCost u = 0 := by
  have h := curvatureCost_le P u hs 0 hP
  norm_num at h
  exact le_antisymm h (curvatureCost_nonneg u)

/-- The absorbing right-hand side has the dissipative sign. -/
theorem absorbed_rhs_nonpos (ν : ℝ) (hν : 0 ≤ ν) (u : FourierVelocity) :
    -(3 * ν / 4) * weightedPalinstrophy u - 6 * ν * radialDissipation u ≤ 0 := by
  have hG := mul_nonneg (show 0 ≤ 3 * ν / 4 by positivity) (weightedPalinstrophy_nonneg u)
  have hR := mul_nonneg (show 0 ≤ 6 * ν by positivity) (radialDissipation_nonneg u)
  linarith only [hG, hR]

end Mettapedia.FluidDynamics.NavierStokes.ProjectionAbsorptionTests
