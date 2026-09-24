import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalTiltAlignmentEnergy

/-! Regression and axiom audit for the physical direct-tilt source budget. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalTiltSourceAudit

open scoped RealInnerProductSpace
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeAnisotropyDepletion SpectralTiltExcess

local notation "R3" => EuclideanSpace ℝ (Fin 3)

example (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    excess S R w ≤ SpectralSourceExcess.excess S R w := excess_le_previous S R w

example (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (hg : topGap S = 0) :
    excess S R w = 2 * ‖R‖ * ‖w‖ ^ 2 := excess_eq_coarse_of_topGap_zero S R w hg

example (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (c : ℝ) (hg : 0 < topGap S) :
    excess S R (c • topVector S) = 0 := excess_aligned S R c hg

example (S : SymmetricStrain) (w : R3) : excess S 0 w = 0 := by
  exact le_antisymm (by simpa using excess_le_coarse S 0 w) (excess_nonneg S 0 w)

example (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (c : ℝ)
    (he : R (topVector S) = c • topVector S) : tiltNorm S R = 0 := by
  rw [tiltNorm_eq, he]
  simp only [lineRemainder, real_inner_smul_right, real_inner_self_eq_norm_sq,
    topVector_norm, one_pow, mul_one, sub_self, norm_zero]

/-- A nonzero transverse-plane commutator need not tilt the selected line.
These are operators, not an independently prescribed physical pressure. -/
example :
    let e := (EuclideanSpace.basisFun (Fin 3) ℝ) 0
    let f := (EuclideanSpace.basisFun (Fin 3) ℝ) 1
    let g := (EuclideanSpace.basisFun (Fin 3) ℝ) 2
    let P := InnerProductSpace.rankOne ℝ e e
    let S := P - InnerProductSpace.rankOne ℝ g g
    let H := InnerProductSpace.rankOne ℝ (f + g) (f + g)
    ‖(ContinuousLinearMap.id ℝ R3 - P) * H * P‖ = 0 ∧ ‖(S * H - H * S) f‖ = 1 := by
  dsimp only
  rw [LineProjectorTilt.norm_transverse_projector_action _ _
    ((EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0)]
  simp [lineRemainder, sub_apply, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
    inner_add_right, EuclideanSpace.inner_single_right]

end Mettapedia.FluidDynamics.NavierStokes.LocalTiltSourceAudit

#print axioms intervalIntegral.endpoint_estimate_of_interior_of_integrable
#print axioms intervalIntegral.endpoint_estimate_of_interior
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.tiltNorm_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.tiltNorm_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.refinedCost_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.excess_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.excess_le_previous
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.excess_le_coarse
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.abs_anisotropy_le_tilt_cost
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.tilt_cost_le_eighth_residual_add
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.abs_anisotropy_le_quarter_residual_add_refinedCost
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.abs_anisotropy_le_quarter_residual_add_excess
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.excess_eq_coarse_of_topGap_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.excess_aligned
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.excess_eq_zero_of_tiltNorm_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess.measurable_excess
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.sourceExcess_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.sourceExcess_le_previous
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.sourceExcess_le_coarse
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.sourceExcess_le_jointTilt_cost
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.forcingEnvelope_le_previous
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.materialRate_add_threeQuarters_residual_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.norm_forcingEnvelope_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.measurable_sourceExcess
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.measurable_forcingEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.integrable_forcingEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.measurable_forcingEnvelope_spaceTime
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.intervalIntegrable_forcingEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource.integral_materialRate_add_quarter_residual_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltAlignmentEnergy.integral_budgetSource_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltAlignmentEnergy.intervalIntegrable_budgetSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltAlignmentEnergy.meanEnergy_add_quarter_integral_residual_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltAlignmentEnergy.meanEnergy_add_quarter_integral_residual_le_initial
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalTiltAlignmentEnergy.exists_physical_localTiltAlignmentEnergy
