import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSquaredGapGradient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GapCutoffRegularity

/-! Regression and axiom audit for the regularized spectral pressure weight. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SquaredGapPressureAudit

open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open SpectralGapTiltWeight

local notation "R3" => EuclideanSpace ℝ (Fin 3)

example : Real.sqrt (gapCutoff 1 (1 + 1 * (1 / 100 : ℝ) ^ 2)) = 1 / 100 :=
  GapCutoffRegularity.sqrt_gapCutoff_quadratic_increment 1 (by norm_num)
    (1 / 100) (by norm_num) (by norm_num)

/-- At a collision the refined weight vanishes, but the source cost does not. -/
example (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (h : topGap S = 0) :
    SquaredGapTiltWeight.weight 1 S w = 0 ∧
      SquaredGapTiltWeight.collisionCost 1 S R w = 2 * ‖R‖ * ‖w‖ ^ 2 := by
  norm_num [SquaredGapTiltWeight.weight, SquaredGapTiltWeight.amplitude,
    SquaredGapTiltWeight.collisionCost, gapCutoff, h]

/-- Away from the transition the usual inverse-gap weight is unchanged. -/
example (gamma : ℝ) (hg : 0 < gamma) (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (h : 2 * gamma ≤ topGap S) :
    SquaredGapTiltWeight.weight gamma S w = ‖w‖ ^ 2 / topGap S ^ 2 ∧
      SquaredGapTiltWeight.collisionCost gamma S R w = 0 := by
  have hc : gapCutoff gamma (topGap S) = 1 := by
    unfold gapCutoff
    have hr : 1 ≤ (topGap S - gamma) / gamma := (le_div_iff₀ hg).mpr (by linarith)
    rw [min_eq_left hr, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
  rw [SquaredGapTiltWeight.weight_eq gamma hg]
  simp [SquaredGapTiltWeight.collisionCost, hc]

/-- Halfway through the ramp, three quarters of the coarse cost is retained. -/
example (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (h : topGap S = 3 / 2) :
    SquaredGapTiltWeight.weight 1 S w = ‖w‖ ^ 2 / 9 ∧
      SquaredGapTiltWeight.collisionCost 1 S R w = (3 / 2 : ℝ) * ‖R‖ * ‖w‖ ^ 2 := by
  norm_num [SquaredGapTiltWeight.weight, SquaredGapTiltWeight.amplitude,
    SquaredGapTiltWeight.collisionCost, gapCutoff, h]
  constructor <;> ring

example (gamma : ℝ) (S : SymmetricStrain) :
    SquaredGapTiltWeight.weightedProjector gamma S 0 = 0 := by
  simp only [SquaredGapTiltWeight.weightedProjector, norm_zero]
  exact _root_.zero_smul ℝ (GapTruncatedProjector.inverseGapProjector gamma S)

end Mettapedia.FluidDynamics.NavierStokes.SquaredGapPressureAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.GapCutoffRegularity.gapCutoff_quadratic_increment
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapCutoffRegularity.sqrt_gapCutoff_quadratic_increment
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapCutoffRegularity.not_lipschitzWith_sqrt_gapCutoff
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector.abs_trace_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector.abs_topGap_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector.abs_gapCutoff_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector.norm_topEigenlineProjector
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector.norm_gatedProjector_le_one
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector.norm_gatedProjector_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector.norm_inverseGapProjector_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector.abs_inv_max_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector.norm_inverseGapProjector_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector.lipschitzWith_inverseGapProjector
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.weight_eq_cutoff_mul_tiltWeight
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.weight_le_tiltWeight
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.amplitude_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.sqrt_weight
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.weightedProjector_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.norm_weightedProjector_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.weighted_lineDistance_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.continuous_weightedProjector
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.locallyLipschitz_weightedProjector
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.norm_derivative_weightedProjector_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.continuous_weight
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.weight_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.collisionCost_eq_linear_add
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.collisionCost_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.excess_le_weighted_tilt_add_collision
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapPressure.continuous_localProjector
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapPressure.locallyLipschitz_localProjector
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapPressure.locallyLipschitz_localProjector_spaceTime
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapPressure.exists_pressure_angular_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapPressure.sourceExcess_le_weighted_jointTilt_add_collision
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapGradient.ae_coordinate_differentiable
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapGradient.norm_coordinateDerivative_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapGradient.gradientSquare_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapGradient.stronglyMeasurable_coordinateDerivative
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapGradient.continuous_fullCurlGradient
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapGradient.integrable_gradientSquare
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapGradient.integral_gradientSquare_le
