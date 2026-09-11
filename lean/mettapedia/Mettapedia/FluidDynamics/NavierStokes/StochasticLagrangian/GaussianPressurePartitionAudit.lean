import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalGaussianGradientBudget

/-! Dependency audit and scale checks for quantitative Gaussian pressure patches. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianPressurePartitionAudit

open AdaptiveGaussianLinePartition GaussianWeightedLinePartition

example (rho : ℝ) : temperature 1 rho = rho ^ 2 / 4 := by
  simp only [temperature, Nat.cast_one, Real.log_one, add_zero, mul_one]

/-- The radius cost is quadratic, while the cover cardinality is unchanged. -/
example (n : ℕ) (rho : ℝ) : temperature n (2 * rho) = 4 * temperature n rho := by
  unfold temperature
  ring

example (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1) : ‖coordinateProjector 0 e‖ = 0 :=
  norm_coordinateProjector 0 (le_refl 0) e he

end Mettapedia.FluidDynamics.NavierStokes.GaussianPressurePartitionAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianWeightedLinePartition.norm_coordinateProjector
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianWeightedLinePartition.sq_mul_lineDistanceSq_le_distance
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianWeightedLinePartition.sum_lineAmplitude_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianWeightedLinePartition.sum_lineAmplitude_sq_mul_lineDistanceSq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianWeightedLinePartition.sum_operator_path_deriv_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.AdaptiveGaussianLinePartition.exists_gaussian_line_partition
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressurePartition.localProjector_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressurePartition.patch_eq_lineAmplitude
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressurePartition.continuous_patch
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressurePartition.locallyLipschitz_patch
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressurePartition.ae_coordinate_differentiable_patch
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressurePartition.stronglyMeasurable_patchGradientSquare
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressurePartition.exists_local_gaussian_partition
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianGradientBudget.continuous_gradientDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianGradientBudget.exists_local_gaussian_gradient_budget
