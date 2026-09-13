import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LowStrainResidualIntegral

/-!
# Low-strain payment dependency audit

The empty-source tests ensure that paying no low modes leaves the
integrating factor equal to one. The scalar test retains a negative
residual, rather than replacing it by its absolute value.
-/

open Mettapedia.FluidDynamics.NavierStokes
open FiniteStrainKineticEnergy FiniteLowStrainWork LowStrainResidualIntegral

example (E : ℝ) : lowStrainGrowthCoefficient ∅ E = 0 := by
  simp [lowStrainGrowthCoefficient, strainEnergyBound, strainGradientEnergyBound]

example (E t : ℝ) : lowStrainIntegratingFactor ∅ E t = 1 := by
  simp [lowStrainIntegratingFactor, lowStrainGrowthCoefficient,
    strainEnergyBound, strainGradientEnergyBound]

example (t : ℝ) (ht : 0 ≤ t) : -t ≤ ∫ _τ in (0 : ℝ)..t, (-1 : ℝ) := by
  have h := Mettapedia.Analysis.ODE.exp_mul_add_integral_le_of_deriv_le ht 0
    (F := fun τ ↦ -τ) (F' := fun _ ↦ -1) (D := fun _ ↦ 0) (W := fun _ ↦ -1)
    continuous_id.neg.continuousOn continuous_const.continuousOn continuous_const.continuousOn
    (fun τ _ ↦ hasDerivAt_neg' τ)
    (fun _ _ ↦ by norm_num)
  simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul,
    intervalIntegral.integral_zero, add_zero, zero_add] using h

#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteStrainKineticEnergy.strainWeight
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteStrainKineticEnergy.strainEnergyBound
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteStrainKineticEnergy.strainGradientEnergyBound
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteStrainKineticEnergy.strainEnergyBound_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteStrainKineticEnergy.strainGradientEnergyBound_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteStrainKineticEnergy.sum_weight_norm_le_sqrt_kineticEnergy
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteStrainKineticEnergy.norm_spatialStrain_le_weighted_sum
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteStrainKineticEnergy.norm_spatialStrain_le_energyBound
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteStrainKineticEnergy.norm_strainGradient_le_energyBound
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.lowStrainSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.lowStrainSourceDerivative
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.lowStrainWork
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.lowStrainGrowthCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.lowStrainGrowthCoefficient_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.continuous_lowStrainSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.continuous_lowStrainSourceDerivative
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.hasDerivAt_lowStrainSource_shift
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.norm_lowStrainSource_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.norm_lowStrainSourceDerivative_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.abs_lowStrainWork_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.abs_lowStrainWork_solution_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.residualStrainSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.residualStrainSubgridWork
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork.strainSubgridWork_eq_low_add_residual
#print axioms Mettapedia.FluidDynamics.NavierStokes.LowStrainAngularBalance.continuous_correctedGradient_parametric
#print axioms Mettapedia.FluidDynamics.NavierStokes.LowStrainAngularBalance.continuousOn_lowStrainWork
#print axioms Mettapedia.FluidDynamics.NavierStokes.LowStrainAngularBalance.continuousOn_residualStrainSubgridWork
#print axioms Mettapedia.FluidDynamics.NavierStokes.LowStrainAngularBalance.exists_residual_differential_inequality
#print axioms Mettapedia.FluidDynamics.NavierStokes.LowStrainResidualIntegral.lowStrainIntegratingFactor
#print axioms Mettapedia.FluidDynamics.NavierStokes.LowStrainResidualIntegral.lowStrainIntegratingFactor_pos
#print axioms Mettapedia.FluidDynamics.NavierStokes.LowStrainResidualIntegral.exists_initial_residual_inequality
#print axioms Mettapedia.FluidDynamics.NavierStokes.LowStrainResidualIntegral.exists_physical_local_initial_residual_inequality
#print axioms Mettapedia.Analysis.ODE.exp_mul_add_integral_le_of_deriv_le
