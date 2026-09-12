import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalCoherenceBudget

/-! Checks separating unconditional source payment from conditional coherence. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.Analysis Mettapedia.FluidDynamics.NavierStokes
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments

example : ∃ C ≥ (0 : ℝ), ∀ N (h : UnitAddTorus (Fin 3)),
    ‖h‖ ^ 3 * ‖PeriodicRieszOperator.kernel N h‖ ≤ C :=
  PeriodicRieszSingularity.exists_uniform_operator_bound

example (nu : ℝ) (hnu : 0 < nu) (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    |VorticityRegularizedSource.source 6 N u| ≤
      nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
        (24 * (PeriodicRieszNearMoment.firstMomentBound 3 + 1) / nu) *
          VorticityAngularPayment.angularIntegral N u :=
  VorticityAngularPayment.abs_source_le_half_dissipation_add_angular nu hnu N u hu

example (nu : ℝ) (hnu : 0 < nu) :
    ∃ C ≥ (0 : ℝ), ∀ K N u, Summable (fourierMoment 3 u) →
      VorticityCoherenceBudget.ProjectiveLipschitz u K →
      |VorticityRegularizedSource.source 6 N u| ≤
        nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
          (C * K ^ 2 / nu * InfiniteConvectionEnergy.kineticEnergy
            (PancakeGalerkinKineticEnergy.fourierCurl u)) * LocalVorticityEighthMoment.meanEnergy u :=
  VorticityCoherenceBudget.exists_uniform_source_bound nu hnu

#print axioms SchwartzDyadicDecay.pow_mul_norm_le_transition
#print axioms SchwartzDyadicDecay.pow_mul_norm_sum_dilate_le
#print axioms AnnularRieszKernel.dimension_pow_mul_norm_partialKernel_le
#print axioms PeriodicRieszSingularity.exists_uniform_entry_bound
#print axioms PeriodicRieszSingularity.exists_uniform_operator_bound
#print axioms SignedCrossKernel.abs_pairedStretch_le_increment_add_angular
#print axioms SignedCrossKernel.angularCost_le_of_cross_bound
#print axioms VorticityAngularPayment.inverseDistanceIncrement_nonneg
#print axioms VorticityAngularPayment.angularIntegral_nonneg
#print axioms VorticityAngularPayment.inverseDistanceIncrement_density_le
#print axioms VorticityAngularPayment.integrable_inverseDistanceIncrement
#print axioms VorticityAngularPayment.inverseDistanceIncrement_le
#print axioms VorticityAngularPayment.integrable_angularDensity
#print axioms VorticityAngularPayment.integrable_pairedDensity
#print axioms VorticityAngularPayment.source_eq_displacement
#print axioms VorticityAngularPayment.abs_source_le_increment_add_angular
#print axioms VorticityAngularPayment.angularAbsorptionScale_pos
#print axioms VorticityAngularPayment.abs_source_le_half_dissipation_add_angular
#print axioms VorticityCoherenceBudget.angularIntegral_le_of_projectiveLipschitz
#print axioms VorticityCoherenceBudget.exists_uniform_source_bound
#print axioms VorticityCoherenceBudget.exists_stretching_bound
#print axioms LocalCoherenceBudget.growthCoefficient_nonneg
#print axioms LocalCoherenceBudget.continuousOn_growthCoefficient
#print axioms LocalCoherenceBudget.integral_growthCoefficient_le
#print axioms LocalCoherenceBudget.exists_source_growth_budget
#print axioms LocalCoherenceBudget.exists_energy_growth_budget
