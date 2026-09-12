import Mettapedia.Analysis.WeightedCrossProductTests
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedAngularEvolution

/-! Weighted endpoint dynamics, source comparison, and a precise damping obstruction. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.Analysis Mettapedia.FluidDynamics.NavierStokes
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments

example (nu : ℝ) (hnu : 0 < nu) (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    |VorticityRegularizedSource.source 6 N u| ≤
      nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
        (24 * (PeriodicRieszNearMoment.firstMomentBound 3 + 1) / nu) *
          LocalWeightedAngularEvolution.symmetricAngularIntegral N u :=
  LocalWeightedAngularEvolution.abs_source_le_half_dissipation_add_symmetric nu hnu N u hu

example : EuclideanCrossProduct.angleRate WeightedCrossProductTests.strain WeightedCrossProductTests.strain
    WeightedCrossProductTests.leftVector WeightedCrossProductTests.rightVector 0 0 < 0 ∧
      0 < WeightedCrossProduct.rate 2 WeightedCrossProductTests.leftVector WeightedCrossProductTests.rightVector
        (WeightedCrossProductTests.strain WeightedCrossProductTests.leftVector)
        (WeightedCrossProductTests.strain WeightedCrossProductTests.rightVector) := by
  rw [WeightedCrossProductTests.angle_rate, WeightedCrossProductTests.energy_rate]
  norm_num

#print axioms WeightedCrossProduct.energy_nonneg
#print axioms WeightedCrossProduct.energy_swap
#print axioms WeightedCrossProduct.max_weight_le_energy
#print axioms WeightedCrossProduct.energy_le_two_max_weight
#print axioms WeightedCrossProduct.contDiff_energy
#print axioms WeightedCrossProduct.hasDerivAt_amplitudeWeight
#print axioms WeightedCrossProduct.hasDerivAt_energy
#print axioms WeightedCrossProduct.rate_eq_strain_add_perturbation
#print axioms WeightedCrossProduct.perturbationRate_common_zero
#print axioms WeightedCrossProduct.hasDerivAt_energy_strain
#print axioms WeightedCrossProductTests.strainMatrix_symmetric
#print axioms WeightedCrossProductTests.strainMatrix_trace
#print axioms WeightedCrossProductTests.energy_value
#print axioms WeightedCrossProductTests.energy_rate
#print axioms WeightedCrossProductTests.angle_rate
#print axioms WeightedCrossProductTests.growing_energy_firstVariation
#print axioms WeightedCrossProductTests.decreasing_angle_firstVariation
#print axioms WeightedCrossProductTests.not_weighted_damping_of_angle_damping
#print axioms TraceFreeWeightedAngularRate.weightedTopDefect_nonneg
#print axioms TraceFreeWeightedAngularRate.amplitudeRate_eq_growth_sub_defect
#print axioms TraceFreeWeightedAngularRate.strainRate_add_defect_le_growth
#print axioms TraceFreeWeightedAngularRate.growthWeight_common
#print axioms TraceFreeWeightedAngularRate.commonGrowthCoefficient_lower_bound
#print axioms TraceFreeWeightedAngularRate.commonGrowthCoefficient_eighth
#print axioms LocalWeightedAngularEvolution.continuous_pairEnergy
#print axioms LocalWeightedAngularEvolution.integrable_symmetricAngularDensity
#print axioms LocalWeightedAngularEvolution.angularIntegral_le_symmetric
#print axioms LocalWeightedAngularEvolution.symmetricAngularIntegral_le_two
#print axioms LocalWeightedAngularEvolution.abs_source_le_half_dissipation_add_symmetric
#print axioms LocalWeightedAngularEvolution.materialPairRate_add_defect_le_growth
#print axioms LocalWeightedAngularEvolution.hasDerivAt_pairEnergy_path
