import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearStretchingMean

/-! Initial-jet checks: full momentum balance and positive mean stretching production. -/

open Mettapedia.FluidDynamics.NavierStokes

example (ν : ℝ) :
    (∀ x, timeVelocityDerivative (TwoShearStretchingJet.velocity ν) 0 x +
        spatialConvection (TwoShearStretchingJet.velocity ν) 0 x +
        spatialPressureGradient (0 : NSPressureField) 0 x =
      ν • spatialLaplacian (TwoShearStretchingJet.velocity ν) 0 x) ∧
    TwoShearStretchingMean.meanStretching ν 0 = 0 ∧
    0 < deriv (TwoShearStretchingMean.meanStretching ν) 0 :=
  ⟨TwoShearStretchingJet.momentum_equation_zero ν,
    TwoShearStretchingMean.meanStretching_zero ν,
    TwoShearStretchingMean.initial_mean_rate_pos ν⟩

example (ν b : ℝ) :
    ¬ deriv (TwoShearStretchingMean.meanStretching ν) 0 ≤
      b * TwoShearStretchingMean.meanStretching ν 0 :=
  TwoShearStretchingMean.not_initial_mean_multiplicative_damping ν b

#print axioms TwoShearStretchingJet.hasFDerivAt_velocity
#print axioms TwoShearStretchingJet.velocity_divergence_zero
#print axioms TwoShearStretchingJet.velocity_periodic
#print axioms TwoShearStretchingJet.contDiff_velocity
#print axioms TwoShearStretchingJet.smoothSpaceTimeVelocity_velocity
#print axioms TwoShearStretchingJet.spatialVorticity_velocity
#print axioms TwoShearStretchingJet.hasDerivAt_velocity
#print axioms TwoShearStretchingJet.spatialLaplacian_velocity_zero
#print axioms TwoShearStretchingJet.momentum_equation_zero
#print axioms TwoShearStretchingJet.norm_spatialVorticity_sq
#print axioms TwoShearStretchingJet.stretching_power
#print axioms TwoShearStretchingJet.eighthStretchingDensity_eq
#print axioms TwoShearStretchingJet.eighthStretchingDensity_zero
#print axioms TwoShearStretchingJet.hasDerivAt_eighthStretchingDensity_zero
#print axioms TwoShearStretchingJet.initial_density_rate_nonneg
#print axioms TwoShearStretchingJet.initial_density_rate_origin
#print axioms TwoShearStretchingJet.not_initial_multiplicative_damping
#print axioms PancakePeriodicMean.continuous_circleMean
#print axioms PancakePeriodicMean.continuous_spatialMean
#print axioms PancakePeriodicMean.circleMean_cos_pow_add_two
#print axioms PancakePeriodicMean.circleMean_cos_pow_four
#print axioms PancakePeriodicMean.circleMean_cos_pow_six
#print axioms PancakePeriodicMean.circleMean_cos_pow_eight
#print axioms PancakePeriodicMean.spatialMean_add
#print axioms TwoShearStretchingMean.meanStretching_zero
#print axioms TwoShearStretchingMean.hasDerivAt_meanStretching_zero
#print axioms TwoShearStretchingMean.initial_mean_rate
#print axioms TwoShearStretchingMean.initial_mean_rate_pos
#print axioms TwoShearStretchingMean.not_initial_mean_multiplicative_damping
