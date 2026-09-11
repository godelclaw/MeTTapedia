import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootTwoPointDerivative

/-! Checks for the actual two-point weak-derivative bound. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointAudit

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail LocalLowDiffusionBudget
open GaussianRootWeakChannelBudget GaussianRootTwoPointDerivative

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (j : Fin 3) (y z : T3)
    (hz : fullVorticity u z = 0) : twoPointDerivativeDensity gamma chi modes u centers tau j y z = 0 := by
  simp [twoPointDerivativeDensity, hz]

example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (j : Fin 3) (y z : T3)
    (hy : fullVorticity u y = 0) : twoPointBudget gamma chi modes u centers tau j y z = 0 := by
  simp [twoPointBudget, hy]

/-- One null set works for every partner point, not just a preselected one. -/
example (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (ht : 0 < tau) (j : Fin 3) :
    ∀ᵐ y : T3, ∀ z : T3, ∀ k : ↑centers,
      twoPointDerivativeDensity gamma chi modes u centers tau j y z ≤
        localizedTwoPointBudget gamma chi modes u centers tau j k y z :=
  ae_twoPointDerivativeDensity_le_localized gamma hg chi modes u hu centers hc tau ht j

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointAudit

#print axioms Mettapedia.Analysis.FiniteExponentialWeights.amplitudeOverlap_self
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.amplitudeOverlap_nonneg
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.amplitudeOverlap_le_one
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.partition_add_const
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.weight_add_const
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.amplitude_mul_eq_overlap_mul_weight
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.amplitude_mul_le_weight_average
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.sum_amplitude_mul_cost_le_mean_average
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.sq_mean_le_mean_sq
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.sum_amplitude_mul_centered_sq_le
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.sum_amplitude_mul_affine_centered_sq_le
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.norm_sub_midpoint_identity
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.score_average_eq_midpoint
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.gaussianAmplitude_mul_le_midpoint_weight
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.sum_gaussianAmplitude_mul_le_one
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.sum_gaussianAmplitude_mul_cost_le_midpoint_mean
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.mean_shifted_distance_sq_le
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.mean_scoreRate_sq_le
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.twoPointDistanceMoment_nonneg
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.mean_scoreRate_sq_average_add_le
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.twoPointDistanceMoment_le
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.twoPointDistanceMoment_le_separation
#print axioms Mettapedia.Analysis.RootPartitionEnergy.deriv_rootAmplitude_eq
#print axioms Mettapedia.Analysis.RootPartitionEnergy.sum_rootAmplitude_sq_mul_sq_le
#print axioms Mettapedia.Analysis.RootPartitionEnergy.sum_rootAmplitude_sq_mul_deriv_sq_le
#print axioms Mettapedia.Analysis.RootPartitionEnergy.sum_twoPoint_rootVorticity_deriv_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointDerivative.ae_twoPointDerivativeDensity_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointDerivative.twoPointBudget_le_localized
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointDerivative.ae_twoPointDerivativeDensity_le_localized
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointDerivative.ae_translated_twoPointDerivativeDensity_le
