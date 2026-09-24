import Mettapedia.Analysis.GaussianPartitionRegularity
import Mettapedia.Analysis.EuclideanOperatorCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-! Normalization, variance, zero-amplitude, and matrix-norm regressions. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.GaussianPartitionTests

open scoped BigOperators
open FiniteExponentialWeights GaussianPartitionEnergy EuclideanOperatorCoordinates

example : weight (fun _ : Fin 2 ↦ 0) 0 = 1 / 2 := by
  norm_num [weight, partition]

example : mean (fun _ : Fin 2 ↦ 0) ![1, -1] = 0 := by
  norm_num [mean, weight, partition, Fin.sum_univ_two]

/-- Opposite score rates attain the variance bound; the factor four is sharp. -/
example : (∑ i : Fin 2, amplitudeRate (fun _ ↦ 0) ![1, -1] i ^ 2) = 1 / 4 := by
  rw [sum_amplitudeRate_sq]
  norm_num [mean, weight, partition, Fin.sum_univ_two]

/-- Common score motion changes neither normalized amplitude. -/
example (s : Fin 7 → ℝ) (c : ℝ) :
    (∑ i, amplitudeRate s (fun _ ↦ c) i ^ 2) = 0 := by
  simp only [amplitudeRate_const, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]

example (s v : Fin 2 → ℝ) (c : ℝ) :
    (∑ i, amplitudeRate s (fun j ↦ v j + c) i ^ 2) = ∑ i, amplitudeRate s v i ^ 2 := by
  simp only [amplitudeRate_add_const]

/-- A zero-temperature singleton exposes the norm corner without an exponential denominator. -/
example : ¬ DifferentiableAt ℝ
    (fun s : ℝ ↦ normScaledAmplitude (fun _ : Fin 1 ↦ (0 : ℝ)) 0 s 0) 0 := by
  simpa [normScaledAmplitude, gaussianAmplitude, score, amplitude, partition] using
    (not_differentiableAt_norm_zero ℝ)

/-- At that corner the total derivative is zero, not a proof of differentiability. -/
example : deriv (fun s : ℝ ↦ normScaledAmplitude (fun _ : Fin 1 ↦ (0 : ℝ)) 0 s 0) 0 = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro s
  simp only [normScaledAmplitude, norm_zero, zero_mul]
  exact mul_nonneg (norm_nonneg _) (amplitude_pos _ _).le

/-- The identity attains the dimension factor in the Hilbert/operator comparison. -/
example : ‖coordinates (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)))‖ ^ 2 = 3 := by
  rw [norm_coordinates_sq]
  simp only [ContinuousLinearMap.id_apply, (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one,
    one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_ofNat]

end Mettapedia.Analysis.GaussianPartitionTests

#print axioms Mettapedia.Analysis.FiniteExponentialWeights.sum_weight
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.sum_amplitude_sq
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.mean_const
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.mean_add_const
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.neg_sum_mul_log_le
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.mean_score_ge
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.mean_cost_le
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.amplitudeRate_const
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.amplitudeRate_add_const
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.hasDerivAt_amplitude
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.sum_amplitude_mul_rate
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.sum_amplitudeRate_sq
#print axioms Mettapedia.Analysis.FiniteExponentialWeights.sum_scaled_amplitudeRate_sq
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.sum_gaussianAmplitude_sq
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.distanceMoment_le
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.hasDerivAt_gaussianAmplitude
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.sum_amplitudeRate_sq_le_moment
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.sum_scaled_deriv_sq_le
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.sum_normScaledAmplitude_sq
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.deriv_norm_sq_le
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.sum_normScaled_deriv_sq_le_moment
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.sum_normScaled_deriv_sq_le
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.contDiff_gaussianAmplitude
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.locallyLipschitz_normScaledAmplitude
#print axioms Mettapedia.Analysis.EuclideanOperatorCoordinates.norm_coordinates_sq
#print axioms Mettapedia.Analysis.EuclideanOperatorCoordinates.norm_le_coordinates
#print axioms Mettapedia.Analysis.EuclideanOperatorCoordinates.norm_coordinates_sq_le
#print axioms Mettapedia.Analysis.EuclideanOperatorCoordinates.norm_coordinates_rankOne
