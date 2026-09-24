import Mettapedia.Analysis.ExponentialAmplitudeOverlap
import Mettapedia.Analysis.GaussianPartitionEnergy

/-!
# Gaussian amplitude overlap at two points

The geometric mean of normalized Gaussian weights is dominated by the
normalized Gaussian weight at the midpoint. The common score offset
cancels exactly. Shifted second moments retain an explicit separation
cost; no pointwise comparison to either endpoint weight is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.GaussianPartitionEnergy

open scoped BigOperators
open FiniteExponentialWeights

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sub_midpoint_identity (x z c : E) :
    (‖x - c‖ ^ 2 + ‖z - c‖ ^ 2) / 2 =
      ‖(1 / 2 : ℝ) • (x + z) - c‖ ^ 2 + ‖x - z‖ ^ 2 / 4 := by
  have hm : (1 / 2 : ℝ) • (x + z) - c = (1 / 2 : ℝ) • ((x - c) + (z - c)) := by module
  have hd : (x - c) - (z - c) = x - z := by abel
  have h := parallelogram_law_with_norm ℝ (x - c) (z - c)
  rw [hd] at h
  rw [hm, norm_smul, mul_pow]
  norm_num
  linarith only [h]

omit [Fintype ι] [Nonempty ι] in
theorem score_average_eq_midpoint (center : ι → E) (tau : ℝ) (x z : E) (i : ι) :
    (score center tau x i + score center tau z i) / 2 =
      score center tau ((1 / 2 : ℝ) • (x + z)) i - ‖x - z‖ ^ 2 / (4 * tau) := by
  have h := norm_sub_midpoint_identity x z (center i)
  unfold score
  calc
    _ = -((‖x - center i‖ ^ 2 + ‖z - center i‖ ^ 2) / 2) / tau := by ring
    _ = _ := by rw [h]; ring

theorem gaussianAmplitude_mul_le_midpoint_weight (center : ι → E) (tau : ℝ) (x z : E) (i : ι) :
    gaussianAmplitude center tau x i * gaussianAmplitude center tau z i ≤
      weight (score center tau ((1 / 2 : ℝ) • (x + z))) i := by
  have h := amplitude_mul_le_weight_average (score center tau x) (score center tau z) i
  simp_rw [score_average_eq_midpoint, sub_eq_add_neg, weight_add_const] at h
  exact h

omit [InnerProductSpace ℝ E] in
theorem sum_gaussianAmplitude_mul_le_one (center : ι → E) (tau : ℝ) (x z : E) :
    (∑ i, gaussianAmplitude center tau x i * gaussianAmplitude center tau z i) ≤ 1 :=
  amplitudeOverlap_le_one _ _

theorem sum_gaussianAmplitude_mul_cost_le_midpoint_mean
    (center : ι → E) (tau : ℝ) (x z : E) (cost : ι → ℝ) (hc : ∀ i, 0 ≤ cost i) :
    (∑ i, gaussianAmplitude center tau x i * gaussianAmplitude center tau z i * cost i) ≤
      mean (score center tau ((1 / 2 : ℝ) • (x + z))) cost :=
  Finset.sum_le_sum (fun i _ ↦
    mul_le_mul_of_nonneg_right (gaussianAmplitude_mul_le_midpoint_weight center tau x z i) (hc i))

omit [InnerProductSpace ℝ E] in
theorem mean_shifted_distance_sq_le (center : ι → E) (tau : ℝ) (x z : E) :
    mean (score center tau z) (fun i ↦ ‖x - center i‖ ^ 2) ≤
      2 * distanceMoment center tau z + 2 * ‖x - z‖ ^ 2 := by
  have hp (i : ι) : ‖x - center i‖ ^ 2 ≤ 2 * ‖z - center i‖ ^ 2 + 2 * ‖x - z‖ ^ 2 := by
    have hn : ‖x - center i‖ ≤ ‖x - z‖ + ‖z - center i‖ := by
      simpa only [dist_eq_norm] using dist_triangle x z (center i)
    have h := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith only [h, sq_nonneg (‖x - z‖ - ‖z - center i‖)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    mul_le_mul_of_nonneg_left (hp i) (weight_pos (score center tau z) i).le)
  apply h.trans_eq
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_weight, one_mul]
  congr 1
  unfold distanceMoment mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mean_scoreRate_sq_le (center : ι → E) (tau : ℝ) (x z v : E) :
    mean (score center tau z) (fun i ↦ scoreRate center tau x v i ^ 2) ≤
      4 / tau ^ 2 * ‖v‖ ^ 2 * mean (score center tau z) (fun i ↦ ‖x - center i‖ ^ 2) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    mul_le_mul_of_nonneg_left (scoreRate_sq_le center tau x v i) (weight_pos (score center tau z) i).le)
  apply h.trans_eq
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def twoPointDistanceMoment (center : ι → E) (tau : ℝ) (x z : E) : ℝ :=
  distanceMoment center tau x +
    2 * distanceMoment center tau ((1 / 2 : ℝ) • (x + z)) +
    2 * ‖x - (1 / 2 : ℝ) • (x + z)‖ ^ 2

theorem twoPointDistanceMoment_nonneg (center : ι → E) (tau : ℝ) (x z : E) :
    0 ≤ twoPointDistanceMoment center tau x z := by
  have hd (y : E) : 0 ≤ distanceMoment center tau y :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (weight_pos _ i).le (sq_nonneg _))
  unfold twoPointDistanceMoment
  exact add_nonneg (add_nonneg (hd x) (mul_nonneg (by norm_num) (hd _)))
    (mul_nonneg (by norm_num) (sq_nonneg _))

theorem mean_scoreRate_sq_average_add_le (center : ι → E) (tau : ℝ) (x z v : E) :
    mean (fun i ↦ (score center tau x i + score center tau z i) / 2)
        (fun i ↦ scoreRate center tau x v i ^ 2) +
      mean (score center tau x) (fun i ↦ scoreRate center tau x v i ^ 2) ≤
        4 / tau ^ 2 * ‖v‖ ^ 2 * twoPointDistanceMoment center tau x z := by
  have he : mean (fun i ↦ (score center tau x i + score center tau z i) / 2)
      (fun i ↦ scoreRate center tau x v i ^ 2) =
      mean (score center tau ((1 / 2 : ℝ) • (x + z))) (fun i ↦ scoreRate center tau x v i ^ 2) := by
    simp only [mean]
    simp_rw [score_average_eq_midpoint, sub_eq_add_neg, weight_add_const]
  rw [he]
  have h0 := mean_scoreRate_sq_le center tau x x v
  have h1 := (mean_scoreRate_sq_le center tau x ((1 / 2 : ℝ) • (x + z)) v).trans
    (mul_le_mul_of_nonneg_left (mean_shifted_distance_sq_le center tau x ((1 / 2 : ℝ) • (x + z)))
      (show 0 ≤ 4 / tau ^ 2 * ‖v‖ ^ 2 by positivity))
  have h := add_le_add h1 h0
  exact h.trans_eq (by unfold twoPointDistanceMoment distanceMoment; ring)

theorem twoPointDistanceMoment_le (center : ι → E) (tau : ℝ) (ht : 0 < tau) (x z : E) (j : ι) :
    twoPointDistanceMoment center tau x z ≤
      2 * ‖x - center j‖ ^ 2 + ‖z - center j‖ ^ 2 + 3 * tau * Real.log (Fintype.card ι) := by
  have h0 := distanceMoment_le center tau ht x j
  have h1 := distanceMoment_le center tau ht ((1 / 2 : ℝ) • (x + z)) j
  have h2 := norm_sub_midpoint_identity x z (center j)
  have hm : x - (1 / 2 : ℝ) • (x + z) = (1 / 2 : ℝ) • (x - z) := by module
  unfold twoPointDistanceMoment
  rw [hm, norm_smul, mul_pow]
  norm_num at h0 h1 h2 ⊢
  linarith only [h0, h1, h2]

/-- A centre chosen near the derivative point incurs only the explicit
separation of the two points in the remaining distance cost. -/
theorem twoPointDistanceMoment_le_separation (center : ι → E) (tau : ℝ) (ht : 0 < tau)
    (x z : E) (j : ι) :
    twoPointDistanceMoment center tau x z ≤
      4 * ‖x - center j‖ ^ 2 + 2 * ‖x - z‖ ^ 2 + 3 * tau * Real.log (Fintype.card ι) := by
  have hn : ‖z - center j‖ ≤ ‖x - z‖ + ‖x - center j‖ := by
    simpa only [dist_eq_norm, norm_sub_rev z x] using dist_triangle z x (center j)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h := twoPointDistanceMoment_le center tau ht x z j
  nlinarith only [h, hs, sq_nonneg (‖x - z‖ - ‖x - center j‖)]

end Mettapedia.Analysis.GaussianPartitionEnergy
