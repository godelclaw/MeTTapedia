import Mettapedia.Analysis.ExponentialAmplitudeDerivative

/-!
# Overlap of normalized exponential amplitudes

The product of two amplitudes is their total overlap times the normalized
weight at the average score. The overlap is at most one. Nonnegative
cross-weighted costs can therefore be bounded at the average score,
without comparing individual weights by a worst-case ratio.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteExponentialWeights

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def amplitudeOverlap (s r : ι → ℝ) : ℝ := ∑ i, amplitude s i * amplitude r i

theorem amplitudeOverlap_self (s : ι → ℝ) : amplitudeOverlap s s = 1 := by
  simpa only [amplitudeOverlap, ← sq] using sum_amplitude_sq s

theorem amplitudeOverlap_nonneg (s r : ι → ℝ) : 0 ≤ amplitudeOverlap s r :=
  Finset.sum_nonneg (fun i _ ↦ mul_nonneg (amplitude_pos s i).le (amplitude_pos r i).le)

theorem amplitudeOverlap_le_one (s r : ι → ℝ) : amplitudeOverlap s r ≤ 1 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    show 2 * (amplitude s i * amplitude r i) ≤ amplitude s i ^ 2 + amplitude r i ^ 2 by
      nlinarith only [sq_nonneg (amplitude s i - amplitude r i)])
  rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_amplitude_sq, sum_amplitude_sq] at h
  unfold amplitudeOverlap
  linarith only [h]

omit [Nonempty ι] in
theorem partition_add_const (s : ι → ℝ) (c : ℝ) :
    partition (fun i ↦ s i + c) = partition s * Real.exp c := by
  simp only [partition, Real.exp_add, Finset.sum_mul]

omit [Nonempty ι] in
theorem weight_add_const (s : ι → ℝ) (c : ℝ) (i : ι) :
    weight (fun j ↦ s j + c) i = weight s i := by
  rw [weight, partition_add_const, Real.exp_add, weight]
  exact mul_div_mul_right _ _ (ne_of_gt (Real.exp_pos c))

theorem amplitude_mul_eq_overlap_mul_weight (s r : ι → ℝ) (i : ι) :
    amplitude s i * amplitude r i =
      amplitudeOverlap s r * weight (fun j ↦ (s j + r j) / 2) i := by
  let m : ι → ℝ := fun j ↦ (s j + r j) / 2
  have he (j : ι) : amplitude s j * amplitude r j =
      Real.exp (m j) / (Real.sqrt (partition s) * Real.sqrt (partition r)) := by
    simp only [amplitude, div_mul_div_comm, ← Real.exp_add]
    congr 2
    dsimp [m]
    ring
  have ho : amplitudeOverlap s r =
      partition m / (Real.sqrt (partition s) * Real.sqrt (partition r)) := by
    simp only [amplitudeOverlap, he, ← Finset.sum_div, partition]
  rw [he, ho]
  change _ = _ * (Real.exp (m i) / partition m)
  field_simp [ne_of_gt (partition_pos m)]

theorem amplitude_mul_le_weight_average (s r : ι → ℝ) (i : ι) :
    amplitude s i * amplitude r i ≤ weight (fun j ↦ (s j + r j) / 2) i := by
  rw [amplitude_mul_eq_overlap_mul_weight]
  exact mul_le_of_le_one_left (weight_pos _ i).le (amplitudeOverlap_le_one s r)

theorem sum_amplitude_mul_cost_le_mean_average (s r cost : ι → ℝ) (hc : ∀ i, 0 ≤ cost i) :
    (∑ i, amplitude s i * amplitude r i * cost i) ≤ mean (fun j ↦ (s j + r j) / 2) cost :=
  Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right (amplitude_mul_le_weight_average s r i) (hc i))

theorem sq_mean_le_mean_sq (s v : ι → ℝ) :
    mean s v ^ 2 ≤ mean s (fun i ↦ v i ^ 2) := by
  have h : 0 ≤ ∑ i, amplitudeRate s v i ^ 2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  rw [sum_amplitudeRate_sq] at h
  linarith only [h]

theorem sum_amplitude_mul_centered_sq_le (s r v : ι → ℝ) :
    (∑ i, amplitude s i * amplitude r i * (v i - mean s v) ^ 2) ≤
      2 * (mean (fun j ↦ (s j + r j) / 2) (fun i ↦ v i ^ 2) +
        mean s (fun i ↦ v i ^ 2)) := by
  have h1 := sum_amplitude_mul_cost_le_mean_average s r
    (fun i ↦ (v i - mean s v) ^ 2) (fun _ ↦ sq_nonneg _)
  have h2 := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    mul_le_mul_of_nonneg_left
      (show (v i - mean s v) ^ 2 ≤ 2 * v i ^ 2 + 2 * mean s v ^ 2 by
        nlinarith only [sq_nonneg (v i + mean s v)])
      (weight_pos (fun j ↦ (s j + r j) / 2) i).le)
  have he : mean (fun j ↦ (s j + r j) / 2)
      (fun i ↦ 2 * v i ^ 2 + 2 * mean s v ^ 2) =
      2 * mean (fun j ↦ (s j + r j) / 2) (fun i ↦ v i ^ 2) + 2 * mean s v ^ 2 := by
    simp only [mean, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_weight, one_mul]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  change mean _ _ ≤ mean _ _ at h2
  rw [he] at h2
  have h3 := sq_mean_le_mean_sq s v
  linarith only [h1, h2, h3]

theorem sum_amplitude_mul_affine_centered_sq_le (s r v : ι → ℝ) (a b : ℝ) :
    (∑ i, amplitude s i * amplitude r i * (a + b * (v i - mean s v)) ^ 2) ≤
      2 * a ^ 2 + 4 * b ^ 2 *
        (mean (fun j ↦ (s j + r j) / 2) (fun i ↦ v i ^ 2) + mean s (fun i ↦ v i ^ 2)) := by
  have hp (i : ι) : amplitude s i * amplitude r i * (a + b * (v i - mean s v)) ^ 2 ≤
      2 * a ^ 2 * (amplitude s i * amplitude r i) +
        2 * b ^ 2 * (amplitude s i * amplitude r i * (v i - mean s v) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left
      (show (a + b * (v i - mean s v)) ^ 2 ≤ 2 * a ^ 2 + 2 * (b * (v i - mean s v)) ^ 2 by
        nlinarith only [sq_nonneg (a - b * (v i - mean s v))])
      (mul_nonneg (amplitude_pos s i).le (amplitude_pos r i).le)
    exact h.trans_eq (by ring)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hp i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have h0 := mul_le_mul_of_nonneg_left (amplitudeOverlap_le_one s r)
    (show 0 ≤ 2 * a ^ 2 by positivity)
  have h1 := mul_le_mul_of_nonneg_left (sum_amplitude_mul_centered_sq_le s r v)
    (show 0 ≤ 2 * b ^ 2 by positivity)
  unfold amplitudeOverlap at h0
  nlinarith only [hs, h0, h1]

end Mettapedia.Analysis.FiniteExponentialWeights
