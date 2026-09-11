import Mettapedia.Analysis.FiniteExponentialWeights
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Derivative energy of normalized exponential amplitudes

Normalization subtracts the weighted mean score rate. Consequently the
total squared amplitude derivative is one quarter of its weighted
variance, with no dimension or cardinality multiplier. Multiplying the
amplitudes by a common scalar has an exact orthogonal energy split.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteExponentialWeights

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def amplitudeRate (s v : ι → ℝ) (i : ι) : ℝ := amplitude s i / 2 * (v i - mean s v)

theorem amplitudeRate_const (s : ι → ℝ) (c : ℝ) (i : ι) :
    amplitudeRate s (fun _ ↦ c) i = 0 := by
  simp only [amplitudeRate, mean_const, sub_self, mul_zero]

theorem amplitudeRate_add_const (s v : ι → ℝ) (c : ℝ) (i : ι) :
    amplitudeRate s (fun j ↦ v j + c) i = amplitudeRate s v i := by
  simp only [amplitudeRate, mean_add_const, add_sub_add_right_eq_sub]

theorem partition_mul_mean (s v : ι → ℝ) :
    partition s * mean s v = ∑ i, Real.exp (s i) * v i := by
  unfold mean weight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [ne_of_gt (partition_pos s)]

theorem hasDerivAt_amplitude {s : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (hs : ∀ i, HasDerivAt (fun r ↦ s r i) (v i) t) (i : ι) :
    HasDerivAt (fun r ↦ amplitude (s r) i) (amplitudeRate (s t) v i) t := by
  have hZ : HasDerivAt (fun r ↦ partition (s r)) (∑ j, Real.exp (s t j) * v j) t :=
    HasDerivAt.fun_sum (fun j _ ↦ (hs j).exp)
  have h : HasDerivAt (fun r ↦ amplitude (s r) i)
      ((Real.exp (s t i / 2) * (v i / 2) * Real.sqrt (partition (s t)) -
        Real.exp (s t i / 2) * ((∑ j, Real.exp (s t j) * v j) / (2 * Real.sqrt (partition (s t))))) /
        Real.sqrt (partition (s t)) ^ 2) t :=
    ((hs i).div_const 2).exp.div (hZ.sqrt (ne_of_gt (partition_pos (s t))))
      (ne_of_gt (Real.sqrt_pos.mpr (partition_pos (s t))))
  have hroot : Real.sqrt (partition (s t)) ^ 2 = partition (s t) := Real.sq_sqrt (partition_pos _).le
  have hroot0 : Real.sqrt (partition (s t)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (partition_pos _))
  have hmean := partition_mul_mean (s t) v
  convert h using 1
  unfold amplitudeRate amplitude
  rw [← hmean]
  field_simp
  rw [hroot]
  ring

theorem sum_amplitude_mul_rate (s v : ι → ℝ) :
    (∑ i, amplitude s i * amplitudeRate s v i) = 0 := by
  have hid (i : ι) : amplitude s i * amplitudeRate s v i = weight s i * (v i - mean s v) / 2 := by
    rw [← amplitude_sq]
    unfold amplitudeRate
    ring
  simp_rw [hid, mul_sub]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_weight, one_mul]
  change (mean s v - mean s v) / 2 = 0
  ring

theorem sum_amplitudeRate_sq (s v : ι → ℝ) :
    (∑ i, amplitudeRate s v i ^ 2) = (mean s (fun i ↦ v i ^ 2) - mean s v ^ 2) / 4 := by
  have hid (i : ι) : amplitudeRate s v i ^ 2 =
      (weight s i * v i ^ 2 - 2 * (weight s i * v i) * mean s v + weight s i * mean s v ^ 2) / 4 := by
    rw [← amplitude_sq]
    unfold amplitudeRate
    ring
  simp_rw [hid]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, sum_weight, one_mul]
  change (mean s (fun i ↦ v i ^ 2) - 2 * mean s v * mean s v + mean s v ^ 2) / 4 = _
  ring

theorem sum_amplitudeRate_sq_le (s v : ι → ℝ) :
    (∑ i, amplitudeRate s v i ^ 2) ≤ mean s (fun i ↦ v i ^ 2) / 4 := by
  rw [sum_amplitudeRate_sq]
  nlinarith only [sq_nonneg (mean s v)]

theorem sum_scaled_amplitudeRate_sq (s v : ι → ℝ) (r r' : ℝ) :
    (∑ i, (r' * amplitude s i + r * amplitudeRate s v i) ^ 2) =
      r' ^ 2 + r ^ 2 * ∑ i, amplitudeRate s v i ^ 2 := by
  have hid (i : ι) : (r' * amplitude s i + r * amplitudeRate s v i) ^ 2 =
      r' ^ 2 * amplitude s i ^ 2 + 2 * r' * r * (amplitude s i * amplitudeRate s v i) +
        r ^ 2 * amplitudeRate s v i ^ 2 := by ring
  simp_rw [hid]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_amplitude_sq, sum_amplitude_mul_rate]
  ring

end Mettapedia.Analysis.FiniteExponentialWeights
