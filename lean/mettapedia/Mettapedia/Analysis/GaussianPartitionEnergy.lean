import Mettapedia.Analysis.ExponentialAmplitudeDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Gaussian square partitions with quantitative derivative and localization costs

Normalized Gaussian amplitudes have squared sum one. Their mean squared
distance is bounded by the nearest squared distance plus `tau * log(card)`.
The same distance moment controls the total derivative energy. The
construction is not compactly supported; its localization error is explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.GaussianPartitionEnergy

open scoped BigOperators RealInnerProductSpace
open FiniteExponentialWeights

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [NormedAddCommGroup E]

def score (center : ι → E) (tau : ℝ) (x : E) (i : ι) : ℝ := -‖x - center i‖ ^ 2 / tau

def gaussianAmplitude (center : ι → E) (tau : ℝ) (x : E) (i : ι) : ℝ :=
  amplitude (score center tau x) i

def distanceMoment (center : ι → E) (tau : ℝ) (x : E) : ℝ :=
  mean (score center tau x) (fun i ↦ ‖x - center i‖ ^ 2)

theorem sum_gaussianAmplitude_sq (center : ι → E) (tau : ℝ) (x : E) :
    (∑ i, gaussianAmplitude center tau x i ^ 2) = 1 := sum_amplitude_sq _

theorem sum_sq_mul_distance_eq (center : ι → E) (tau : ℝ) (x : E) :
    (∑ i, gaussianAmplitude center tau x i ^ 2 * ‖x - center i‖ ^ 2) =
      distanceMoment center tau x := by
  simp only [gaussianAmplitude, amplitude_sq, distanceMoment, mean]

theorem distanceMoment_le (center : ι → E) (tau : ℝ) (ht : 0 < tau) (x : E) (j : ι) :
    distanceMoment center tau x ≤ ‖x - center j‖ ^ 2 + tau * Real.log (Fintype.card ι) :=
  mean_cost_le (fun i ↦ ‖x - center i‖ ^ 2) tau ht j

theorem continuous_gaussianAmplitude (center : ι → E) (tau : ℝ) (i : ι) :
    Continuous (fun x ↦ gaussianAmplitude center tau x i) := by
  have hscore (j : ι) : Continuous (fun x ↦ score center tau x j) := by
    unfold score
    fun_prop
  have hZ : Continuous (fun x ↦ partition (score center tau x)) :=
    continuous_finsetSum _ (fun j _ ↦ (hscore j).rexp)
  exact ((hscore i).div_const 2).rexp.div hZ.sqrt
    (fun x ↦ ne_of_gt (Real.sqrt_pos.mpr (partition_pos _)))

variable [InnerProductSpace ℝ E]

def scoreRate (center : ι → E) (tau : ℝ) (x v : E) (i : ι) : ℝ :=
  -(2 * ⟪x - center i, v⟫) / tau

theorem hasDerivAt_gaussianAmplitude (center : ι → E) (tau : ℝ)
    {x : ℝ → E} {v : E} {t : ℝ} (hx : HasDerivAt x v t) (i : ι) :
    HasDerivAt (fun r ↦ gaussianAmplitude center tau (x r) i)
      (amplitudeRate (score center tau (x t)) (scoreRate center tau (x t) v) i) t := by
  apply hasDerivAt_amplitude
  intro j
  exact (((hx.sub_const (center j)).norm_sq).neg).div_const tau

omit [Fintype ι] [Nonempty ι] in
theorem scoreRate_sq_le (center : ι → E) (tau : ℝ) (x v : E) (i : ι) :
    scoreRate center tau x v i ^ 2 ≤ 4 / tau ^ 2 * ‖v‖ ^ 2 * ‖x - center i‖ ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm (x - center i) v) 2
  rw [sq_abs, mul_pow] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 4 / tau ^ 2 by positivity)
  unfold scoreRate
  simp only [div_pow, neg_sq, mul_pow]
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm]

theorem sum_amplitudeRate_sq_le_moment (center : ι → E) (tau : ℝ) (x v : E) :
    (∑ i, amplitudeRate (score center tau x) (scoreRate center tau x v) i ^ 2) ≤
      distanceMoment center tau x * ‖v‖ ^ 2 / tau ^ 2 := by
  have hm := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    mul_le_mul_of_nonneg_left (scoreRate_sq_le center tau x v i) (weight_pos (score center tau x) i).le)
  have hid : (∑ i, weight (score center tau x) i *
      (4 / tau ^ 2 * ‖v‖ ^ 2 * ‖x - center i‖ ^ 2)) =
      4 / tau ^ 2 * ‖v‖ ^ 2 * distanceMoment center tau x := by
    unfold distanceMoment mean
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid] at hm
  have h := sum_amplitudeRate_sq_le (score center tau x) (scoreRate center tau x v)
  unfold mean at h
  simp only [div_eq_mul_inv] at h hm ⊢
  nlinarith only [h, hm]

/-- This is a bound for the actual derivatives of the scaled amplitudes,
not an assumption on independent rates. -/
theorem sum_scaled_deriv_sq_le (center : ι → E) (tau : ℝ) (ht : 0 < tau)
    {x : ℝ → E} {v : E} {t : ℝ} (hx : HasDerivAt x v t)
    {r : ℝ → ℝ} {r' : ℝ} (hr : HasDerivAt r r' t) (j : ι) :
    (∑ i, deriv (fun s ↦ r s * gaussianAmplitude center tau (x s) i) t ^ 2) ≤
      r' ^ 2 + r t ^ 2 * (‖x t - center j‖ ^ 2 + tau * Real.log (Fintype.card ι)) * ‖v‖ ^ 2 / tau ^ 2 := by
  have hd (i : ι) : deriv (fun s ↦ r s * gaussianAmplitude center tau (x s) i) t =
      r' * gaussianAmplitude center tau (x t) i +
        r t * amplitudeRate (score center tau (x t)) (scoreRate center tau (x t) v) i :=
    (hr.mul (hasDerivAt_gaussianAmplitude center tau hx i)).deriv
  simp_rw [hd]
  rw [show (∑ i, (r' * gaussianAmplitude center tau (x t) i +
      r t * amplitudeRate (score center tau (x t)) (scoreRate center tau (x t) v) i) ^ 2) =
      r' ^ 2 + r t ^ 2 * ∑ i, amplitudeRate (score center tau (x t)) (scoreRate center tau (x t) v) i ^ 2
    from sum_scaled_amplitudeRate_sq _ _ _ _]
  have h1 := mul_le_mul_of_nonneg_left (sum_amplitudeRate_sq_le_moment center tau (x t) v) (sq_nonneg (r t))
  have h2 := mul_le_mul_of_nonneg_right (distanceMoment_le center tau ht (x t) j)
    (show 0 ≤ r t ^ 2 * ‖v‖ ^ 2 / tau ^ 2 by positivity)
  simp only [div_eq_mul_inv] at h1 h2 ⊢
  nlinarith only [h1, h2]

end Mettapedia.Analysis.GaussianPartitionEnergy
