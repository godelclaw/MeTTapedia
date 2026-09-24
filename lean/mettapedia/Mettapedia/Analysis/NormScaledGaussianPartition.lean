import Mettapedia.Analysis.GaussianPartitionEnergy
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Norm-scaled Gaussian partitions, including their zero-amplitude points

At a zero of the amplitude every scalar patch is nonnegative with a local
minimum, so its total derivative is zero. Away from zero the norm is
differentiable and the normalization cancellation controls the sum of
squared patch derivatives. No differentiability assumption on the norm
path is added at its zeros.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.GaussianPartitionEnergy

open scoped BigOperators RealInnerProductSpace
open FiniteExponentialWeights

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [NormedAddCommGroup E]

def normScaledAmplitude (center : ι → E) (tau : ℝ) (x : E) (i : ι) : ℝ :=
  ‖x‖ * gaussianAmplitude center tau x i

theorem sum_normScaledAmplitude_sq (center : ι → E) (tau : ℝ) (x : E) :
    (∑ i, normScaledAmplitude center tau x i ^ 2) = ‖x‖ ^ 2 := by
  simp only [normScaledAmplitude, mul_pow, ← Finset.mul_sum, sum_gaussianAmplitude_sq, mul_one]

theorem continuous_normScaledAmplitude (center : ι → E) (tau : ℝ) (i : ι) :
    Continuous (fun x ↦ normScaledAmplitude center tau x i) :=
  continuous_norm.mul (continuous_gaussianAmplitude center tau i)

variable [InnerProductSpace ℝ E]

omit [Fintype ι] [Nonempty ι] in
theorem deriv_norm_sq_le {x : ℝ → E} {v : E} {t : ℝ} (hx : HasDerivAt x v t) :
    deriv (fun s ↦ ‖x s‖) t ^ 2 ≤ ‖v‖ ^ 2 := by
  by_cases h0 : x t = 0
  · have hm : IsLocalMin (fun s ↦ ‖x s‖) t :=
      Filter.Eventually.of_forall (fun s ↦ by simp only [h0, norm_zero]; exact norm_nonneg _)
    have hz : deriv (fun s ↦ ‖x s‖) t = 0 := hm.deriv_eq_zero
    rw [hz]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using sq_nonneg ‖v‖
  · have hr := (hx.differentiableAt.norm ℝ h0).hasDerivAt
    have hid := (hr.pow 2).unique hx.norm_sq
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hid
    have hid' : ‖x t‖ * deriv (fun s ↦ ‖x s‖) t = ⟪x t, v⟫ := by linarith only [hid]
    have hinner := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm (x t) v) 2
    rw [sq_abs, ← hid', mul_pow, mul_pow] at hinner
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos (norm_pos_iff.mpr h0))).mp hinner

theorem sum_normScaled_deriv_sq_le_moment (center : ι → E) (tau : ℝ)
    {x : ℝ → E} {v : E} {t : ℝ} (hx : HasDerivAt x v t) :
    (∑ i, deriv (fun s ↦ normScaledAmplitude center tau (x s) i) t ^ 2) ≤
      ‖v‖ ^ 2 + ‖x t‖ ^ 2 * distanceMoment center tau (x t) * ‖v‖ ^ 2 / tau ^ 2 := by
  by_cases h0 : x t = 0
  · have hd (i : ι) : deriv (fun s ↦ normScaledAmplitude center tau (x s) i) t = 0 := by
      apply IsLocalMin.deriv_eq_zero
      apply Filter.Eventually.of_forall
      intro s
      simp only [normScaledAmplitude, h0, norm_zero, zero_mul]
      exact mul_nonneg (norm_nonneg _) (amplitude_pos _ i).le
    simp only [hd, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, h0, norm_zero, zero_mul,
      zero_div, add_zero]
    positivity
  · have hr := (hx.differentiableAt.norm ℝ h0).hasDerivAt
    have hd (i : ι) : deriv (fun s ↦ ‖x s‖ * gaussianAmplitude center tau (x s) i) t =
        deriv (fun s ↦ ‖x s‖) t * gaussianAmplitude center tau (x t) i +
          ‖x t‖ * amplitudeRate (score center tau (x t)) (scoreRate center tau (x t) v) i :=
      (hr.mul (hasDerivAt_gaussianAmplitude center tau hx i)).deriv
    unfold normScaledAmplitude
    simp_rw [hd]
    simp only [gaussianAmplitude]
    rw [sum_scaled_amplitudeRate_sq]
    have hm := mul_le_mul_of_nonneg_left (sum_amplitudeRate_sq_le_moment center tau (x t) v)
      (sq_nonneg ‖x t‖)
    have hn := deriv_norm_sq_le hx
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm, hn]

theorem sum_normScaled_deriv_sq_le (center : ι → E) (tau : ℝ) (ht : 0 < tau)
    {x : ℝ → E} {v : E} {t : ℝ} (hx : HasDerivAt x v t) (j : ι) :
    (∑ i, deriv (fun s ↦ normScaledAmplitude center tau (x s) i) t ^ 2) ≤
      (1 + ‖x t‖ ^ 2 * (‖x t - center j‖ ^ 2 + tau * Real.log (Fintype.card ι)) / tau ^ 2) * ‖v‖ ^ 2 := by
  have h := sum_normScaled_deriv_sq_le_moment center tau hx
  have hm := mul_le_mul_of_nonneg_right (distanceMoment_le center tau ht (x t) j)
    (show 0 ≤ ‖x t‖ ^ 2 * ‖v‖ ^ 2 / tau ^ 2 by positivity)
  simp only [div_eq_mul_inv] at h hm ⊢
  nlinarith only [h, hm]

end Mettapedia.Analysis.GaussianPartitionEnergy
