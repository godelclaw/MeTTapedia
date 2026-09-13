import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A division-free Duhamel identity for two exponential rates

The formula remains valid when the rates coincide. The signed rate
difference is kept outside a nonnegative convolution kernel.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.ExponentialDuhamel

open MeasureTheory

def kernel (a b t s : ℝ) : ℝ := Real.exp (-a * (t - s)) * Real.exp (-b * s)

theorem continuous_kernel (a b t : ℝ) : Continuous (kernel a b t) := by
  unfold kernel
  fun_prop

theorem kernel_pos (a b t s : ℝ) : 0 < kernel a b t s :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

theorem hasDerivAt_kernel (a b t s : ℝ) :
    HasDerivAt (kernel a b t) ((a - b) * kernel a b t s) s := by
  have h := ((((hasDerivAt_id s).const_sub t).const_mul (-a)).exp).mul
    (((hasDerivAt_id s).const_mul (-b)).exp)
  apply h.congr_deriv
  dsimp [kernel]
  ring

/-- No inverse rate difference, including at resonance. -/
theorem exp_sub_eq_rate_mul_integral (a b t : ℝ) :
    Real.exp (-a * t) - Real.exp (-b * t) =
      (b - a) * ∫ s in (0 : ℝ)..t, kernel a b t s := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_kernel a b t s)
    (((continuous_const (y := a - b)).mul (continuous_kernel a b t)).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul] at h
  simp only [kernel, sub_self, mul_zero, Real.exp_zero, one_mul, sub_zero, mul_one] at h
  unfold kernel
  linarith

theorem integral_kernel_nonneg (a b : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∫ s in (0 : ℝ)..t, kernel a b t s :=
  intervalIntegral.integral_nonneg_of_forall ht (fun s ↦ (kernel_pos a b t s).le)

theorem kernel_le_exp_min (a b : ℝ) {t s : ℝ} (hs : s ∈ Set.Icc 0 t) :
    kernel a b t s ≤ Real.exp (-min a b * t) := by
  rw [kernel, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left a b) (sub_nonneg.mpr hs.2)
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right a b) hs.1
  nlinarith

theorem integral_kernel_le (a b : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, kernel a b t s) ≤ t * Real.exp (-min a b * t) := by
  have h := intervalIntegral.integral_mono_on (μ := volume) ht
    ((continuous_kernel a b t).intervalIntegrable 0 t)
    (continuous_const.intervalIntegrable 0 t) (fun s hs ↦ kernel_le_exp_min a b hs)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h

theorem abs_exp_sub_le (a b : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |Real.exp (-a * t) - Real.exp (-b * t)| ≤
      |b - a| * t * Real.exp (-min a b * t) := by
  rw [exp_sub_eq_rate_mul_integral, abs_mul, abs_of_nonneg (integral_kernel_nonneg a b ht)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (integral_kernel_le a b ht) (abs_nonneg (b - a))

theorem integral_weighted_exp_sub (a b c : ℝ) (ha : 0 < c + a) (hb : 0 < c + b) :
    (∫ t : ℝ in Set.Ioi 0,
      Real.exp (-c * t) * (Real.exp (-a * t) - Real.exp (-b * t))) =
      (b - a) / ((c + a) * (c + b)) := by
  have he : (fun t : ℝ ↦ Real.exp (-c * t) * (Real.exp (-a * t) - Real.exp (-b * t))) =
      fun t ↦ Real.exp (-(c + a) * t) - Real.exp (-(c + b) * t) := by
    funext t
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [he, integral_sub (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0)
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hb) 0),
    integral_exp_mul_Ioi (neg_lt_zero.mpr ha), integral_exp_mul_Ioi (neg_lt_zero.mpr hb)]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
  field_simp
  nlinarith

end Mettapedia.Analysis.ExponentialDuhamel
