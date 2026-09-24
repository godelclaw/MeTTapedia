import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Normalized periodic spatial means

The means below are the actual Lebesgue integrals over a full period,
not an abstract distribution with separately supplied moments. Frequency
repetition and translations preserve the mean. The cosine-square moment
and a lower bound for the absolute-cosine moment are derived explicitly.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePeriodicMean

open MeasureTheory Real

def circleMean (f : ℝ → ℝ) : ℝ := (∫ x in (0 : ℝ)..2 * π, f x) / (2 * π)

theorem circleMean_congr (f g : ℝ → ℝ) (h : ∀ x, f x = g x) : circleMean f = circleMean g := by
  congr 1
  exact funext h

theorem circleMean_const (c : ℝ) : circleMean (fun _ ↦ c) = c := by
  simp [circleMean, intervalIntegral.integral_const, Real.pi_ne_zero]

theorem circleMean_add (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    circleMean (fun x ↦ f x + g x) = circleMean f + circleMean g := by
  rw [circleMean, intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  exact add_div _ _ _

theorem circleMean_sub (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    circleMean (fun x ↦ f x - g x) = circleMean f - circleMean g := by
  rw [circleMean, intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  exact sub_div _ _ _

theorem circleMean_const_mul (c : ℝ) (f : ℝ → ℝ) :
    circleMean (fun x ↦ c * f x) = c * circleMean f := by
  simp only [circleMean, intervalIntegral.integral_const_mul]
  ring

theorem circleMean_mul_const (c : ℝ) (f : ℝ → ℝ) :
    circleMean (fun x ↦ f x * c) = circleMean f * c := by
  simp only [circleMean, intervalIntegral.integral_mul_const]
  ring

theorem circleMean_div (c : ℝ) (f : ℝ → ℝ) :
    circleMean (fun x ↦ f x / c) = circleMean f / c := by
  simp only [circleMean, intervalIntegral.integral_div]
  ring

theorem circleMean_mono (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, f x ≤ g x) : circleMean f ≤ circleMean g := by
  apply div_le_div_of_nonneg_right ?_ (by positivity : 0 ≤ 2 * π)
  exact intervalIntegral.integral_mono_on (by positivity) (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    (fun x _ ↦ h x)

theorem continuous_circleMean {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [LocallyCompactSpace P]
    (f : P → ℝ → ℝ) (hf : Continuous f.uncurry) :
    Continuous (fun x ↦ circleMean (f x)) := by
  have h := continuous_parametric_integral_of_continuous (μ := volume) hf
    (isCompact_Icc (a := 0) (b := 2 * π))
  have heq : (fun x ↦ circleMean (f x)) =
      (fun x ↦ (∫ y in Set.Icc (0 : ℝ) (2 * π), f x y) / (2 * π)) := by
    funext x
    rw [circleMean, intervalIntegral.integral_of_le (by positivity), integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact h.div_const _

theorem circleMean_shift (f : ℝ → ℝ) (hf : Function.Periodic f (2 * π)) (d : ℝ) :
    circleMean (fun x ↦ f (x + d)) = circleMean f := by
  unfold circleMean
  rw [intervalIntegral.integral_comp_add_right]
  congr 1
  simpa only [zero_add, add_comm (2 * π) d] using hf.intervalIntegral_add_eq d 0

theorem circleMean_nat_frequency (f : ℝ → ℝ) (hf : Continuous f)
    (hp : Function.Periodic f (2 * π)) (N : ℕ) (hN : N ≠ 0) :
    circleMean (fun x ↦ f ((N : ℝ) * x)) = circleMean f := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have h := hp.intervalIntegral_add_zsmul_eq (N : ℤ) 0
    (fun a b ↦ hf.intervalIntegrable (a := a) (b := b))
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast] at h
  unfold circleMean
  rw [intervalIntegral.integral_comp_mul_left _ hNr, mul_zero, h]
  simp [smul_eq_mul, hNr]

theorem circleMean_cos_sq : circleMean (fun x ↦ cos x ^ 2) = 1 / 2 := by
  simp [circleMean, integral_cos_sq, sin_two_pi, cos_two_pi]
  field_simp

/-- The full-period cosine moment recurrence, obtained from integration by parts. -/
theorem circleMean_cos_pow_add_two (n : ℕ) :
    circleMean (fun x ↦ cos x ^ (n + 2)) =
      ((n : ℝ) + 1) / ((n : ℝ) + 2) * circleMean (fun x ↦ cos x ^ n) := by
  unfold circleMean
  rw [integral_cos_pow]
  simp only [sin_two_pi, sin_zero, mul_zero, sub_self, zero_div, zero_add]
  ring

theorem circleMean_cos_pow_four : circleMean (fun x ↦ cos x ^ 4) = 3 / 8 := by
  rw [show (4 : ℕ) = 2 + 2 by decide, circleMean_cos_pow_add_two, circleMean_cos_sq]
  norm_num

theorem circleMean_cos_pow_six : circleMean (fun x ↦ cos x ^ 6) = 5 / 16 := by
  rw [show (6 : ℕ) = 4 + 2 by decide, circleMean_cos_pow_add_two, circleMean_cos_pow_four]
  norm_num

theorem circleMean_cos_pow_eight : circleMean (fun x ↦ cos x ^ 8) = 35 / 128 := by
  rw [show (8 : ℕ) = 6 + 2 by decide, circleMean_cos_pow_add_two, circleMean_cos_pow_six]
  norm_num

theorem circleMean_abs_cos_lower : (1 : ℝ) / 2 ≤ circleMean (fun x ↦ |cos x|) := by
  rw [← circleMean_cos_sq]
  apply circleMean_mono _ _ (by fun_prop) (by fun_prop)
  intro x
  have h := abs_cos_le_one x
  have hn := abs_nonneg (cos x)
  nlinarith [sq_abs (cos x)]

theorem circleMean_scaled_abs_cos_sq (eps : ℝ) :
    circleMean (fun x ↦ (eps * |cos x|) ^ 2) = eps ^ 2 / 2 := by
  simp_rw [mul_pow, sq_abs]
  rw [circleMean_const_mul, circleMean_cos_sq]
  ring

def spatialMean (f : ℝ → ℝ → ℝ) : ℝ := circleMean (fun x ↦ circleMean (f x))

theorem continuous_spatialMean {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [LocallyCompactSpace P]
    (f : P → ℝ → ℝ → ℝ)
    (hf : Continuous (fun q : P × (ℝ × ℝ) ↦ f q.1 q.2.1 q.2.2)) :
    Continuous (fun p ↦ spatialMean (f p)) := by
  apply continuous_circleMean
  apply continuous_circleMean
  exact hf.comp (show Continuous (fun q : (P × ℝ) × ℝ ↦ (q.1.1, (q.1.2, q.2)))
    from by fun_prop)

theorem spatialMean_congr (f g : ℝ → ℝ → ℝ) (h : ∀ x y, f x y = g x y) :
    spatialMean f = spatialMean g := by
  apply circleMean_congr
  intro x
  exact circleMean_congr _ _ (h x)

theorem spatialMean_const (c : ℝ) : spatialMean (fun _ _ ↦ c) = c := by
  simp only [spatialMean, circleMean_const]

theorem spatialMean_mono (f g : ℝ → ℝ → ℝ) (hf : Continuous f.uncurry)
    (hg : Continuous g.uncurry) (h : ∀ x y, f x y ≤ g x y) : spatialMean f ≤ spatialMean g := by
  apply circleMean_mono _ _ (continuous_circleMean f hf) (continuous_circleMean g hg)
  intro x
  exact circleMean_mono _ _ (hf.comp (continuous_const.prodMk continuous_id))
    (hg.comp (continuous_const.prodMk continuous_id)) (h x)

theorem spatialMean_sub (f g : ℝ → ℝ → ℝ) (hf : Continuous f.uncurry)
    (hg : Continuous g.uncurry) :
    spatialMean (fun x y ↦ f x y - g x y) = spatialMean f - spatialMean g := by
  unfold spatialMean
  have heq : (fun x ↦ circleMean (fun y ↦ f x y - g x y)) =
      (fun x ↦ circleMean (f x) - circleMean (g x)) := by
    funext x
    exact circleMean_sub _ _ (hf.comp (continuous_const.prodMk continuous_id))
      (hg.comp (continuous_const.prodMk continuous_id))
  rw [heq, circleMean_sub _ _ (continuous_circleMean f hf) (continuous_circleMean g hg)]

theorem spatialMean_add (f g : ℝ → ℝ → ℝ) (hf : Continuous f.uncurry)
    (hg : Continuous g.uncurry) :
    spatialMean (fun x y ↦ f x y + g x y) = spatialMean f + spatialMean g := by
  unfold spatialMean
  have heq : (fun x ↦ circleMean (fun y ↦ f x y + g x y)) =
      (fun x ↦ circleMean (f x) + circleMean (g x)) := by
    funext x
    exact circleMean_add _ _ (hf.comp (continuous_const.prodMk continuous_id))
      (hg.comp (continuous_const.prodMk continuous_id))
  rw [heq, circleMean_add _ _ (continuous_circleMean f hf) (continuous_circleMean g hg)]

theorem spatialMean_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    spatialMean (fun x y ↦ c * f x y) = c * spatialMean f := by
  simp only [spatialMean, circleMean_const_mul]

theorem spatialMean_product (f g : ℝ → ℝ) :
    spatialMean (fun x y ↦ f x * g y) = circleMean f * circleMean g := by
  simp only [spatialMean, circleMean_const_mul, circleMean_mul_const]

end Mettapedia.FluidDynamics.NavierStokes.PancakePeriodicMean
