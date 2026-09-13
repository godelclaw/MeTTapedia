import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# First moments of decaying exponentials

Integrability and the exact first moment on the positive half-line.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.ExponentialMoments

open MeasureTheory

theorem integrableOn_mul_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ x * Real.exp (-(a * x))) (Set.Ioi 0) := by
  have hi : IntegrableOn (fun x : ℝ ↦ Real.exp (-x) * x) (Set.Ioi 0) := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
      Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2)
  have hc := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ ↦ Real.exp (-x) * x) 0 ha).mpr
    (by simpa using hi)
  have he : (fun x : ℝ ↦ x * Real.exp (-(a * x))) =
      (fun x : ℝ ↦ (1 / a) * (Real.exp (-(a * x)) * (a * x))) := by
    funext x
    field_simp
  rw [he]
  exact hc.const_mul _

theorem integral_mul_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Set.Ioi 0, x * Real.exp (-(a * x))) = 1 / a ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 2) ha
  norm_num [Real.Gamma_nat_eq_factorial] at h
  simpa [one_div_pow] using h

end Mettapedia.Analysis.ExponentialMoments
