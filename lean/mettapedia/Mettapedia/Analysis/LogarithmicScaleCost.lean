import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Accumulated relative speed controls logarithmic scale growth

Absolute relative speed is not automatically integrable with a uniform
bound when a positive scale diverges. On increasing differentiable paths
its integral is exactly the logarithmic endpoint increase.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.LogarithmicScaleCost

open MeasureTheory Set

theorem integral_rate_div_eq_log_sub (κ dκ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hk : ContinuousOn κ (Icc a b)) (hd : ContinuousOn dκ (Icc a b))
    (hp : ∀ t ∈ Icc a b, 0 < κ t)
    (hder : ∀ t ∈ Ioo a b, HasDerivAt κ (dκ t) t) :
    (∫ t in a..b, dκ t / κ t) = Real.log (κ b) - Real.log (κ a) := by
  have hc := hk.log (fun t ht ↦ (hp t ht).ne')
  have hi : IntervalIntegrable (fun t ↦ dκ t / κ t) volume a b :=
    (hd.div hk (fun t ht ↦ (hp t ht).ne')).intervalIntegrable_of_Icc hab
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
    (fun t ht ↦ (hder t ht).log (hp t (Ioo_subset_Icc_self ht)).ne') hi

theorem log_sub_le_integral_abs_rate (κ dκ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hk : ContinuousOn κ (Icc a b)) (hd : ContinuousOn dκ (Icc a b))
    (hp : ∀ t ∈ Icc a b, 0 < κ t)
    (hder : ∀ t ∈ Ioo a b, HasDerivAt κ (dκ t) t) :
    Real.log (κ b) - Real.log (κ a) ≤ ∫ t in a..b, |dκ t| / κ t := by
  rw [← integral_rate_div_eq_log_sub κ dκ a b hab hk hd hp hder]
  apply intervalIntegral.integral_mono_on hab
    ((hd.div hk (fun t ht ↦ (hp t ht).ne')).intervalIntegrable_of_Icc hab)
    ((hd.abs.div hk (fun t ht ↦ (hp t ht).ne')).intervalIntegrable_of_Icc hab)
  intro t ht
  exact div_le_div_of_nonneg_right (le_abs_self _) (hp t ht).le

theorem integral_abs_rate_eq_log_sub_of_nonneg (κ dκ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hk : ContinuousOn κ (Icc a b)) (hd : ContinuousOn dκ (Icc a b))
    (hp : ∀ t ∈ Icc a b, 0 < κ t)
    (hder : ∀ t ∈ Ioo a b, HasDerivAt κ (dκ t) t)
    (hn : ∀ t ∈ Icc a b, 0 ≤ dκ t) :
    (∫ t in a..b, |dκ t| / κ t) = Real.log (κ b) - Real.log (κ a) := by
  rw [← integral_rate_div_eq_log_sub κ dκ a b hab hk hd hp hder]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  change |dκ t| / κ t = dκ t / κ t
  rw [abs_of_nonneg (hn t ht)]

end Mettapedia.Analysis.LogarithmicScaleCost
