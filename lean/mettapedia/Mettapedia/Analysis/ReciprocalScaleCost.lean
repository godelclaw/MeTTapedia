import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrated inverse-square scale speed

Unlike logarithmic speed, inverse-square speed has a uniform endpoint
bound along a positive increasing scale. This controls a coefficient
in a differential inequality, not the energy multiplying that coefficient.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.ReciprocalScaleCost

open MeasureTheory Set

theorem integral_rate_div_sq_eq_inv_sub (κ dκ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hk : ContinuousOn κ (Icc a b)) (hd : ContinuousOn dκ (Icc a b))
    (hp : ∀ t ∈ Icc a b, 0 < κ t)
    (hder : ∀ t ∈ Ioo a b, HasDerivAt κ (dκ t) t) :
    (∫ t in a..b, dκ t / κ t ^ 2) = (κ a)⁻¹ - (κ b)⁻¹ := by
  have hc := (hk.inv₀ (fun t ht ↦ (hp t ht).ne')).neg
  have hi : IntervalIntegrable (fun t ↦ dκ t / κ t ^ 2) volume a b :=
    (hd.div (hk.pow 2) (fun t ht ↦ pow_ne_zero 2 (hp t ht).ne')).intervalIntegrable_of_Icc hab
  have hrec (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun τ ↦ -(κ τ)⁻¹) (dκ t / κ t ^ 2) t := by
    simpa only [Pi.neg_def, Pi.inv_def, neg_div, neg_neg] using
      ((hder t ht).inv (hp t (Ioo_subset_Icc_self ht)).ne').neg
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hrec hi
  simpa only [neg_div, neg_neg, Pi.neg_apply, Pi.inv_apply, neg_sub_neg] using he

theorem integral_abs_rate_div_sq_eq_inv_sub_of_nonneg (κ dκ : ℝ → ℝ)
    (a b : ℝ) (hab : a ≤ b) (hk : ContinuousOn κ (Icc a b))
    (hd : ContinuousOn dκ (Icc a b)) (hp : ∀ t ∈ Icc a b, 0 < κ t)
    (hder : ∀ t ∈ Ioo a b, HasDerivAt κ (dκ t) t)
    (hn : ∀ t ∈ Icc a b, 0 ≤ dκ t) :
    (∫ t in a..b, |dκ t| / κ t ^ 2) = (κ a)⁻¹ - (κ b)⁻¹ := by
  rw [← integral_rate_div_sq_eq_inv_sub κ dκ a b hab hk hd hp hder]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  simp only [abs_of_nonneg (hn t ht)]

theorem integral_abs_rate_div_sq_le_inv_of_nonneg (κ dκ : ℝ → ℝ)
    (a b : ℝ) (hab : a ≤ b) (hk : ContinuousOn κ (Icc a b))
    (hd : ContinuousOn dκ (Icc a b)) (hp : ∀ t ∈ Icc a b, 0 < κ t)
    (hder : ∀ t ∈ Ioo a b, HasDerivAt κ (dκ t) t)
    (hn : ∀ t ∈ Icc a b, 0 ≤ dκ t) :
    (∫ t in a..b, |dκ t| / κ t ^ 2) ≤ (κ a)⁻¹ := by
  rw [integral_abs_rate_div_sq_eq_inv_sub_of_nonneg κ dκ a b hab hk hd hp hder hn]
  exact sub_le_self _ (inv_nonneg.mpr (hp b ⟨hab, le_rfl⟩).le)

end Mettapedia.Analysis.ReciprocalScaleCost
