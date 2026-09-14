import Mathlib.Analysis.MeanInequalities
import Mettapedia.Analysis.WeightedInnerProduct

/-!
# Weighted Young bounds with a bounded first factor

Conjugate powers can replace the second square norm without assuming its
integrability. The first factor's pointwise bound leaves a measurable
square majorant, so extended integrals retain the entire unpaid cost.
-/

namespace Mettapedia.Analysis.WeightedYoung

open MeasureTheory
open scoped RealInnerProductSpace

theorem mul_le_weighted_rpow {x y a p q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 < a) (hpq : p.HolderConjugate q) :
    x * y ≤ a * x ^ p / p + a ^ (-p⁻¹ * q) * y ^ q / q := by
  have h := Real.young_inequality_of_nonneg
    (mul_nonneg (Real.rpow_nonneg ha.le _) hx)
    (mul_nonneg (Real.rpow_nonneg ha.le _) hy) hpq
      (a := a ^ p⁻¹ * x) (b := a ^ (-p⁻¹) * y)
  have he : (a ^ p⁻¹ * x) * (a ^ (-p⁻¹) * y) = x * y := by
    calc
      _ = (a ^ p⁻¹ * a ^ (-p⁻¹)) * (x * y) := by ring
      _ = _ := by rw [← Real.rpow_add ha, add_neg_cancel, Real.rpow_zero, one_mul]
  rw [he, Real.mul_rpow (Real.rpow_nonneg ha.le _) hx,
    Real.mul_rpow (Real.rpow_nonneg ha.le _) hy,
    ← Real.rpow_mul ha.le, ← Real.rpow_mul ha.le,
    inv_mul_cancel₀ hpq.ne_zero, Real.rpow_one] at h
  exact h

theorem rpow_eight_thirds_le_sq_mul {x M : ℝ} (hx : 0 ≤ x) (hM : x ≤ M) :
    x ^ (8 / 3 : ℝ) ≤ x ^ 2 * M ^ (2 / 3 : ℝ) := by
  calc
    _ = x ^ 2 * x ^ (2 / 3 : ℝ) := by
      rw [show (8 / 3 : ℝ) = 2 + 2 / 3 by norm_num,
        Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num), Real.rpow_two]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hM (by norm_num))
      (sq_nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The second norm has exponent `8/5`; no estimate for that norm is asserted. -/
theorem two_mul_abs_inner_le_bounded_eight_fifths (x y : E) {a M : ℝ}
    (ha : 0 < a) (hM : ‖x‖ ≤ M) :
    2 * |⟪x, y⟫| ≤ (2 * a * M ^ (2 / 3 : ℝ)) * ‖x‖ ^ 2 +
      (2 * a ^ (-3 / 5 : ℝ)) * ‖y‖ ^ (8 / 5 : ℝ) := by
  have h := mul_le_weighted_rpow (norm_nonneg x) (norm_nonneg y) ha
    (by norm_num [Real.holderConjugate_iff] : (8 / 3 : ℝ).HolderConjugate (8 / 5))
  norm_num only [show -((8 / 3 : ℝ)⁻¹) * (8 / 5) = -3 / 5 by norm_num] at h
  have hx := rpow_eight_thirds_le_sq_mul (norm_nonneg x) hM
  have hp := Real.rpow_nonneg (norm_nonneg x) (8 / 3 : ℝ)
  have hq := mul_nonneg (Real.rpow_nonneg ha.le (-3 / 5 : ℝ))
    (Real.rpow_nonneg (norm_nonneg y) (8 / 5 : ℝ))
  have hi := abs_real_inner_le_norm x y
  nlinarith [mul_le_mul_of_nonneg_left hx ha.le]

/-- Only the first square norm needs measurability. -/
theorem lintegral_two_mul_abs_inner_le_bounded_eight_fifths
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (x y : α → E)
    {a M : ℝ} (ha : 0 < a) (hM0 : 0 ≤ M) (hM : ∀ᵐ z ∂μ, ‖x z‖ ≤ M)
    (hx : AEMeasurable (fun z ↦ ENNReal.ofReal (‖x z‖ ^ 2)) μ) :
    (∫⁻ z, ENNReal.ofReal (2 * |⟪x z, y z⟫|) ∂μ) ≤
      ENNReal.ofReal (2 * a * M ^ (2 / 3 : ℝ)) *
        (∫⁻ z, ENNReal.ofReal (‖x z‖ ^ 2) ∂μ) +
      ENNReal.ofReal (2 * a ^ (-3 / 5 : ℝ)) *
        ∫⁻ z, ENNReal.ofReal (‖y z‖ ^ (8 / 5 : ℝ)) ∂μ := by
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (2 * a * M ^ (2 / 3 : ℝ)) *
        ENNReal.ofReal (‖x z‖ ^ 2) + ENNReal.ofReal (2 * a ^ (-3 / 5 : ℝ)) *
        ENNReal.ofReal (‖y z‖ ^ (8 / 5 : ℝ)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hM] with z hz
      have h := ENNReal.ofReal_le_ofReal
        (two_mul_abs_inner_le_bounded_eight_fifths (x z) (y z) ha hz)
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (show 0 ≤ 2 * a * M ^ (2 / 3 : ℝ) by positivity),
        ENNReal.ofReal_mul (show 0 ≤ 2 * a ^ (-3 / 5 : ℝ) by positivity)] at h
      exact h
    _ = _ := by
      rw [lintegral_add_left' (hx.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end Mettapedia.Analysis.WeightedYoung
