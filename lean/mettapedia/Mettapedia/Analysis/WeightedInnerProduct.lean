import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Weighted real inner-product bounds

The two square norms carry reciprocal weights. Infinite sums require
explicit summability of both weighted square norms.
-/

namespace Mettapedia.Analysis.WeightedInnerProduct

open scoped RealInnerProductSpace
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem two_mul_abs_inner_le (x y : E) {a : ℝ} (ha : 0 < a) :
    2 * |⟪x, y⟫| ≤ a * ‖x‖ ^ 2 + a⁻¹ * ‖y‖ ^ 2 := by
  have h : (2 * |⟪x, y⟫|) * a ≤ a ^ 2 * ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    have hi := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm x y) ha.le
    nlinarith [sq_nonneg (a * ‖x‖ - ‖y‖)]
  have hd := (le_div_iff₀ ha).mpr h
  apply hd.trans_eq
  field_simp

theorem two_mul_inner_le (x y : E) {a : ℝ} (ha : 0 < a) :
    2 * ⟪x, y⟫ ≤ a * ‖x‖ ^ 2 + a⁻¹ * ‖y‖ ^ 2 :=
  (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (two_mul_abs_inner_le x y ha)

theorem two_mul_abs_inner_sum_le {ι : Type*} (s : Finset ι) (x y : ι → E)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) :
    2 * |∑ i ∈ s, ⟪x i, y i⟫| ≤
      (∑ i ∈ s, a i * ‖x i‖ ^ 2) + ∑ i ∈ s, (a i)⁻¹ * ‖y i‖ ^ 2 := by
  calc
    _ ≤ ∑ i ∈ s, 2 * |⟪x i, y i⟫| := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ ∑ i ∈ s, (a i * ‖x i‖ ^ 2 + (a i)⁻¹ * ‖y i‖ ^ 2) :=
      Finset.sum_le_sum (fun i hi ↦ two_mul_abs_inner_le (x i) (y i) (ha i hi))
    _ = _ := Finset.sum_add_distrib

/-- Only the first square norm needs measurability for this extended-integral bound. -/
theorem lintegral_two_mul_abs_inner_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (x y : α → E) {a : ℝ} (ha : 0 < a)
    (hx : AEMeasurable (fun z ↦ ENNReal.ofReal (‖x z‖ ^ 2)) μ) :
    (∫⁻ z, ENNReal.ofReal (2 * |⟪x z, y z⟫|) ∂μ) ≤
      ENNReal.ofReal a * (∫⁻ z, ENNReal.ofReal (‖x z‖ ^ 2) ∂μ) +
      ENNReal.ofReal a⁻¹ * ∫⁻ z, ENNReal.ofReal (‖y z‖ ^ 2) ∂μ := by
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal a * ENNReal.ofReal (‖x z‖ ^ 2) +
        ENNReal.ofReal a⁻¹ * ENNReal.ofReal (‖y z‖ ^ 2) ∂μ := by
      apply lintegral_mono
      intro z
      have h := ENNReal.ofReal_le_ofReal (two_mul_abs_inner_le (x z) (y z) ha)
      rw [ENNReal.ofReal_add (mul_nonneg ha.le (sq_nonneg _))
        (mul_nonneg (inv_nonneg.mpr ha.le) (sq_nonneg _)),
        ENNReal.ofReal_mul ha.le, ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)] at h
      exact h
    _ = _ := by
      rw [lintegral_add_left' (hx.const_mul _)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end Mettapedia.Analysis.WeightedInnerProduct
