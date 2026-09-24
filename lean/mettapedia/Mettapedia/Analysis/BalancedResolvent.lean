import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Reflected resolvent defects with an explicit test mismatch

The first-order defect cancels for equal tests. Unequal tests leave a
separate first-order difference term; the cancellation does not remove it.
-/

noncomputable section

namespace Mettapedia.Analysis.BalancedResolvent

def defect (a d : ℝ) : ℝ := -d / (a * (a + d))

theorem denominator_pos {a d : ℝ} (_ha : 0 < a) (hd : |d| < a) :
    0 < a ^ 2 - d ^ 2 := by
  have h := abs_lt.mp hd
  nlinarith [mul_pos (by linarith : 0 < a - d) (by linarith : 0 < a + d)]

/-- The sign of the original defect is retained in the test-difference term. -/
theorem weighted_pair_eq {a d : ℝ} (ha : 0 < a) (hd : |d| < a) (x y : ℝ) :
    defect a d * x + defect a (-d) * y =
      d ^ 2 / (a * (a ^ 2 - d ^ 2)) * (x + y) -
        d / (a ^ 2 - d ^ 2) * (x - y) := by
  have h := abs_lt.mp hd
  have hp : a + d ≠ 0 := by linarith
  have hm : a - d ≠ 0 := by linarith
  have hden := (denominator_pos ha hd).ne'
  unfold defect
  simp only [neg_neg, ← sub_eq_add_neg]
  field_simp [ha.ne', hp, hm, hden]
  ring

theorem defect_add_reflected {a d : ℝ} (ha : 0 < a) (hd : |d| < a) :
    defect a d + defect a (-d) = 2 * d ^ 2 / (a * (a ^ 2 - d ^ 2)) := by
  have h := weighted_pair_eq ha hd 1 1
  simp only [mul_one, sub_self, mul_zero, sub_zero] at h
  exact h.trans (by ring)

theorem defect_add_reflected_nonneg {a d : ℝ} (ha : 0 < a) (hd : |d| < a) :
    0 ≤ defect a d + defect a (-d) := by
  rw [defect_add_reflected ha hd]
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_pos ha (denominator_pos ha hd)).le

theorem abs_weighted_pair_le {a d : ℝ} (ha : 0 < a) (hd : |d| ≤ a / 2) (x y : ℝ) :
    |defect a d * x + defect a (-d) * y| ≤
      (2 * d ^ 2 / a ^ 3) * |x + y| + (2 * |d| / a ^ 2) * |x - y| := by
  have hdt : |d| < a := lt_of_le_of_lt hd (by linarith)
  have hp := denominator_pos ha hdt
  have hsq : d ^ 2 ≤ a ^ 2 / 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg d) hd 2
    rw [sq_abs] at h
    nlinarith
  have hden : a ^ 2 ≤ 2 * (a ^ 2 - d ^ 2) := by nlinarith [sq_nonneg a]
  have hodd : |d| / (a ^ 2 - d ^ 2) ≤ 2 * |d| / a ^ 2 := by
    apply (div_le_div_iff₀ hp (sq_pos_of_pos ha)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden (abs_nonneg d)]
  have heven : d ^ 2 / (a * (a ^ 2 - d ^ 2)) ≤ 2 * d ^ 2 / a ^ 3 := by
    apply (div_le_div_iff₀ (mul_pos ha hp) (pow_pos ha 3)).mpr
    have h := mul_le_mul_of_nonneg_left hden (mul_nonneg ha.le (sq_nonneg d))
    nlinarith
  rw [weighted_pair_eq ha hdt]
  calc
    _ ≤ |d ^ 2 / (a * (a ^ 2 - d ^ 2)) * (x + y)| +
        |d / (a ^ 2 - d ^ 2) * (x - y)| := abs_sub _ _
    _ = (d ^ 2 / (a * (a ^ 2 - d ^ 2))) * |x + y| +
        (|d| / (a ^ 2 - d ^ 2)) * |x - y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) (mul_pos ha hp).le),
        abs_div, abs_of_pos hp]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right heven (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hodd (abs_nonneg _))

theorem abs_weighted_pair_le_ratio {a d r : ℝ} (ha : 0 < a)
    (_hr : 0 ≤ r) (hrh : r ≤ 1 / 2) (hd : |d| ≤ r * a) (x y : ℝ) :
    |defect a d * x + defect a (-d) * y| ≤
      (2 * r ^ 2 / a) * |x + y| + (2 * r / a) * |x - y| := by
  have hhalf : |d| ≤ a / 2 := by nlinarith
  have hsq : d ^ 2 ≤ (r * a) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg d) hd 2
  have heven : 2 * d ^ 2 / a ^ 3 ≤ 2 * r ^ 2 / a := by
    apply (div_le_div_iff₀ (pow_pos ha 3) ha).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsq ha.le]
  have hodd : 2 * |d| / a ^ 2 ≤ 2 * r / a := by
    apply (div_le_div_iff₀ (sq_pos_of_pos ha) ha).mpr
    nlinarith [mul_le_mul_of_nonneg_right hd ha.le]
  exact (abs_weighted_pair_le ha hhalf x y).trans (add_le_add
    (mul_le_mul_of_nonneg_right heven (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hodd (abs_nonneg _)))

theorem abs_defect_le_ratio {a d r : ℝ} (ha : 0 < a) (hr : 0 ≤ r)
    (hrh : r ≤ 1 / 2) (hd : |d| ≤ r * a) : |defect a d| ≤ 2 * r / a := by
  have hhalf : |d| ≤ a / 2 := by nlinarith
  have habs := abs_le.mp hhalf
  have hp : 0 < a + d := by linarith
  rw [defect, abs_div, abs_neg, abs_of_pos (mul_pos ha hp)]
  apply (div_le_div_iff₀ (mul_pos ha hp) ha).mpr
  have h₁ := mul_le_mul_of_nonneg_right hd ha.le
  have h₂ := mul_le_mul_of_nonneg_left habs.1 (mul_nonneg hr ha.le)
  nlinarith

end Mettapedia.Analysis.BalancedResolvent
