import Mettapedia.Analysis.BalancedResolvent

/-!
# Stability of reflected resolvent cancellation

Two shifts need not be exact negatives. Their sum is retained as a
separate error, in addition to the difference between the two tests.
-/

noncomputable section

namespace Mettapedia.Analysis.BalancedResolvent

theorem defect_sub_defect {a d e : ℝ} (ha : a ≠ 0)
    (hd : a + d ≠ 0) (he : a + e ≠ 0) :
    defect a d - defect a e = (e - d) / ((a + d) * (a + e)) := by
  unfold defect
  field_simp
  ring

theorem abs_defect_sub_le {a d e : ℝ} (ha : 0 < a)
    (hd : |d| ≤ a / 2) (he : |e| ≤ a / 2) :
    |defect a d - defect a e| ≤ 4 * |d - e| / a ^ 2 := by
  have hd' := (abs_le.mp hd).1
  have he' := (abs_le.mp he).1
  have hdp : 0 < a + d := by linarith
  have hep : 0 < a + e := by linarith
  have hprod : a ^ 2 / 4 ≤ (a + d) * (a + e) := by
    have h := mul_le_mul (show a / 2 ≤ a + d by linarith)
      (show a / 2 ≤ a + e by linarith) (by positivity : 0 ≤ a / 2) hdp.le
    nlinarith
  rw [defect_sub_defect ha.ne' hdp.ne' hep.ne', abs_div,
    abs_of_pos (mul_pos hdp hep), abs_sub_comm e d]
  apply (div_le_div_iff₀ (mul_pos hdp hep) (sq_pos_of_pos ha)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hprod (abs_nonneg (d - e))]

/-- Approximate reflection preserves the quadratic channel, with its error exposed. -/
theorem abs_near_reflected_pair_le {a d e r : ℝ} (ha : 0 < a)
    (hr : 0 ≤ r) (hrh : r ≤ 1 / 2) (hd : |d| ≤ r * a)
    (he : |e| ≤ a / 2) (x y : ℝ) :
    |defect a d * x + defect a e * y| ≤
      (2 * r ^ 2 / a) * |x + y| + (2 * r / a) * |x - y| +
        (4 * |d + e| / a ^ 2) * |y| := by
  have hdn : |-d| ≤ a / 2 := by rw [abs_neg]; nlinarith
  have hs := abs_defect_sub_le ha he hdn
  rw [sub_neg_eq_add, add_comm e d] at hs
  have hid : defect a d * x + defect a e * y =
      (defect a d * x + defect a (-d) * y) +
        (defect a e - defect a (-d)) * y := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  apply add_le_add (abs_weighted_pair_le_ratio ha hr hrh hd x y)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right hs (abs_nonneg y)

end Mettapedia.Analysis.BalancedResolvent
