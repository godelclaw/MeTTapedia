import Mettapedia.Analysis.OddMapWeightedContinuity
import Mathlib.Tactic.NormNum

/-! Weighted norm continuity without any regularity of sign choices. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.OddMapWeightedContinuityTests

open OddMapLineEstimate OddMapWeightedContinuity

example : (‖(1 : ℝ)‖ - ‖(-1 : ℝ)‖) ^ 2 ≤
    min (‖(1 : ℝ) - (-1)‖ ^ 2) (‖(1 : ℝ) + (-1)‖ ^ 2) := by
  simpa only [one_pow, one_mul] using norm_sub_norm_sq_le_unoriented
    (fun x : ℝ ↦ x) (fun _ ↦ rfl) 1 (fun _ _ _ _ ↦ by simp)
    1 (-1) (by norm_num) (by norm_num)

example : |(7 : ℝ) * (‖(1 : ℝ)‖ - ‖(-1 : ℝ)‖)| ≤ 0 := by
  have h := abs_weight_mul_norm_sub_norm_le
    (fun x : ℝ ↦ x) (fun _ ↦ rfl) 1 (by norm_num) (fun _ _ _ _ ↦ by simp)
    1 (-1) (by norm_num) (by norm_num) 7 0 (by norm_num) (by norm_num)
  simpa only [mul_zero] using h

/-- Even a nonmeasurable sign selection is allowed. The weighted scalar
output is continuous because the map is odd and its norm is sign-invariant. -/
example (sign : ℝ → Bool) :
    Continuous (fun x : ℝ ↦ x * ‖if sign x then (1 : ℝ) else -1‖) := by
  apply continuous_weighted_norm (fun d (_ : ℝ) ↦ d) (fun _ _ ↦ rfl)
    1 (by norm_num) (fun _ _ _ _ _ ↦ by simp) (fun _ _ ↦ continuous_const)
    (fun x : ℝ ↦ x) continuous_id (fun x ↦ if sign x then (1 : ℝ) else -1)
    (fun x ↦ by split_ifs <;> norm_num) (fun x : ℝ ↦ x) continuous_id
  intro x y
  split_ifs <;> norm_num <;> exact sq_nonneg _

end Mettapedia.Analysis.OddMapWeightedContinuityTests

#print axioms Mettapedia.Analysis.OddMapLineEstimate.norm_sub_norm_sq_le_unoriented
#print axioms Mettapedia.Analysis.OddMapLineEstimate.abs_weight_mul_norm_sub_norm_le
#print axioms Mettapedia.Analysis.OddMapWeightedContinuity.continuous_weighted_norm
