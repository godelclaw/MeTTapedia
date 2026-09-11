import Mettapedia.Analysis.OddMapLineEstimate
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.NormNum

/-! Opposite representatives, weighted families, and the necessity of oddness. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.OddMapLineEstimateTests

open OddMapLineEstimate

example : min (‖(1 : ℝ) - (-1)‖ ^ 2) (‖(1 : ℝ) + (-1)‖ ^ 2) = 0 := by norm_num

example (e r : ℝ) (he : ‖e‖ = 1) (hr : ‖r‖ = 1) :
    ‖e‖ ^ 2 ≤ 2 * ‖r‖ ^ 2 + 2 * min (‖e - r‖ ^ 2) (‖e + r‖ ^ 2) := by
  simpa only [one_pow, mul_one] using norm_sq_le_unoriented (fun x : ℝ ↦ x)
    (fun _ ↦ rfl) 1 (fun _ _ _ _ ↦ by simp) e r he hr

/-- No factor equal to the family size enters the estimate. -/
example {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r : ι → ℝ) (hr : ∀ i, ‖r i‖ = 1) :
    (∑ i, a i) ≤ 2 * (∑ i, a i * ‖r i‖ ^ 2) +
      2 * ∑ i, a i * min (‖(1 : ℝ) - r i‖ ^ 2) (‖(1 : ℝ) + r i‖ ^ 2) := by
  simpa only [norm_one, one_pow, mul_one] using sum_weight_mul_norm_sq_le
    (fun x : ℝ ↦ x) (fun _ ↦ rfl) 1 (fun _ _ _ _ ↦ by simp)
    1 (by norm_num) r hr a ha

/-- A Lipschitz map without oddness can distinguish opposite representatives. -/
example : ¬ (‖((1 : ℝ) + 1) / 2‖ ^ 2 ≤ 2 * ‖((-1 : ℝ) + 1) / 2‖ ^ 2 +
    2 * (1 / 2 : ℝ) ^ 2 * min (‖(1 : ℝ) - (-1)‖ ^ 2) (‖(1 : ℝ) + (-1)‖ ^ 2)) := by
  norm_num

end Mettapedia.Analysis.OddMapLineEstimateTests

#print axioms Mettapedia.Analysis.OddMapLineEstimate.norm_sq_le_oriented
#print axioms Mettapedia.Analysis.OddMapLineEstimate.norm_sq_le_unoriented
#print axioms Mettapedia.Analysis.OddMapLineEstimate.sum_weight_mul_norm_sq_le
