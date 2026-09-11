import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! # Quantitative normalization with zero vectors retained -/

set_option autoImplicit false

namespace Mettapedia.Analysis

open NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_normalize_le_one (x : E) : ‖normalize x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (norm_normalize hx).le

/-- Multiplication by the reference radius permits either vector to be
zero. Division is needed only when a positive reference radius is known. -/
theorem norm_normalize_sub_mul_norm_le (x y : E) :
    ‖normalize x - normalize y‖ * ‖x‖ ≤ 2 * ‖x - y‖ := by
  have he : ‖x‖ • (normalize x - normalize y) =
      (x - y) + (‖y‖ - ‖x‖) • normalize y := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  calc
    _ = ‖‖x‖ • (normalize x - normalize y)‖ := by rw [norm_smul, norm_norm]; ring
    _ ≤ ‖x - y‖ + ‖(‖y‖ - ‖x‖) • normalize y‖ := by rw [he]; exact norm_add_le _ _
    _ ≤ ‖x - y‖ + |‖y‖ - ‖x‖| := by
      rw [norm_smul, Real.norm_eq_abs]
      apply add_le_add le_rfl
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (norm_normalize_le_one y) (abs_nonneg (‖y‖ - ‖x‖))
    _ ≤ _ := by
      have h := abs_norm_sub_norm_le y x
      rw [norm_sub_rev] at h
      linarith

end Mettapedia.Analysis
