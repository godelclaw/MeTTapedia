import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Squared norm bounds for finite linear combinations -/

set_option autoImplicit false

namespace Finset

variable {ι E 𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem norm_sum_smul_sq_le (s : Finset ι) (a : ι → 𝕜) (v : ι → E) :
    ‖∑ i ∈ s, a i • v i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s (fun i ↦ a i • v i)) 2
  simp only [norm_smul] at hn
  exact hn.trans (sum_mul_sq_le_sq_mul_sq s (fun i ↦ ‖a i‖) (fun i ↦ ‖v i‖))

theorem norm_sum_sq_le_card_mul_sum_norm_sq (s : Finset ι) (v : ι → E) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq s (fun _ ↦ (1 : ℝ)) (fun i ↦ ‖v i‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s v) 2).trans h

end Finset
