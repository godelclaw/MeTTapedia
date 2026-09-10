import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

/-!
# Operator norm bounded by its energy on an orthonormal basis

The squared operator norm is at most the sum of squared images of an
orthonormal basis. The estimate has no dimension factor.
-/

set_option autoImplicit false
noncomputable section

namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι]

theorem norm_apply_sq_le_sum_orthonormalBasis (T : E →L[𝕜] F)
    (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ‖T x‖ ^ 2 ≤ (∑ i, ‖T (b i)‖ ^ 2) * ‖x‖ ^ 2 := by
  have ht : ‖T x‖ ≤ ∑ i, ‖⟪b i, x⟫_𝕜‖ * ‖T (b i)‖ := by
    calc
      _ = ‖∑ i, ⟪b i, x⟫_𝕜 • T (b i)‖ := by
        congr 1
        simpa only [map_sum, map_smul] using (congrArg T (b.sum_repr' x)).symm
      _ ≤ _ := by
        simpa only [norm_smul] using (norm_sum_le Finset.univ (fun i ↦ ⟪b i, x⟫_𝕜 • T (b i)))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i ↦ ‖⟪b i, x⟫_𝕜‖) (fun i ↦ ‖T (b i)‖)
  rw [b.sum_sq_norm_inner_right] at hc
  simpa only [mul_comm] using (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hc

theorem norm_sq_le_sum_orthonormalBasis (T : E →L[𝕜] F) (b : OrthonormalBasis ι 𝕜 E) :
    ‖T‖ ^ 2 ≤ ∑ i, ‖T (b i)‖ ^ 2 := by
  have hn : 0 ≤ ∑ i, ‖T (b i)‖ ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hs := Real.sq_sqrt hn
  have h : ‖T‖ ≤ Real.sqrt (∑ i, ‖T (b i)‖ ^ 2) := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg _)
    intro x
    have hx := norm_apply_sq_le_sum_orthonormalBasis T b x
    have hr : (Real.sqrt (∑ i, ‖T (b i)‖ ^ 2) * ‖x‖) ^ 2 =
        (∑ i, ‖T (b i)‖ ^ 2) * ‖x‖ ^ 2 := by rw [mul_pow, hs]
    nlinarith only [hx, hr, norm_nonneg (T x),
      mul_nonneg (Real.sqrt_nonneg (∑ i, ‖T (b i)‖ ^ 2)) (norm_nonneg x)]
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq hs

end ContinuousLinearMap
