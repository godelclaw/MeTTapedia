import Mettapedia.Analysis.AnnularRieszKernel

/-!
# Cutoff-independent decay away from the Riesz kernel singularity

One additional spatial power beyond the dimension makes the dyadic
pointwise majorants summable. The estimate is deliberately non-sharp
near the origin and is used only for separated interactions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AnnularRieszKernel

open SchwartzDilation
open scoped SchwartzMap

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

def decayBound (i j : Fin d) : ℝ :=
  4 * SchwartzMap.seminorm ℝ (d + 1) 0 (kernel i j)

theorem decayBound_nonneg (i j : Fin d) : 0 ≤ decayBound i j := by
  unfold decayBound
  positivity

theorem pow_mul_norm_dyadicKernel_le (i j : Fin d) (n : ℕ) (x : Rd) :
    ‖x‖ ^ (d + 1) * ‖dyadicKernel i j n x‖ ≤
      (scale n)⁻¹ * SchwartzMap.seminorm ℝ (d + 1) 0 (kernel i j) := by
  have hr := scale_pos n
  have he : ‖x‖ ^ (d + 1) * ‖dyadicKernel i j n x‖ =
      (scale n)⁻¹ * (‖scale n • x‖ ^ (d + 1) * ‖kernel i j (scale n • x)‖) := by
    simp only [dyadicKernel, dilate_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, finrank_euclideanSpace_fin,
      abs_pow, mul_pow, pow_succ]
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (SchwartzMap.norm_pow_mul_le_seminorm ℝ (kernel i j) (d + 1) (scale n • x))
    (inv_nonneg.mpr hr.le)

theorem pow_mul_norm_partialKernel_le (i j : Fin d) (N : ℕ) (x : Rd) :
    ‖x‖ ^ (d + 1) * ‖partialKernel i j N x‖ ≤ decayBound i j := by
  have hs : (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) ≤ 2 := by
    have h := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    have hb := h.summable.sum_le_tsum (Finset.range N) (fun n _ ↦ by positivity)
    rw [h.tsum_eq] at hb
    norm_num at hb
    exact hb
  calc
    _ ≤ ‖x‖ ^ (d + 1) * ∑ n ∈ Finset.range N, ‖dyadicKernel i j n x‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [partialKernel, sum_apply] using
        norm_sum_le (Finset.range N) (fun n ↦ dyadicKernel i j n x)
    _ = ∑ n ∈ Finset.range N, ‖x‖ ^ (d + 1) * ‖dyadicKernel i j n x‖ :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ n ∈ Finset.range N,
        (scale n)⁻¹ * SchwartzMap.seminorm ℝ (d + 1) 0 (kernel i j) :=
      Finset.sum_le_sum (fun n _ ↦ pow_mul_norm_dyadicKernel_le i j n x)
    _ = (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) *
        (2 * SchwartzMap.seminorm ℝ (d + 1) 0 (kernel i j)) := by
      simp only [inv_scale, mul_assoc, Finset.sum_mul]
    _ ≤ 2 * (2 * SchwartzMap.seminorm ℝ (d + 1) 0 (kernel i j)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = decayBound i j := by unfold decayBound; ring

theorem norm_partialKernel_le (i j : Fin d) (N : ℕ) (x : Rd) (hx : x ≠ 0) :
    ‖partialKernel i j N x‖ ≤ decayBound i j * ‖x‖⁻¹ ^ (d + 1) := by
  have hp : 0 < ‖x‖ ^ (d + 1) := pow_pos (norm_pos_iff.mpr hx) _
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
  exact pow_mul_norm_partialKernel_le i j N x

end Mettapedia.Analysis.AnnularRieszKernel
