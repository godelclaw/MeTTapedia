import Mettapedia.Analysis.BilinearKernelLocalization

/-!
# Bilinear localization controlled by squared weights

For same-sign input weights, the error between a target squared weight
and a product of two input weights is controlled by differences of squared
weights. Summing these squared differences introduces no cardinality factor.
The sign condition is essential.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SquaredWeightLocalization

theorem squaredWeight_defect_identity (a b c : ℝ) :
    (a - b ^ 2) ^ 2 + (a - c ^ 2) ^ 2 - (a - b * c) ^ 2 =
      (a - b ^ 2 - c ^ 2 + b * c) ^ 2 + 2 * (b * c) * (b - c) ^ 2 := by
  ring

theorem sq_sub_mul_le (a b c : ℝ) (hbc : 0 ≤ b * c) :
    (a - b * c) ^ 2 ≤ (a - b ^ 2) ^ 2 + (a - c ^ 2) ^ 2 := by
  have h := squaredWeight_defect_identity a b c
  have hp := mul_nonneg hbc (sq_nonneg (b - c))
  nlinarith only [h, hp, sq_nonneg (a - b ^ 2 - c ^ 2 + b * c)]

theorem sum_sq_sub_mul_le {ι : Type*} (S : Finset ι) (a b c : ι → ℝ)
    (hbc : ∀ i ∈ S, 0 ≤ b i * c i) :
    (∑ i ∈ S, (a i - b i * c i) ^ 2) ≤
      (∑ i ∈ S, (a i - b i ^ 2) ^ 2) + ∑ i ∈ S, (a i - c i ^ 2) ^ 2 := by
  simpa only [Finset.sum_add_distrib] using
    Finset.sum_le_sum (fun i hi ↦ sq_sub_mul_le (a i) (b i) (c i) (hbc i hi))

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [NormedAddCommGroup G] [NormedSpace ℂ G]

local instance : NormedAddCommGroup (F →L[ℂ] G) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (F →L[ℂ] G) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℂ] F →L[ℂ] G) := ContinuousLinearMap.toNormedAddCommGroup

theorem norm_localization_sq_le (B : E →L[ℂ] F →L[ℂ] G)
    (a b c : ℝ) (hbc : 0 ≤ b * c) (u : E) (v : F) :
    ‖((a : ℂ) * (a : ℂ)) • B u v - B ((b : ℂ) • u) ((c : ℂ) • v)‖ ^ 2 ≤
      ‖B‖ ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 *
        ((a ^ 2 - b ^ 2) ^ 2 + (a ^ 2 - c ^ 2) ^ 2) := by
  have hB : ‖B u v‖ ≤ ‖B‖ * ‖u‖ * ‖v‖ :=
    (B u).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (B.le_opNorm u) (norm_nonneg v))
  have hb := pow_le_pow_left₀ (norm_nonneg _) hB 2
  have hs := sq_sub_mul_le (a ^ 2) b c hbc
  rw [BilinearKernelLocalization.smul_sub_apply_smul]
  rw [show ((a : ℂ) * (a : ℂ) - (b : ℂ) * (c : ℂ)) = ((a ^ 2 - b * c : ℝ) : ℂ) by push_cast; ring]
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  exact (mul_le_mul hs hb (sq_nonneg _) (by positivity)).trans_eq (by ring)

theorem sum_norm_localization_sq_le {ι : Type*} (S : Finset ι)
    (B : ι → E →L[ℂ] F →L[ℂ] G) (a b c : ι → ℝ)
    (hbc : ∀ i ∈ S, 0 ≤ b i * c i) (u : E) (v : F)
    (L : ℝ) (hB : ∀ i ∈ S, ‖B i‖ ≤ L) :
    (∑ i ∈ S, ‖((a i : ℂ) * (a i : ℂ)) • B i u v -
      B i ((b i : ℂ) • u) ((c i : ℂ) • v)‖ ^ 2) ≤
      L ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 *
        ((∑ i ∈ S, (a i ^ 2 - b i ^ 2) ^ 2) + ∑ i ∈ S, (a i ^ 2 - c i ^ 2) ^ 2) := by
  calc
    _ ≤ ∑ i ∈ S, L ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 *
        ((a i ^ 2 - b i ^ 2) ^ 2 + (a i ^ 2 - c i ^ 2) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_localization_sq_le (B i) (a i) (b i) (c i) (hbc i hi) u v).trans
      gcongr
      exact hB i hi
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]

end Mettapedia.Analysis.SquaredWeightLocalization
