import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTiltEnergy

/-!
# The order-zero pressure-tilt symbol

Factoring the Laplacian-pressure coefficient out of the tilt leaves an
even, real vector symbol. It is small on a transverse cone and varies by
at most four times the relative frequency displacement. The latter
estimate also allows the displaced frequency to be zero.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTiltSymbol

open scoped RealInnerProductSpace
open NormedSpace PancakeAnisotropyDepletion PancakeFrequencyProjectorCommutator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def tiltSymbol (e k : E) : E := (⟪k, e⟫ / ‖k‖ ^ 2) • lineRemainder e k

theorem tiltSymbol_zero (e : E) : tiltSymbol e 0 = 0 := by simp [tiltSymbol, lineRemainder]

theorem tiltSymbol_neg (e k : E) : tiltSymbol e (-k) = tiltSymbol e k := by
  simp only [tiltSymbol, inner_neg_left, norm_neg, neg_div, lineRemainder,
    inner_neg_right, neg_smul, sub_neg_eq_add, smul_add, smul_neg, neg_neg]
  module

theorem norm_sq_smul_tiltSymbol (e k : E) :
    ‖k‖ ^ 2 • tiltSymbol e k = ⟪k, e⟫ • lineRemainder e k := by
  by_cases hk : k = 0
  · simp [hk, tiltSymbol_zero]
  · unfold tiltSymbol
    rw [smul_smul, mul_div_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hk))]

theorem norm_tiltSymbol_sq_le (e k : E) (he : ‖e‖ = 1) (eta : ℝ)
    (hcone : ⟪k, e⟫ ^ 2 ≤ eta ^ 2 * ‖k‖ ^ 2) : ‖tiltSymbol e k‖ ^ 2 ≤ eta ^ 2 := by
  by_cases hk : k = 0
  · simp only [hk, tiltSymbol_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg eta
  · have hn := norm_pos_iff.mpr hk
    have hr := pow_le_pow_left₀ (norm_nonneg _) (norm_lineRemainder_le e k he) 2
    have h := mul_le_mul hcone hr (sq_nonneg _) (by positivity)
    rw [tiltSymbol, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < (‖k‖ ^ 2) ^ 2)).mpr
    nlinarith only [h]

theorem norm_tiltSymbol_le_one (e k : E) (he : ‖e‖ = 1) : ‖tiltSymbol e k‖ ≤ 1 := by
  have hi := abs_real_inner_le_norm k e
  rw [he, mul_one] at hi
  have hcone : ⟪k, e⟫ ^ 2 ≤ (1 : ℝ) ^ 2 * ‖k‖ ^ 2 := by
    nlinarith only [pow_le_pow_left₀ (abs_nonneg _) hi 2, sq_abs ⟪k, e⟫]
  have h := norm_tiltSymbol_sq_le e k he 1 hcone
  nlinarith only [h, norm_nonneg (tiltSymbol e k)]

theorem tiltSymbol_eq_remainder_projector (e k : E) :
    tiltSymbol e k = lineRemainder e (InnerProductSpace.rankOne ℝ (normalize k) (normalize k) e) := by
  simp only [tiltSymbol, InnerProductSpace.rankOne_apply, NormedSpace.normalize,
    real_inner_smul_left, lineRemainder_smul, smul_smul]
  congr 1
  ring

theorem norm_real_unitProjector_sub_le (k l : E) (hk : ‖k‖ = 1) (hl : ‖l‖ = 1) :
    ‖InnerProductSpace.rankOne ℝ k k - InnerProductSpace.rankOne ℝ l l‖ ≤ 2 * ‖k - l‖ := by
  have h : InnerProductSpace.rankOne ℝ k k - InnerProductSpace.rankOne ℝ l l =
      InnerProductSpace.rankOne ℝ (k - l) k + InnerProductSpace.rankOne ℝ l (k - l) := by
    ext x
    simp only [sub_apply, add_apply, InnerProductSpace.rankOne_apply, inner_sub_left, sub_smul]
    module
  rw [h]
  have hn := norm_add_le (InnerProductSpace.rankOne ℝ (k - l) k) (InnerProductSpace.rankOne ℝ l (k - l))
  simpa only [InnerProductSpace.norm_rankOne, hk, hl, mul_one, one_mul, two_mul] using hn

theorem norm_tiltSymbol_sub_le (e k l : E) (he : ‖e‖ = 1) (hk : k ≠ 0) :
    ‖tiltSymbol e k - tiltSymbol e l‖ ≤ 4 * ‖k - l‖ / ‖k‖ := by
  by_cases hl : l = 0
  · rw [hl, tiltSymbol_zero, sub_zero, sub_zero, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hk)]
    exact (norm_tiltSymbol_le_one e k he).trans (by norm_num)
  · let P := fun v : E ↦ InnerProductSpace.rankOne ℝ (normalize v) (normalize v)
    have hid : tiltSymbol e k - tiltSymbol e l = lineRemainder e ((P k - P l) e) := by
      rw [tiltSymbol_eq_remainder_projector, tiltSymbol_eq_remainder_projector]
      simp only [P, lineRemainder, sub_apply, inner_sub_right, sub_smul]
      abel
    have h1 := norm_real_unitProjector_sub_le (normalize k) (normalize l) (norm_normalize hk) (norm_normalize hl)
    have h2 := norm_normalize_sub_le k l hk hl
    rw [hid]
    calc
      _ ≤ ‖(P k - P l) e‖ := norm_lineRemainder_le _ _ he
      _ ≤ ‖P k - P l‖ := by simpa only [he, mul_one] using (P k - P l).le_opNorm e
      _ ≤ 2 * ‖normalize k - normalize l‖ := h1
      _ ≤ 2 * (2 * ‖k - l‖ / ‖k‖) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PressureTiltSymbol
