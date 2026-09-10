import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnisotropyDepletion

/-!
# Freezing the direction in a transverse operator action

Unit directions may be compared without a spectral gap. The error is
linear in their distance; the squared error is quadratic. No continuity
of an eigenvector selection is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing

open scoped RealInnerProductSpace
open PancakeAnisotropyDepletion PancakeSpectralDefectEvolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem abs_rayleigh_sub_le (R : E →L[ℝ] E) (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    |⟪e, R e⟫ - ⟪f, R f⟫| ≤ 2 * ‖R‖ * ‖e - f‖ := by
  have hid : ⟪e, R e⟫ - ⟪f, R f⟫ = ⟪e - f, R e⟫ + ⟪f, R (e - f)⟫ := by
    simp only [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [hid]
  have h1 := abs_inner_operator_le R (e - f) e
  have h2 := abs_inner_operator_le R f (e - f)
  rw [he, mul_one] at h1
  rw [hf, mul_one] at h2
  exact (abs_add_le _ _).trans (by linarith only [h1, h2])

theorem norm_transverse_action_sub_le (R : E →L[ℝ] E) (e f : E)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    ‖lineRemainder e (R e) - lineRemainder f (R f)‖ ≤ 4 * ‖R‖ * ‖e - f‖ := by
  have hid : lineRemainder e (R e) - lineRemainder f (R f) =
      R (e - f) - ⟪e, R e⟫ • (e - f) - (⟪e, R e⟫ - ⟪f, R f⟫) • f := by
    simp only [lineRemainder, map_sub, smul_sub, sub_smul]
    abel
  have h1 : |⟪e, R e⟫| ≤ ‖R‖ := by
    simpa only [he, mul_one] using abs_inner_operator_le R e e
  have h2 := abs_rayleigh_sub_le R e f he hf
  rw [hid]
  calc
    _ ≤ ‖R (e - f) - ⟪e, R e⟫ • (e - f)‖ + ‖(⟪e, R e⟫ - ⟪f, R f⟫) • f‖ := norm_sub_le _ _
    _ ≤ ‖R (e - f)‖ + ‖⟪e, R e⟫ • (e - f)‖ + ‖(⟪e, R e⟫ - ⟪f, R f⟫) • f‖ := by
      exact add_le_add (norm_sub_le (R (e - f)) (⟪e, R e⟫ • (e - f))) le_rfl
    _ = ‖R (e - f)‖ + |⟪e, R e⟫| * ‖e - f‖ + |⟪e, R e⟫ - ⟪f, R f⟫| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hf, mul_one]
    _ ≤ _ := by nlinarith only [R.le_opNorm (e - f),
      mul_le_mul_of_nonneg_right h1 (norm_nonneg (e - f)), h2]

theorem norm_transverse_action_sq_le_frozen (R : E →L[ℝ] E) (e f : E)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    ‖lineRemainder e (R e)‖ ^ 2 ≤ 2 * ‖lineRemainder f (R f)‖ ^ 2 +
      32 * ‖R‖ ^ 2 * ‖e - f‖ ^ 2 := by
  have hn := norm_le_norm_sub_add (lineRemainder e (R e)) (lineRemainder f (R f))
  have h := hn.trans (add_le_add (norm_transverse_action_sub_le R e f he hf) le_rfl)
  have hp := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith only [hp, sq_nonneg (‖lineRemainder f (R f)‖ - 4 * ‖R‖ * ‖e - f‖)]

def lineDistanceSq (e f : E) : ℝ := min (‖e - f‖ ^ 2) (‖e + f‖ ^ 2)

theorem transverse_action_neg (R : E →L[ℝ] E) (e : E) :
    lineRemainder (-e) (R (-e)) = -lineRemainder e (R e) := by
  simp only [lineRemainder, map_neg, inner_neg_left, inner_neg_right, neg_neg, smul_neg]
  abel

theorem norm_transverse_action_sq_le_lineDistance (R : E →L[ℝ] E) (e f : E)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    ‖lineRemainder e (R e)‖ ^ 2 ≤ 2 * ‖lineRemainder f (R f)‖ ^ 2 +
      32 * ‖R‖ ^ 2 * lineDistanceSq e f := by
  by_cases h : ‖e - f‖ ^ 2 ≤ ‖e + f‖ ^ 2
  · rw [lineDistanceSq, min_eq_left h]
    exact norm_transverse_action_sq_le_frozen R e f he hf
  · rw [lineDistanceSq, min_eq_right (le_of_not_ge h)]
    simpa only [transverse_action_neg, norm_neg, sub_neg_eq_add] using
      norm_transverse_action_sq_le_frozen R e (-f) he (by simpa only [norm_neg] using hf)

end Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing
