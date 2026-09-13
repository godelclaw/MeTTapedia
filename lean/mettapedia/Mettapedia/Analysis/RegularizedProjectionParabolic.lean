import Mettapedia.Analysis.RegularizedProjection

/-!
# Second derivatives of the regularized projection coefficient

The quotient's second derivative differs from its linear response to second
derivatives of the input fields. The difference consists of a drift term
and a signed first-derivative pairing. It is not scalar diffusion alone.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RegularizedProjectionParabolic

open scoped RealInnerProductSpace
open RegularizedProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def coefficientRate (δ : ℝ) (a b v z : E) : ℝ :=
  (⟪v, b⟫ + ⟪a, z⟫ - 2 * coefficient δ a b * ⟪a, v⟫) / (δ + ‖a‖ ^ 2)

def coefficientSecondRate (δ : ℝ) (a b v z aa bb : E) : ℝ :=
  coefficientRate δ a b aa bb -
    (4 * ⟪a, v⟫ / (δ + ‖a‖ ^ 2)) * coefficientRate δ a b v z +
    2 * (⟪v, z⟫ - coefficient δ a b * ‖v‖ ^ 2) / (δ + ‖a‖ ^ 2)

theorem hasDerivAt_coefficient (δ : ℝ) (hδ : 0 < δ) {a b : ℝ → E} {v z : E} {t : ℝ}
    (ha : HasDerivAt a v t) (hb : HasDerivAt b z t) :
    HasDerivAt (fun τ ↦ coefficient δ (a τ) (b τ)) (coefficientRate δ (a t) (b t) v z) t := by
  apply (RegularizedProjection.hasDerivAt_coefficient δ hδ ha hb).congr_deriv
  have hd : δ + ‖a t‖ ^ 2 ≠ 0 := by positivity
  simp only [coefficientRate, coefficient]
  field_simp

theorem hasDerivAt_coefficientRate (δ : ℝ) (hδ : 0 < δ)
    {a b v z : ℝ → E} {aa bb : E} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hb : HasDerivAt b (z t) t)
    (hv : HasDerivAt v aa t) (hz : HasDerivAt z bb t) :
    HasDerivAt (fun τ ↦ coefficientRate δ (a τ) (b τ) (v τ) (z τ))
      (coefficientSecondRate δ (a t) (b t) (v t) (z t) aa bb) t := by
  have hc := hasDerivAt_coefficient δ hδ ha hb
  have hd : δ + ‖a t‖ ^ 2 ≠ 0 := by positivity
  have h := (((hv.inner ℝ hb).add (ha.inner ℝ hz)).sub
    ((hc.const_mul 2).mul (ha.inner ℝ hv))).fun_div ((hasDerivAt_const t δ).add ha.norm_sq) hd
  apply h.congr_deriv
  simp only [coefficientSecondRate, coefficientRate, coefficient, real_inner_self_eq_norm_sq,
    zero_add, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  field_simp
  ring

/-- The exact non-diffusive correction in the coefficient's second derivative. -/
theorem linearRate_eq_secondRate_add (δ : ℝ) (a b v z aa bb : E) :
    coefficientRate δ a b aa bb = coefficientSecondRate δ a b v z aa bb +
      (4 * ⟪a, v⟫ / (δ + ‖a‖ ^ 2)) * coefficientRate δ a b v z +
      2 * (coefficient δ a b * ‖v‖ ^ 2 - ⟪v, z⟫) / (δ + ‖a‖ ^ 2) := by
  unfold coefficientSecondRate
  ring

theorem coefficientRate_eq_residual (δ : ℝ) (a b v z : E) :
    coefficientRate δ a b v z =
      (⟪residual δ a b, v⟫ + ⟪a, z - coefficient δ a b • v⟫) / (δ + ‖a‖ ^ 2) := by
  simp only [coefficientRate, RegularizedProjection.residual, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm b v]
  ring

def energyRate (δ : ℝ) (a b v z : E) : ℝ :=
  2 * ⟪RegularizedProjection.residual δ a b, z - coefficient δ a b • v⟫

/-- The Hessian correction for the moving minimum. The second term has
the opposite sign from ordinary vector-valued heat dissipation. -/
def energyCurvature (δ : ℝ) (a b v z : E) : ℝ :=
  2 * ‖z - coefficient δ a b • v‖ ^ 2 -
    2 * (δ + ‖a‖ ^ 2) * coefficientRate δ a b v z ^ 2

theorem hasDerivAt_energyRate (δ : ℝ) (hδ : 0 < δ)
    {a b v z : ℝ → E} {aa bb : E} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hb : HasDerivAt b (z t) t)
    (hv : HasDerivAt v aa t) (hz : HasDerivAt z bb t) :
    HasDerivAt (fun τ ↦ energyRate δ (a τ) (b τ) (v τ) (z τ))
      (energyRate δ (a t) (b t) aa bb + energyCurvature δ (a t) (b t) (v t) (z t)) t := by
  have hc := hasDerivAt_coefficient δ hδ ha hb
  have h := ((hb.fun_sub (hc.smul ha)).inner ℝ (hz.fun_sub (hc.smul hv))).const_mul 2
  apply h.congr_deriv
  have hd : δ + ‖a t‖ ^ 2 ≠ 0 := by positivity
  simp only [energyRate, energyCurvature, RegularizedProjection.residual, coefficientRate,
    coefficient, Pi.smul_apply', inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_self_eq_norm_sq, real_inner_comm (v t) (a t),
    real_inner_comm (b t) (a t), real_inner_comm (z t) (a t), real_inner_comm (v t) (b t),
    real_inner_comm (z t) (v t)]
  field_simp
  ring

/-- Completing the rank-one square bounds the possible negative curvature. -/
theorem square_div_le (δ : ℝ) (hδ : 0 < δ) (a e : E) (c : ℝ) :
    (c + ⟪a, e⟫) ^ 2 / (δ + ‖a‖ ^ 2) ≤ ‖e‖ ^ 2 + c ^ 2 / δ := by
  have hd : 0 < δ + ‖a‖ ^ 2 := by positivity
  have hn : 0 ≤ δ ^ 2 * ‖e‖ ^ 2 + c ^ 2 * ‖a‖ ^ 2 - 2 * δ * c * ⟪a, e⟫ := by
    have h := sq_nonneg ‖δ • e - c • a‖
    simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right] at h
    rw [real_inner_comm a e] at h
    nlinarith only [h]
  have hcs : ⟪a, e⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖e‖ ^ 2 := by
    simpa only [sq, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le a e
  have hp := mul_nonneg hδ.le (sub_nonneg.mpr hcs)
  apply (div_le_iff₀ hd).mpr
  have he : (‖e‖ ^ 2 + c ^ 2 / δ) * (δ + ‖a‖ ^ 2) =
      ((δ * ‖e‖ ^ 2 + c ^ 2) * (δ + ‖a‖ ^ 2)) / δ := by field_simp
  rw [he]
  apply (le_div_iff₀ hδ).mpr
  nlinarith only [hn, hp]

theorem energyCurvature_ge (δ : ℝ) (hδ : 0 < δ) (a b v z : E) :
    -(2 / δ) * ⟪RegularizedProjection.residual δ a b, v⟫ ^ 2 ≤ energyCurvature δ a b v z := by
  have hd : δ + ‖a‖ ^ 2 ≠ 0 := by positivity
  have h := square_div_le δ hδ a (z - coefficient δ a b • v)
    ⟪RegularizedProjection.residual δ a b, v⟫
  have he : (δ + ‖a‖ ^ 2) * coefficientRate δ a b v z ^ 2 =
      (⟪RegularizedProjection.residual δ a b, v⟫ + ⟪a, z - coefficient δ a b • v⟫) ^ 2 /
        (δ + ‖a‖ ^ 2) := by
    rw [coefficientRate_eq_residual]
    field_simp
  unfold energyCurvature
  rw [show 2 * (δ + ‖a‖ ^ 2) * coefficientRate δ a b v z ^ 2 =
      2 * ((δ + ‖a‖ ^ 2) * coefficientRate δ a b v z ^ 2) by ring, he]
  calc
    -(2 / δ) * ⟪RegularizedProjection.residual δ a b, v⟫ ^ 2 =
        -2 * (⟪RegularizedProjection.residual δ a b, v⟫ ^ 2 / δ) := by ring
    _ ≤ _ := by linarith only [h]

end Mettapedia.Analysis.RegularizedProjectionParabolic
