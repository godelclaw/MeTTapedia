import Mettapedia.Analysis.WeightedProjectionParabolic

/-!
# Moving regularization in scalar projection energy

The derivative of the minimizing coefficient still cancels, but changing
the regularization contributes its own explicit squared-coefficient term.
No monotonicity of a frequency-normalized correction is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RegularizedProjectionParameter

open scoped RealInnerProductSpace
open RegularizedProjection RegularizedProjectionParabolic WeightedProjectionParabolic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_coefficient {δ : ℝ → ℝ} {dδ : ℝ} {a b : ℝ → E}
    {da db : E} {t : ℝ} (hδ : 0 < δ t) (hd : HasDerivAt δ dδ t)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun τ ↦ coefficient (δ τ) (a τ) (b τ))
      (((⟪da, b t⟫ + ⟪a t, db⟫) * (δ t + ‖a t‖ ^ 2) -
        ⟪a t, b t⟫ * (dδ + 2 * ⟪a t, da⟫)) / (δ t + ‖a t‖ ^ 2) ^ 2) t := by
  have hden : δ t + ‖a t‖ ^ 2 ≠ 0 := by positivity
  simpa only [coefficient, add_comm] using (ha.inner ℝ hb).fun_div (hd.fun_add ha.norm_sq) hden

/-- Varying the parameter contributes `delta' * coefficient^2` in addition
to the ordinary two-field variation. -/
theorem hasDerivAt_energy {δ : ℝ → ℝ} {dδ : ℝ} {a b : ℝ → E}
    {da db : E} {t : ℝ} (hδ : 0 < δ t) (hd : HasDerivAt δ dδ t)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun τ ↦ energy (δ τ) (a τ) (b τ))
      (energyRate (δ t) (a t) (b t) da db + dδ * coefficient (δ t) (a t) (b t) ^ 2) t := by
  have hc := hasDerivAt_coefficient hδ hd ha hb
  have hr := hb.fun_sub (hc.smul ha)
  have he := hr.norm_sq.fun_add (hd.mul (hc.pow 2))
  change HasDerivAt (fun τ ↦ energy (δ τ) (a τ) (b τ)) _ t at he
  apply he.congr_deriv
  simp only [Pi.smul_apply', inner_sub_right, inner_add_right, real_inner_smul_right,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [show ⟪b t - coefficient (δ t) (a t) (b t) • a t, a t⟫ =
      δ t * coefficient (δ t) (a t) (b t) from
    (real_inner_comm _ _).trans (inner_residual _ hδ _ _)]
  unfold energyRate RegularizedProjection.residual
  simp only [Pi.pow_apply, inner_sub_right, real_inner_smul_right]
  ring

theorem hasDerivAt_weightedEnergy {δ : ℝ → ℝ} {dδ : ℝ} {a b : ℝ → E}
    {da db : E} {t : ℝ} (hδ : 0 < δ t) (hd : HasDerivAt δ dδ t)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun τ ↦ weightedEnergy (δ τ) (a τ) (b τ))
      (weightedRate (δ t) (a t) (b t) da db +
        dδ * ‖a t‖ ^ 6 * coefficient (δ t) (a t) (b t) ^ 2) t := by
  have h := (ha.norm_sq.fun_pow 3).mul (hasDerivAt_energy hδ hd ha hb)
  simp only [← pow_mul, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat] at h
  apply h.congr_deriv
  unfold weightedRate
  ring

def normalizedDensity (ν κ : ℝ) (a b : E) : ℝ :=
  ‖a‖ ^ 8 / 8 - 3 / κ * weightedEnergy (ν ^ 2 * κ ^ 2 / 3) a b

/-- The scale-motion contribution is signed: the residual part and the
regularized longitudinal part enter with opposite signs. -/
def scaleRate (ν κ dκ : ℝ) (a b : E) : ℝ :=
  (3 * dκ / κ ^ 2) * ‖a‖ ^ 6 *
    (‖residual (ν ^ 2 * κ ^ 2 / 3) a b‖ ^ 2 -
      (ν ^ 2 * κ ^ 2 / 3) * coefficient (ν ^ 2 * κ ^ 2 / 3) a b ^ 2)

theorem hasDerivAt_normalizedDensity (ν : ℝ) (hν : 0 < ν)
    {κ : ℝ → ℝ} {dκ : ℝ} {a b : ℝ → E} {da db : E} {t : ℝ}
    (hκ : 0 < κ t) (hk : HasDerivAt κ dκ t)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun τ ↦ normalizedDensity ν (κ τ) (a τ) (b τ))
      (‖a t‖ ^ 6 * ⟪a t, da⟫ - 3 / κ t *
        weightedRate (ν ^ 2 * κ t ^ 2 / 3) (a t) (b t) da db +
          scaleRate ν (κ t) dκ (a t) (b t)) t := by
  have hd := ((hk.pow 2).const_mul (ν ^ 2)).div_const 3
  have hδ : 0 < ν ^ 2 * κ t ^ 2 / 3 := by positivity
  have hW := hasDerivAt_weightedEnergy (δ := fun τ ↦ ν ^ 2 * κ τ ^ 2 / 3) (t := t) hδ hd ha hb
  have h := ((ha.norm_sq.pow 4).div_const 8).sub (((hk.inv hκ.ne').const_mul 3).mul hW)
  simp only [Pi.pow_apply, Pi.inv_apply,
    ← pow_mul, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat, pow_one] at h
  change HasDerivAt (fun τ ↦ normalizedDensity ν (κ τ) (a τ) (b τ)) _ t at h
  apply h.congr_deriv
  unfold scaleRate weightedEnergy energy
  field_simp
  ring

theorem abs_scaleRate_le (ν κ dκ : ℝ) (a b : E) :
    |scaleRate ν κ dκ a b| ≤ (3 * |dκ| / κ ^ 2) * weightedEnergy (ν ^ 2 * κ ^ 2 / 3) a b := by
  have hδ : 0 ≤ ν ^ 2 * κ ^ 2 / 3 := by positivity
  have h : |‖residual (ν ^ 2 * κ ^ 2 / 3) a b‖ ^ 2 -
      (ν ^ 2 * κ ^ 2 / 3) * coefficient (ν ^ 2 * κ ^ 2 / 3) a b ^ 2| ≤
      ‖residual (ν ^ 2 * κ ^ 2 / 3) a b‖ ^ 2 +
        (ν ^ 2 * κ ^ 2 / 3) * coefficient (ν ^ 2 * κ ^ 2 / 3) a b ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [sq_nonneg ‖residual (ν ^ 2 * κ ^ 2 / 3) a b‖,
      mul_nonneg hδ (sq_nonneg (coefficient (ν ^ 2 * κ ^ 2 / 3) a b))]
  unfold scaleRate weightedEnergy energy
  rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg (sq_nonneg κ), abs_of_nonneg (by positivity : 0 ≤ ‖a‖ ^ 6)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h
    (show 0 ≤ (3 * |dκ| / κ ^ 2) * ‖a‖ ^ 6 by positivity)

end Mettapedia.Analysis.RegularizedProjectionParameter
