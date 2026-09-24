import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Regularized scalar projection and its moving minimum

The minimizer of `norm (b - c • a)^2 + delta * c^2` is well-defined even
at `a = 0` when `delta > 0`. Along differentiable curves the derivative of
the minimum has no derivative of the minimizing coefficient. This is an
exact cancellation, not a claim that the coefficient is constant.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RegularizedProjection

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def coefficient (δ : ℝ) (a b : E) : ℝ := ⟪a, b⟫ / (δ + ‖a‖ ^ 2)

def residual (δ : ℝ) (a b : E) : E := b - coefficient δ a b • a

def energy (δ : ℝ) (a b : E) : ℝ := ‖residual δ a b‖ ^ 2 + δ * coefficient δ a b ^ 2

theorem inner_residual (δ : ℝ) (hδ : 0 < δ) (a b : E) :
    ⟪a, residual δ a b⟫ = δ * coefficient δ a b := by
  have hden : δ + ‖a‖ ^ 2 ≠ 0 := by positivity
  simp only [residual, coefficient, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem energy_nonneg (δ : ℝ) (hδ : 0 ≤ δ) (a b : E) : 0 ≤ energy δ a b := by
  unfold energy
  positivity

theorem inner_residual_eq_energy (δ : ℝ) (hδ : 0 < δ) (a b : E) :
    ⟪residual δ a b, b⟫ = energy δ a b := by
  have hb : b = residual δ a b + coefficient δ a b • a := by simp [residual]
  have hi : ⟪residual δ a b, a⟫ = δ * coefficient δ a b :=
    (real_inner_comm _ _).trans (inner_residual δ hδ a b)
  calc
    _ = ⟪residual δ a b, residual δ a b + coefficient δ a b • a⟫ :=
      congrArg (fun z ↦ ⟪residual δ a b, z⟫) hb
    _ = _ := by
      simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hi, energy]
      ring

/-- Exact excess above the regularized minimum, with no condition on the
trial coefficient. -/
theorem objective_eq_energy_add_sq (δ : ℝ) (hδ : 0 < δ) (a b : E) (c : ℝ) :
    ‖b - c • a‖ ^ 2 + δ * c ^ 2 =
      energy δ a b + (δ + ‖a‖ ^ 2) * (c - coefficient δ a b) ^ 2 := by
  have hden : δ + ‖a‖ ^ 2 ≠ 0 := by positivity
  simp only [energy, residual, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_right, coefficient, real_inner_comm b a]
  field_simp
  ring

theorem energy_le_objective (δ : ℝ) (hδ : 0 < δ) (a b : E) (c : ℝ) :
    energy δ a b ≤ ‖b - c • a‖ ^ 2 + δ * c ^ 2 := by
  rw [objective_eq_energy_add_sq δ hδ]
  exact le_add_of_nonneg_right (by positivity)

theorem energy_le_norm_sq (δ : ℝ) (hδ : 0 < δ) (a b : E) : energy δ a b ≤ ‖b‖ ^ 2 := by
  simpa only [zero_smul, sub_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using
    energy_le_objective δ hδ a b 0

theorem energy_eq (δ : ℝ) (hδ : 0 < δ) (a b : E) :
    energy δ a b = ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 / (δ + ‖a‖ ^ 2) := by
  have h := objective_eq_energy_add_sq δ hδ a b 0
  have hden : δ + ‖a‖ ^ 2 ≠ 0 := by positivity
  simp only [zero_smul, sub_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero,
    zero_sub, neg_sq, coefficient] at h
  field_simp at h ⊢
  nlinarith only [h]

/-- A sharp bound for the residual component along the projection vector.
The factor `delta / 4` is independent of both vector magnitudes. -/
theorem inner_residual_sq_le (δ : ℝ) (hδ : 0 < δ) (a b : E) :
    ⟪a, residual δ a b⟫ ^ 2 ≤ δ / 4 * ‖b‖ ^ 2 := by
  have hden : 0 < δ + ‖a‖ ^ 2 := by positivity
  have hi : ⟪a, b⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    simpa only [sq, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le a b
  rw [inner_residual δ hδ, coefficient, mul_pow, div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
  have h1 := mul_le_mul_of_nonneg_left hi (sq_nonneg δ)
  have h2 := mul_nonneg (sq_nonneg (δ - ‖a‖ ^ 2)) (mul_nonneg hδ.le (sq_nonneg ‖b‖))
  nlinarith only [h1, h2]

theorem hasDerivAt_coefficient (δ : ℝ) (hδ : 0 < δ) {a b : ℝ → E} {da db : E} {t : ℝ}
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun τ ↦ coefficient δ (a τ) (b τ))
      (((⟪da, b t⟫ + ⟪a t, db⟫) * (δ + ‖a t‖ ^ 2) -
          ⟪a t, b t⟫ * (2 * ⟪a t, da⟫)) / (δ + ‖a t‖ ^ 2) ^ 2) t := by
  have hden : δ + ‖a t‖ ^ 2 ≠ 0 := by positivity
  simpa only [coefficient, zero_add, add_comm] using
    (ha.inner ℝ hb).fun_div ((hasDerivAt_const t δ).fun_add ha.norm_sq) hden

/-- The derivative of the minimizing coefficient cancels from the energy
balance because `inner a residual = delta * coefficient`. -/
theorem hasDerivAt_energy (δ : ℝ) (hδ : 0 < δ) {a b : ℝ → E} {da db : E} {t : ℝ}
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun τ ↦ energy δ (a τ) (b τ))
      (2 * ⟪residual δ (a t) (b t), db - coefficient δ (a t) (b t) • da⟫) t := by
  have hc := hasDerivAt_coefficient δ hδ ha hb
  have hr := hb.fun_sub (hc.smul ha)
  have he := hr.norm_sq.fun_add ((hc.pow 2).const_mul δ)
  change HasDerivAt (fun τ ↦ energy δ (a τ) (b τ)) _ t at he
  apply he.congr_deriv
  simp only [Pi.smul_apply', inner_sub_right, inner_add_right, real_inner_smul_right,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [show ⟪b t - coefficient δ (a t) (b t) • a t, a t⟫ =
      δ * coefficient δ (a t) (b t) from (real_inner_comm _ _).trans (inner_residual δ hδ _ _)]
  unfold residual
  ring

end Mettapedia.Analysis.RegularizedProjection
