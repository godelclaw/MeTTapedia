import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Hessians of rotationally invariant functions

A scalar function invariant under all linear isometries has a profile in
the squared norm. Away from the origin its Hessian is a scalar identity
plus a radial rank-one form. The coefficients are derivatives of the
constructed profile, not additional hypotheses.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialHessian

open Filter
open scoped Topology ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def profile (f : E → ℝ) (e : E) (r : ℝ) : ℝ := f (Real.sqrt r • e)

theorem eq_profile_norm_sq (f : E → ℝ) (e : E) (he : ‖e‖ = 1)
    (hf : ∀ A : E ≃ₗᵢ[ℝ] E, ∀ x, f (A x) = f x) (x : E) :
    f x = profile f e (‖x‖ ^ 2) := by
  have hn : ‖x‖ = ‖‖x‖ • e‖ := by simp [norm_smul, he]
  have h := hf (Submodule.reflection (ℝ ∙ (x - ‖x‖ • e))ᗮ) x
  rw [Submodule.reflection_sub hn] at h
  simpa only [profile, Real.sqrt_sq (norm_nonneg x)] using h.symm

theorem contDiffAt_profile {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (e : E)
    {r : ℝ} (hr : r ≠ 0) : ContDiffAt ℝ ∞ (profile f e) r :=
  hf.contDiffAt.comp r ((Real.contDiffAt_sqrt hr).smul contDiffAt_const)

theorem fderiv_profile_norm_sq {g : ℝ → ℝ} {x : E}
    (hg : DifferentiableAt ℝ g (‖x‖ ^ 2)) (w : E) :
    fderiv ℝ (fun y : E ↦ g (‖y‖ ^ 2)) x w =
      2 * deriv g (‖x‖ ^ 2) * ⟪x, w⟫ := by
  have h := (hg.hasDerivAt.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt).fderiv
  simp only [Function.comp_def] at h
  rw [h]
  simp only [smul_apply, two_smul, add_apply, innerSL_apply_apply, smul_eq_mul]
  ring

theorem secondFDeriv_profile_norm_sq {g : ℝ → ℝ}
    (hg : ∀ r > 0, ContDiffAt ℝ ∞ g r) {x : E} (hx : x ≠ 0) (v w : E) :
    fderiv ℝ (fun y : E ↦ fderiv ℝ (fun z : E ↦ g (‖z‖ ^ 2)) y w) x v =
      2 * deriv g (‖x‖ ^ 2) * ⟪v, w⟫ +
        4 * deriv (deriv g) (‖x‖ ^ 2) * ⟪x, v⟫ * ⟪x, w⟫ := by
  have hp : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hd : DifferentiableAt ℝ (deriv g) (‖x‖ ^ 2) :=
    ((hg _ hp).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have h₁ := hd.hasDerivAt.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  simp only [Function.comp_def] at h₁
  have h₂ := (innerSL ℝ w).hasFDerivAt (x := x)
  have h := (h₁.const_mul 2).mul h₂
  have he : (fun y : E ↦ fderiv ℝ (fun z : E ↦ g (‖z‖ ^ 2)) y w) =ᶠ[𝓝 x]
      (fun y : E ↦ 2 * deriv g (‖y‖ ^ 2) * ⟪w, y⟫) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [fderiv_profile_norm_sq ((hg _ (sq_pos_of_pos (norm_pos_iff.mpr hy))).differentiableAt
      (by simp)), real_inner_comm y w]
  rw [(h.congr_of_eventuallyEq he).fderiv]
  simp only [add_apply, smul_apply, two_smul, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm w x, real_inner_comm w v]
  ring

theorem secondFDeriv_eq (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hrot : ∀ A : E ≃ₗᵢ[ℝ] E, ∀ x, f (A x) = f x)
    (e : E) (he : ‖e‖ = 1) {x : E} (hx : x ≠ 0) (v w : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y w) x v =
      2 * deriv (profile f e) (‖x‖ ^ 2) * ⟪v, w⟫ +
        4 * deriv (deriv (profile f e)) (‖x‖ ^ 2) * ⟪x, v⟫ * ⟪x, w⟫ := by
  have hfun : f = fun y ↦ profile f e (‖y‖ ^ 2) := funext (eq_profile_norm_sq f e he hrot)
  conv_lhs => rw [hfun]
  exact secondFDeriv_profile_norm_sq (fun r hr ↦ contDiffAt_profile hf e hr.ne') hx v w

end Mettapedia.Analysis.RadialHessian
