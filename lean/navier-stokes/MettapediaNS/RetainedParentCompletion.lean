import MettapediaNS.PressureImpulseHistory
import MettapediaNS.PressureDiffusionCompletion
import MettapediaNS.SignedViscousPressure

/-!
# Actual geometry with retained passive and pressure-impulse parents

The actual gradient is the difference of the passive and impulse gradients.
The companion lab keeps its vorticity geometry and completes both branches
using their joint squared size. These declarations certify the scalar mixed
curvature bounds, actual-field reconstruction, continuation coercivity and
payment of the actual derivative-parent pressure source.

Full matrix differentiation and evolving-history identification remain
analytic inputs. No signed nonlinear renewal estimate is established.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RetainedParentCompletion

open MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev WholeSpaceBetchov
  WholeSpacePressureDiffusion MiddleEigenvalueAlgebra PressureImpulseHistory

theorem split_product_le (r e R E : ℝ) (hR : 0 ≤ R) (he : 0 ≤ e)
    (hr : r ≤ 2 * R) (heE : e ≤ 2 * E) : r * e ≤ 4 * R * E := by
  calc
    r * e ≤ (2 * R) * e := mul_le_mul_of_nonneg_right hr he
    _ ≤ (2 * R) * (2 * E) := mul_le_mul_of_nonneg_left heE (by positivity)
    _ = 4 * R * E := by ring

/-- Core curvature keeps the actual difference gradient. The radial
curvature and the physical negative-part bound are explicit inputs. -/
theorem completed_core_lower (r e R q E g c k : ℝ)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (he : 0 ≤ e) (hE : 0 ≤ E) (hg : 0 ≤ g)
    (hr : r ≤ 2 * R) (heE : e ≤ 2 * E)
    (hc : -(1744 / 21 : ℝ) * r * e ≤ c)
    (hk : 2 * (R + q) * E + (2 / 5 : ℝ) * g ≤ k) :
    32 * (R + q) * E + (56 / 5 : ℝ) * g ≤ c + 192 * k := by
  have hp := split_product_le r e R E hR he hr heE
  nlinarith [mul_nonneg hR hE, mul_nonneg hq hE]

/-- Both pressure slots and all joint increments remain in the input. -/
theorem completed_pressure_lower (r e R q E g p k : ℝ)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (he : 0 ≤ e) (hE : 0 ≤ E) (hg : 0 ≤ g)
    (hr : r ≤ 2 * R) (heE : e ≤ 2 * E)
    (hp : -(88 * r + 8 * q) * e - 8 * g ≤ p)
    (hk : 2 * (R + q) * E + (2 / 5 : ℝ) * g ≤ k) :
    32 * (R + q) * E + (56 / 5 : ℝ) * g ≤ p + 192 * k := by
  have hprod := split_product_le r e R E hR he hr heE
  have hqe := mul_le_mul_of_nonneg_left heE hq
  nlinarith [mul_nonneg hq hE]

theorem actual_parent_curvature (r e R q E D : ℝ)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hr : r ≤ 2 * R) (heE : e ≤ 2 * E)
    (hD : 32 * (R + q) * E ≤ D) : 8 * r * e ≤ D := by
  have hp := split_product_le r e R E hR he hr heE
  nlinarith [mul_nonneg hq hE]

theorem pressure_branch_scale (R q p : ℝ) (hp : -8 * R * q ≤ p) :
    190 * (R + q) ^ 2 ≤ p + 192 * (R + q) ^ 2 := by
  nlinarith [sq_nonneg (R - q)]

theorem branch_baseline (R q σ p c : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q)
    (hσ : σ ^ 2 ≤ q ^ 2) (hp : -8 * R * q ≤ p) (hc : 0 ≤ c) :
    192 * σ ^ 2 ≤ p + 192 * (R + q) ^ 2 ∧
      192 * σ ^ 2 ≤ c + 192 * (R + q) ^ 2 := by
  constructor <;> nlinarith [sq_nonneg R, mul_nonneg hR hq]

private theorem normSq_nonneg (A : GradMatrix) : 0 ≤ normSq A :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem impulse_gradient_entry (u H : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    gradMatrix (impulse u H) x i j = gradMatrix H x i j - gradMatrix u x i j := by
  have he : (impulse u H).field = H.field - u.field :=
    funext (fieldSub_field H u)
  simp only [gradMatrix, directionalField_field]
  rw [he, fderiv_sub (H.smooth.differentiable (by simp) x)
    (u.smooth.differentiable (by simp) x)]
  rfl

def retainedGradientSquare (u H : SmoothL2Field Space) (x : Space) : ℝ :=
  normSq (gradMatrix H x) + normSq (gradMatrix (impulse u H) x)

theorem retainedGradientSquare_nonneg (u H : SmoothL2Field Space) (x : Space) :
    0 ≤ retainedGradientSquare u H x :=
  add_nonneg (normSq_nonneg _) (normSq_nonneg _)

/-- The original actual gradient, rather than the passive gradient,
is the geometric and continuation observable. -/
theorem actual_gradient_square_le (u H : SmoothL2Field Space) (x : Space) :
    normSq (gradMatrix u x) ≤ 2 * retainedGradientSquare u H x := by
  have h (i j : Fin 3) : (gradMatrix u x i j) ^ 2 ≤
      2 * (gradMatrix H x i j) ^ 2 + 2 * (gradMatrix (impulse u H) x i j) ^ 2 := by
    rw [impulse_gradient_entry]
    nlinarith [sq_nonneg (2 * gradMatrix H x i j - gradMatrix u x i j)]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    Finset.sum_le_sum (s := Finset.univ) fun j _ ↦ h i j
  simpa only [retainedGradientSquare, normSq, Finset.sum_add_distrib,
    ← Finset.mul_sum, mul_add] using hs

theorem retainedGradientSquare_initial (u : SmoothL2Field Space) (x : Space) :
    retainedGradientSquare u u x = normSq (gradMatrix u x) := by
  simp only [retainedGradientSquare, normSq, impulse_gradient_entry, sub_self,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, add_zero]

def retainedDerivativeSquare (u H : SmoothL2Field Space) (x : Space) : ℝ :=
  ∑ k : Fin 3, retainedGradientSquare (u.directionalField (axis k))
    (H.directionalField (axis k)) x

theorem retainedDerivativeSquare_nonneg (u H : SmoothL2Field Space) (x : Space) :
    0 ≤ retainedDerivativeSquare u H x :=
  Finset.sum_nonneg fun _ _ ↦ retainedGradientSquare_nonneg _ _ _

theorem actual_parent_cost_le (u H : SmoothL2Field Space) (x : Space) :
    normSq (gradMatrix u x) *
        (∑ k : Fin 3, normSq (gradMatrix (u.directionalField (axis k)) x)) ≤
      4 * retainedGradientSquare u H x * retainedDerivativeSquare u H x := by
  have he : (∑ k : Fin 3, normSq (gradMatrix (u.directionalField (axis k)) x)) ≤
      2 * retainedDerivativeSquare u H x := by
    simpa only [retainedDerivativeSquare, ← Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦
        actual_gradient_square_le (u.directionalField (axis k)) (H.directionalField (axis k)) x)
  exact split_product_le _ _ _ _ (retainedGradientSquare_nonneg u H x)
    (Finset.sum_nonneg fun _ _ ↦ normSq_nonneg _) (actual_gradient_square_le u H x) he

/-- The literal derivative-parent pressure from the full velocity is
paid. Identification of the joint diffusion is not hidden in the conclusion. -/
theorem source_pressure_paid (u H : SmoothL2Field Space) (q D : Space → ℝ)
    {ν : ℝ} (hν : 0 ≤ ν) (hq : ∀ x, 0 ≤ q x) (hD : Integrable D)
    (hcurv : ∀ x, 32 * ν * (retainedGradientSquare u H x + q x) *
      retainedDerivativeSquare u H x ≤ D x) :
    ν * ‖(SignedViscousPressure.sourcePressure u).toLp‖ ^ 2 ≤ (∫ x, D x) / 8 := by
  apply SignedViscousPressure.source_pressure_paid u hν
  have hi := (SignedViscousPressure.parent_cost_integrable u).const_mul (8 * ν)
  have hp (x : Space) : 8 * ν * (normSq (gradMatrix u x) *
      ∑ k : Fin 3, normSq (gradMatrix (u.directionalField (axis k)) x)) ≤ D x := by
    have hc := mul_le_mul_of_nonneg_left (actual_parent_cost_le u H x)
      (show 0 ≤ 8 * ν by positivity)
    have hn := retainedDerivativeSquare_nonneg u H x
    nlinarith [hcurv x, mul_nonneg hν (mul_nonneg (hq x) hn)]
  have h := integral_mono hi hD hp
  simpa only [integral_const_mul] using h

theorem vorticity_normSq_le (A : GradMatrix) : vortSq A ≤ 2 * normSq A := by
  simp only [vortSq, vort, normSq, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  nlinarith [sq_nonneg (A 0 1 + A 1 0), sq_nonneg (A 0 2 + A 2 0),
    sq_nonneg (A 1 2 + A 2 1), sq_nonneg (A 0 0), sq_nonneg (A 1 1), sq_nonneg (A 2 2)]

/-- This is the original actual-vorticity input of the existing
whole-space soft-excess continuation adapter. -/
theorem actual_vorticity_coercivity (u H : SmoothL2Field Space) (x : Space)
    (q X : ℝ) (hq : 0 ≤ q)
    (hX : 192 * (retainedGradientSquare u H x + q) ^ 2 ≤ X) :
    12 * vortSq (gradMatrix u x) ^ 2 ≤ X := by
  have hR := retainedGradientSquare_nonneg u H x
  have hr := actual_gradient_square_le u H x
  have hv := vorticity_normSq_le (gradMatrix u x)
  have hv0 : 0 ≤ vortSq (gradMatrix u x) := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hbound : vortSq (gradMatrix u x) ≤ 4 * retainedGradientSquare u H x := by linarith
  have hs := (sq_le_sq₀ hv0 (show 0 ≤ 4 * retainedGradientSquare u H x by positivity)).2 hbound
  nlinarith [mul_nonneg hR hq, sq_nonneg q]

end Mettapedia.FluidDynamics.NavierStokes.RetainedParentCompletion
