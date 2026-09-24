import Mettapedia.Analysis.OperatorQuadraticForm
import Mettapedia.Analysis.SecondDerivative

/-!
# Second-order positivity at the kernel of a positive operator curve

Testing a positive symmetric operator curve on an affine vector curve
through a kernel vector couples operator curvature to its first derivative.
Only local positivity, symmetry, and `C²` regularity are used.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PositiveOperatorKernelCurvature

open scoped Topology ContDiff RealInnerProductSpace
open OperatorQuadraticForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem second_order_form_nonneg {A : ℝ → H →L[ℝ] H} {t : ℝ}
    (hA : ContDiffAt ℝ 2 A t)
    (hs : ∀ᶠ τ in 𝓝 t, ∀ a b, ⟪A τ a, b⟫ = ⟪a, A τ b⟫)
    (hp : ∀ᶠ τ in 𝓝 t, ∀ w, 0 ≤ ⟪w, A τ w⟫)
    (w v : H) (hw : A t w = 0) :
    0 ≤ 2 * ⟪v, A t v⟫ + 4 * ⟪v, deriv A t w⟫ + ⟪w, deriv (deriv A) t w⟫ := by
  let z : ℝ → H := fun τ ↦ w + (τ - t) • v
  have hz : ContDiffAt ℝ 2 z t := by dsimp [z]; fun_prop
  have hzt : z t = w := by simp only [z, sub_self, zero_smul, add_zero]
  have hd : deriv z = fun _ ↦ v := by
    funext τ
    simpa only [z, id_eq, one_smul] using ((((hasDerivAt_id τ).sub_const t).smul_const v).const_add w).deriv
  have hm : IsLocalMin (fun τ ↦ value (A τ) (z τ)) t := by
    filter_upwards [hp] with τ hτ
    change value (A t) (z t) ≤ value (A τ) (z τ)
    simpa only [value, hzt, hw, inner_zero_right] using hτ (z τ)
  have hc : ContinuousAt (fun τ ↦ value (A τ) (z τ)) t :=
    hz.continuousAt.inner (hA.continuousAt.clm_apply hz.continuousAt)
  have hn := second_derivative_nonneg_of_isLocalMin hm hc
  rw [deriv_deriv_value hA hz hs, hd] at hn
  simpa only [hzt, deriv_const, inner_zero_right, mul_zero, zero_add] using hn

end Mettapedia.Analysis.PositiveOperatorKernelCurvature
