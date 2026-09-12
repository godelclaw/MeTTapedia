import Mettapedia.Analysis.SmoothAmplitudeCutoff
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Exact first and second variations of the smooth amplitude weight -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SmoothAmplitudeCutoff

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def retainedRate (L : ℝ) (a v : E) : ℝ :=
  2 * L ^ 2 * ⟪a, v⟫ / (L ^ 2 + ‖a‖ ^ 2) ^ 2

def retainedCurvature (L : ℝ) (a v : E) : ℝ :=
  2 * L ^ 2 * ‖v‖ ^ 2 / (L ^ 2 + ‖a‖ ^ 2) ^ 2 -
    8 * L ^ 2 * ⟪a, v⟫ ^ 2 / (L ^ 2 + ‖a‖ ^ 2) ^ 3

theorem hasDerivAt_retainedWeight (L : ℝ) (hL : 0 < L) {a : ℝ → E} {v : E} {t : ℝ}
    (ha : HasDerivAt a v t) :
    HasDerivAt (fun τ ↦ retainedWeight L (a τ)) (retainedRate L (a t) v) t := by
  have h := ha.norm_sq.div (ha.norm_sq.const_add (L ^ 2)) (denominator_pos L hL (a t)).ne'
  apply h.congr_deriv
  simp only [retainedRate]
  ring

theorem hasDerivAt_retainedRate (L : ℝ) (hL : 0 < L) {a v : ℝ → E} {z : E} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hv : HasDerivAt v z t) :
    HasDerivAt (fun τ ↦ retainedRate L (a τ) (v τ))
      (retainedRate L (a t) z + retainedCurvature L (a t) (v t)) t := by
  have h := ((ha.inner ℝ hv).const_mul (2 * L ^ 2)).div
    (HasDerivAt.pow (HasDerivAt.const_add (L ^ 2) ha.norm_sq) 2)
    (pow_ne_zero _ (denominator_pos L hL (a t)).ne')
  apply h.congr_deriv
  simp only [retainedRate, retainedCurvature, real_inner_self_eq_norm_sq, Pi.pow_apply]
  field_simp [(denominator_pos L hL (a t)).ne']
  ring

end Mettapedia.Analysis.SmoothAmplitudeCutoff
