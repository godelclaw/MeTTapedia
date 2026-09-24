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

def pairRate (L : ℝ) (a b v w : E) : ℝ :=
  retainedRate L a v * retainedWeight L b + retainedWeight L a * retainedRate L b w

def pairCurvature (L : ℝ) (a b v w : E) : ℝ :=
  retainedCurvature L a v * retainedWeight L b +
    2 * retainedRate L a v * retainedRate L b w + retainedWeight L a * retainedCurvature L b w

theorem hasDerivAt_pairWeight (L : ℝ) (hL : 0 < L) {a b : ℝ → E} {v w : E} {t : ℝ}
    (ha : HasDerivAt a v t) (hb : HasDerivAt b w t) :
    HasDerivAt (fun τ ↦ pairWeight L (a τ) (b τ)) (pairRate L (a t) (b t) v w) t :=
  (hasDerivAt_retainedWeight L hL ha).mul (hasDerivAt_retainedWeight L hL hb)

theorem hasDerivAt_pairRate (L : ℝ) (hL : 0 < L) {a b v w : ℝ → E} {z q : E} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hb : HasDerivAt b (w t) t)
    (hv : HasDerivAt v z t) (hw : HasDerivAt w q t) :
    HasDerivAt (fun τ ↦ pairRate L (a τ) (b τ) (v τ) (w τ))
      (pairRate L (a t) (b t) z q + pairCurvature L (a t) (b t) (v t) (w t)) t := by
  have h := ((hasDerivAt_retainedRate L hL ha hv).mul (hasDerivAt_retainedWeight L hL hb)).add
    ((hasDerivAt_retainedWeight L hL ha).mul (hasDerivAt_retainedRate L hL hb hw))
  apply h.congr_deriv
  simp only [pairRate, pairCurvature]
  ring

theorem continuous_retainedRate {X : Type*} [TopologicalSpace X]
    (L : ℝ) (hL : 0 < L) {a v : X → E} (ha : Continuous a) (hv : Continuous v) :
    Continuous (fun x ↦ retainedRate L (a x) (v x)) :=
  ((ha.inner hv).const_mul (2 * L ^ 2)).div ((continuous_const.add (ha.norm.pow 2)).pow 2)
    (fun x ↦ pow_ne_zero _ (denominator_pos L hL (a x)).ne')

theorem continuous_retainedCurvature {X : Type*} [TopologicalSpace X]
    (L : ℝ) (hL : 0 < L) {a v : X → E} (ha : Continuous a) (hv : Continuous v) :
    Continuous (fun x ↦ retainedCurvature L (a x) (v x)) :=
  (((hv.norm.pow 2).const_mul (2 * L ^ 2)).div ((continuous_const.add (ha.norm.pow 2)).pow 2)
    (fun x ↦ pow_ne_zero _ (denominator_pos L hL (a x)).ne')).sub
    ((((ha.inner hv).pow 2).const_mul (8 * L ^ 2)).div
      ((continuous_const.add (ha.norm.pow 2)).pow 3)
      (fun x ↦ pow_ne_zero _ (denominator_pos L hL (a x)).ne'))

theorem continuous_pairRate {X : Type*} [TopologicalSpace X]
    (L : ℝ) (hL : 0 < L) {a b v w : X → E}
    (ha : Continuous a) (hb : Continuous b) (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ pairRate L (a x) (b x) (v x) (w x)) :=
  ((continuous_retainedRate L hL ha hv).mul ((contDiff_retainedWeight L hL).continuous.comp hb)).add
    (((contDiff_retainedWeight L hL).continuous.comp ha).mul (continuous_retainedRate L hL hb hw))

theorem continuous_pairCurvature {X : Type*} [TopologicalSpace X]
    (L : ℝ) (hL : 0 < L) {a b v w : X → E}
    (ha : Continuous a) (hb : Continuous b) (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ pairCurvature L (a x) (b x) (v x) (w x)) :=
  (((continuous_retainedCurvature L hL ha hv).mul
    ((contDiff_retainedWeight L hL).continuous.comp hb)).add
    (((continuous_retainedRate L hL ha hv).const_mul 2).mul (continuous_retainedRate L hL hb hw))).add
    (((contDiff_retainedWeight L hL).continuous.comp ha).mul (continuous_retainedCurvature L hL hb hw))

theorem pairRate_sum {ι : Type*} (J : Finset ι) (L : ℝ) (a b : E) (v w : ι → E) :
    pairRate L a b (∑ j ∈ J, v j) (∑ j ∈ J, w j) = ∑ j ∈ J, pairRate L a b (v j) (w j) := by
  simp only [pairRate, retainedRate, inner_sum, Finset.mul_sum, Finset.sum_div,
    Finset.sum_mul, Finset.sum_add_distrib]

theorem pairRate_add (L : ℝ) (a b v w f g : E) :
    pairRate L a b (v + f) (w + g) = pairRate L a b v w + pairRate L a b f g := by
  simp only [pairRate, retainedRate, inner_add_right]
  ring

theorem pairRate_smul (L c : ℝ) (a b v w : E) :
    pairRate L a b (c • v) (c • w) = c * pairRate L a b v w := by
  simp only [pairRate, retainedRate, real_inner_smul_right]
  ring

end Mettapedia.Analysis.SmoothAmplitudeCutoff
