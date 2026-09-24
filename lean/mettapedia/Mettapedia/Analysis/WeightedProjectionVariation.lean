import Mettapedia.Analysis.WeightedProjectionParabolic

/-!
# First variation of the weighted regularized projection

The derivative of the minimizing projection coefficient cancels in the
first variation. Both input responses remain explicit and linear; no sign
or size estimate for an evolution source is imposed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedProjectionVariation

open scoped RealInnerProductSpace
open RegularizedProjection RegularizedProjectionParabolic WeightedProjectionParabolic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def firstGradient (δ : ℝ) (a b : E) : E :=
  (6 * ‖a‖ ^ 4 * energy δ a b) • a -
    (2 * ‖a‖ ^ 6 * coefficient δ a b) • residual δ a b

def secondGradient (δ : ℝ) (a b : E) : E :=
  (2 * ‖a‖ ^ 6) • residual δ a b

theorem weightedRate_eq (δ : ℝ) (a b v z : E) :
    weightedRate δ a b v z =
      ⟪firstGradient δ a b, v⟫ + ⟪secondGradient δ a b, z⟫ := by
  simp only [weightedRate, energyRate, firstGradient, secondGradient, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  ring

theorem weightedRate_add (δ : ℝ) (a b v z f g : E) :
    weightedRate δ a b (v + f) (z + g) =
      weightedRate δ a b v z + weightedRate δ a b f g := by
  simp only [weightedRate_eq, inner_add_right]
  ring

theorem weightedRate_smul (δ : ℝ) (a b v z : E) (c : ℝ) :
    weightedRate δ a b (c • v) (c • z) = c * weightedRate δ a b v z := by
  simp only [weightedRate_eq, real_inner_smul_right]
  ring

def secondGradientRate (δ : ℝ) (a b v z : E) : E :=
  (12 * ‖a‖ ^ 4 * ⟪a, v⟫) • residual δ a b +
    (2 * ‖a‖ ^ 6) • (z - coefficientRate δ a b v z • a - coefficient δ a b • v)

theorem hasDerivAt_secondGradient (δ : ℝ) (hδ : 0 < δ)
    {a b : ℝ → E} {v z : E} {t : ℝ} (ha : HasDerivAt a v t) (hb : HasDerivAt b z t) :
    HasDerivAt (fun τ ↦ secondGradient δ (a τ) (b τ))
      (secondGradientRate δ (a t) (b t) v z) t := by
  have hc := RegularizedProjectionParabolic.hasDerivAt_coefficient δ hδ ha hb
  have hr := hb.fun_sub (hc.smul ha)
  have h := ((ha.norm_sq.fun_pow 3).const_mul 2).smul hr
  simp only [← pow_mul, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat] at h
  apply h.congr_deriv
  simp only [secondGradientRate, RegularizedProjection.residual, Pi.smul_apply']
  module

variable {X : Type*} [TopologicalSpace X]

theorem continuous_firstGradient (δ : ℝ) (hδ : 0 < δ) {a b : X → E}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x ↦ firstGradient δ (a x) (b x)) := by
  unfold firstGradient energy RegularizedProjection.residual coefficient
  fun_prop (disch := intro x; positivity)

theorem continuous_secondGradient (δ : ℝ) (hδ : 0 < δ) {a b : X → E}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x ↦ secondGradient δ (a x) (b x)) := by
  unfold secondGradient RegularizedProjection.residual coefficient
  fun_prop (disch := intro x; positivity)

theorem continuous_secondGradientRate (δ : ℝ) (hδ : 0 < δ) {a b v z : X → E}
    (ha : Continuous a) (hb : Continuous b) (hv : Continuous v) (hz : Continuous z) :
    Continuous (fun x ↦ secondGradientRate δ (a x) (b x) (v x) (z x)) := by
  unfold secondGradientRate coefficientRate RegularizedProjection.residual coefficient
  fun_prop (disch := intro x; positivity)

end Mettapedia.Analysis.WeightedProjectionVariation
