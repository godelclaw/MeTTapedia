import Mettapedia.Analysis.WeightedCrossProductEvolution
import Mettapedia.Analysis.LocallyLipschitz

/-!
# Complete second variation of the weighted angular energy

The acceleration terms are linear and separate from the quadratic
first-variation terms. The latter include two mixed terms whose signs
must be retained in a diffusion identity. All formulas include zeros.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedCrossProduct

open EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem locallyLipschitz_energy {X : Type*} [PseudoMetricSpace X] (n : ℕ)
    {a b : X → R3} (ha : LocallyLipschitz a) (hb : LocallyLipschitz b) :
    LocallyLipschitz (fun x ↦ energy n (a x) (b x)) := by
  have h : ContDiff ℝ 1 (fun p : R3 × R3 ↦ energy n p.1 p.2) :=
    (contDiff_energy n).of_le (by norm_num)
  exact h.locallyLipschitz.comp (g := fun x ↦ (a x, b x)) (ha.prodMk hb)

def amplitudeCurvature (n : ℕ) (a b v w : R3) : ℝ :=
  (4 * (n + 2) * (n + 1) : ℝ) *
    (‖a‖ ^ (2 * n) * ⟪a, v⟫ ^ 2 + ‖b‖ ^ (2 * n) * ⟪b, w⟫ ^ 2) +
  (2 * (n + 2) : ℝ) *
    (‖a‖ ^ (2 * (n + 1)) * ‖v‖ ^ 2 + ‖b‖ ^ (2 * (n + 1)) * ‖w‖ ^ 2)

def curvature (n : ℕ) (a b v w : R3) : ℝ :=
  amplitudeCurvature n a b v w * ‖cross a b‖ ^ 2 +
    4 * amplitudeRate (n + 1) a b v w * ⟪cross a b, cross v b + cross a w⟫ +
    2 * amplitudeWeight (n + 1) a b * ‖cross v b + cross a w‖ ^ 2 +
    4 * amplitudeWeight (n + 1) a b * ⟪cross a b, cross v w⟫

theorem hasDerivAt_amplitudeRate (n : ℕ) {a b v w : ℝ → R3} {z q : R3} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hb : HasDerivAt b (w t) t)
    (hv : HasDerivAt v z t) (hw : HasDerivAt w q t) :
    HasDerivAt (fun τ ↦ amplitudeRate (n + 1) (a τ) (b τ) (v τ) (w τ))
      (amplitudeRate (n + 1) (a t) (b t) z q + amplitudeCurvature n (a t) (b t) (v t) (w t)) t := by
  have h := ((((ha.norm_sq).pow (n + 1)).mul (ha.inner ℝ hv)).add
    (((hb.norm_sq).pow (n + 1)).mul (hb.inner ℝ hw))).const_mul (2 * (n + 1 + 1) : ℝ)
  simp only [amplitudeRate, pow_mul, Nat.cast_add, Nat.cast_one]
  apply h.congr_deriv
  simp only [Pi.pow_apply, amplitudeCurvature, pow_mul, Nat.add_sub_cancel,
    real_inner_self_eq_norm_sq, Nat.cast_add, Nat.cast_one]
  ring

theorem hasDerivAt_rate (n : ℕ) {a b v w : ℝ → R3} {z q : R3} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hb : HasDerivAt b (w t) t)
    (hv : HasDerivAt v z t) (hw : HasDerivAt w q t) :
    HasDerivAt (fun τ ↦ rate (n + 1) (a τ) (b τ) (v τ) (w τ))
      (rate (n + 1) (a t) (b t) z q + curvature n (a t) (b t) (v t) (w t)) t := by
  have hc := hasDerivAt_cross ha hb
  have hcc := (hasDerivAt_cross hv hb).add (hasDerivAt_cross ha hw)
  have h := ((hasDerivAt_amplitudeRate n ha hb hv hw).mul hc.norm_sq).add
    (((hasDerivAt_amplitudeWeight (n + 1) ha hb).const_mul 2).mul (hc.inner ℝ hcc))
  apply h.congr_deriv
  simp only [Pi.add_apply, real_inner_self_eq_norm_sq]
  simp only [rate, curvature, inner_add_right]
  ring

theorem rate_sum {ι : Type*} (J : Finset ι) (n : ℕ) (a b : R3) (v w : ι → R3) :
    rate n a b (∑ j ∈ J, v j) (∑ j ∈ J, w j) = ∑ j ∈ J, rate n a b (v j) (w j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [rate, amplitudeRate]
  | @insert j J hj ih =>
    simp only [Finset.sum_insert hj]
    rw [← ih]
    simp only [rate, amplitudeRate, cross_add_left, cross_add_right, inner_add_right]
    ring

theorem continuous_amplitudeRate {X : Type*} [TopologicalSpace X] (n : ℕ)
    {a b v w : X → R3} (ha : Continuous a) (hb : Continuous b)
    (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ amplitudeRate n (a x) (b x) (v x) (w x)) :=
  (((ha.norm.pow _).mul (ha.inner hv)).add ((hb.norm.pow _).mul (hb.inner hw))).const_mul _

theorem continuous_rate {X : Type*} [TopologicalSpace X] (n : ℕ)
    {a b v w : X → R3} (ha : Continuous a) (hb : Continuous b)
    (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ rate n (a x) (b x) (v x) (w x)) := by
  have hc {f g : X → R3} (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun x ↦ cross (f x) (g x)) := contDiff_cross.continuous.comp (hf.prodMk hg)
  exact ((continuous_amplitudeRate n ha hb hv hw).mul ((hc ha hb).norm.pow 2)).add
    (((ha.norm.pow _).add (hb.norm.pow _)).const_mul 2 |>.mul
      ((hc ha hb).inner ((hc hv hb).add (hc ha hw))))

theorem continuous_curvature {X : Type*} [TopologicalSpace X] (n : ℕ)
    {a b v w : X → R3} (ha : Continuous a) (hb : Continuous b)
    (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ curvature n (a x) (b x) (v x) (w x)) := by
  have hc {f g : X → R3} (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun x ↦ cross (f x) (g x)) := contDiff_cross.continuous.comp (hf.prodMk hg)
  have hW : Continuous (fun x ↦ amplitudeWeight (n + 1) (a x) (b x)) :=
    (ha.norm.pow _).add (hb.norm.pow _)
  have hA : Continuous (fun x ↦ amplitudeCurvature n (a x) (b x) (v x) (w x)) :=
    ((((ha.norm.pow _).mul ((ha.inner hv).pow 2)).add
      ((hb.norm.pow _).mul ((hb.inner hw).pow 2))).const_mul _).add
      ((((ha.norm.pow _).mul (hv.norm.pow 2)).add
        ((hb.norm.pow _).mul (hw.norm.pow 2))).const_mul _)
  exact (((hA.mul ((hc ha hb).norm.pow 2)).add
    (((continuous_amplitudeRate (n + 1) ha hb hv hw).const_mul 4).mul
      ((hc ha hb).inner ((hc hv hb).add (hc ha hw))))).add
    ((hW.const_mul 2).mul (((hc hv hb).add (hc ha hw)).norm.pow 2))).add
    ((hW.const_mul 4).mul ((hc ha hb).inner (hc hv hw)))

end Mettapedia.Analysis.WeightedCrossProduct
