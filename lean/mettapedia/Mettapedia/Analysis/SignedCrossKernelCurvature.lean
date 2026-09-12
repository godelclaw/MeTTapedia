import Mettapedia.Analysis.RadialPowerCurvature
import Mettapedia.Analysis.SignedCrossKernelRateDecomposition
import Mettapedia.Analysis.SignedCrossKernelRegularity

/-!
# Common-translation curvature of the signed radial pairing

The kernel is fixed along a simultaneous endpoint translation. The second
derivative splits into a linear endpoint-acceleration term and a signed
quadratic first-derivative term. No positive curvature is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open RadialPower EuclideanCrossProduct
open scoped RealInnerProductSpace ContDiff
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def pairedCurvature (n : ℕ) (H : Op) (a b v w : R3) : ℝ :=
  2 * ⟪cross v w, H (radialPower (2 * (n + 2)) a - radialPower (2 * (n + 2)) b)⟫ +
    2 * ⟪cross v b + cross a w, H (evenRadialRate (n + 1) a v - evenRadialRate (n + 1) b w)⟫ +
    ⟪cross a b, H (evenRadialCurvature n a v - evenRadialCurvature n b w)⟫

theorem pairedCurvature_self (n : ℕ) (H : Op) (a v : R3) :
    pairedCurvature n H a a v v = 0 := by
  simp [pairedCurvature]

theorem pairedCurvature_collinear (n : ℕ) (H : Op) (e : R3) (a b v w : ℝ) :
    pairedCurvature n H (a • e) (b • e) (v • e) (w • e) = 0 := by
  simp [pairedCurvature, cross_smul_left, cross_smul_right]

theorem continuous_pairedEndpointRate {X : Type*} [TopologicalSpace X]
    (n : ℕ) {H : X → Op} {a b v w : X → R3}
    (hH : Continuous H) (ha : Continuous a) (hb : Continuous b)
    (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ pairedEndpointRate n (H x) (a x) (b x) (v x) (w x)) := by
  have hc {f g : X → R3} (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun x ↦ cross (f x) (g x)) :=
    contDiff_cross.continuous.comp (hf.prodMk hg)
  exact ((hc hv hb).add (hc ha hw)).inner
    (hH.clm_apply (((continuous_radialPower _).comp ha).sub ((continuous_radialPower _).comp hb))) |>.add
      ((hc ha hb).inner (hH.clm_apply
        ((continuous_evenRadialRate n ha hv).sub (continuous_evenRadialRate n hb hw))))

theorem continuous_pairedCurvature {X : Type*} [TopologicalSpace X]
    (n : ℕ) {H : X → Op} {a b v w : X → R3}
    (hH : Continuous H) (ha : Continuous a) (hb : Continuous b)
    (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ pairedCurvature n (H x) (a x) (b x) (v x) (w x)) := by
  have hc {f g : X → R3} (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun x ↦ cross (f x) (g x)) :=
    contDiff_cross.continuous.comp (hf.prodMk hg)
  have h₁ := ((hc hv hw).inner
    (hH.clm_apply (((continuous_radialPower (2 * (n + 2))).comp ha).sub
      ((continuous_radialPower (2 * (n + 2))).comp hb)))).const_mul (2 : ℝ)
  have h₂ := (((hc hv hb).add (hc ha hw)).inner (hH.clm_apply
    ((continuous_evenRadialRate (n + 1) ha hv).sub
      (continuous_evenRadialRate (n + 1) hb hw)))).const_mul (2 : ℝ)
  have h₃ := (hc ha hb).inner (𝕜 := ℝ) (hH.clm_apply
    ((continuous_evenRadialCurvature n ha hv).sub (continuous_evenRadialCurvature n hb hw)))
  exact (h₁.add h₂).add h₃

theorem hasDerivAt_pairedStretch_constKernel (n : ℕ) (H : Op)
    {a b : ℝ → R3} {v w : R3} {t : ℝ} (ha : HasDerivAt a v t) (hb : HasDerivAt b w t) :
    HasDerivAt (fun τ ↦ pairedStretch (2 * (n + 1)) H (a τ) (b τ))
      (pairedEndpointRate n H (a t) (b t) v w) t := by
  have h := (hasDerivAt_cross ha hb).inner ℝ
    (H.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_radialPower_even n ha).sub (hasDerivAt_radialPower_even n hb)))
  apply h.congr_deriv
  simp only [pairedEndpointRate, Function.comp_def, Pi.sub_apply, add_comm]

theorem hasDerivAt_pairedEndpointRate (n : ℕ) (H : Op)
    {a b v w : ℝ → R3} {z q : R3} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hb : HasDerivAt b (w t) t)
    (hv : HasDerivAt v z t) (hw : HasDerivAt w q t) :
    HasDerivAt (fun τ ↦ pairedEndpointRate (n + 1) H (a τ) (b τ) (v τ) (w τ))
      (pairedEndpointRate (n + 1) H (a t) (b t) z q + pairedCurvature n H (a t) (b t) (v t) (w t)) t := by
  have hc := (hasDerivAt_cross hv hb).add (hasDerivAt_cross ha hw)
  have hr := (hasDerivAt_radialPower_even (n + 1) ha).sub (hasDerivAt_radialPower_even (n + 1) hb)
  have hrr := (hasDerivAt_evenRadialRate n ha hv).sub (hasDerivAt_evenRadialRate n hb hw)
  have h := (hc.inner ℝ (H.hasFDerivAt.comp_hasDerivAt t hr)).add
    ((hasDerivAt_cross ha hb).inner ℝ (H.hasFDerivAt.comp_hasDerivAt t hrr))
  apply h.congr_deriv
  simp only [Function.comp_def, Pi.add_apply, Pi.sub_apply,
    pairedEndpointRate, pairedCurvature, inner_add_left, inner_add_right,
    inner_sub_right, map_add, map_sub, show n + 1 + 1 = n + 2 by omega]
  ring

theorem pairedEndpointRate_sum {ι : Type*} (J : Finset ι) (n : ℕ) (H : Op) (a b : R3)
    (f g : ι → R3) :
    pairedEndpointRate n H a b (∑ j ∈ J, f j) (∑ j ∈ J, g j) =
      ∑ j ∈ J, pairedEndpointRate n H a b (f j) (g j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [pairedEndpointRate, evenRadialRate]
  | @insert j J hj ih =>
    simp only [Finset.sum_insert hj]
    rw [← ih]
    simp only [pairedEndpointRate, evenRadialRate, cross_add_left, cross_add_right,
      inner_add_right, smul_add, add_smul, mul_add, map_add, map_sub,
      inner_add_left, inner_sub_right]
    ring

end Mettapedia.Analysis.SignedCrossKernel
