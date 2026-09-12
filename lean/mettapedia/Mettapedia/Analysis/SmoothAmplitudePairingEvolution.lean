import Mettapedia.Analysis.SmoothAmplitudePairing
import Mettapedia.Analysis.SmoothAmplitudeCutoffEvolution
import Mettapedia.Analysis.SignedCrossKernelCurvatureIncrement

/-!
# Exact variations of the smooth retained pairing

The curvature retains all three product-rule terms: weighted pairing
curvature, the mixed first variations, and weight curvature times the
pairing. No term has an assumed sign. At equal endpoint values only the
weighted transverse gradient-increment curvature survives.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SmoothAmplitudePairing

open SmoothAmplitudeCutoff SignedCrossKernel RadialPower EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def retainedEndpointRate (n : ℕ) (L : ℝ) (H : Op) (a b v w : R3) : ℝ :=
  pairWeight L a b * pairedEndpointRate n H a b v w +
    pairRate L a b v w * pairedStretch (2 * (n + 1)) H a b

def retainedPairCurvature (n : ℕ) (L : ℝ) (H : Op) (a b v w : R3) : ℝ :=
  pairWeight L a b * pairedCurvature n H a b v w +
    2 * pairRate L a b v w * pairedEndpointRate (n + 1) H a b v w +
    pairCurvature L a b v w * pairedStretch (2 * (n + 2)) H a b

theorem hasDerivAt_retainedStretch_constKernel (n : ℕ) (L : ℝ) (hL : 0 < L) (H : Op)
    {a b : ℝ → R3} {v w : R3} {t : ℝ} (ha : HasDerivAt a v t) (hb : HasDerivAt b w t) :
    HasDerivAt (fun τ ↦ retainedStretch (2 * (n + 1)) L H (a τ) (b τ))
      (retainedEndpointRate n L H (a t) (b t) v w) t := by
  have h := (hasDerivAt_pairWeight L hL ha hb).mul (hasDerivAt_pairedStretch_constKernel n H ha hb)
  apply h.congr_deriv
  simp only [retainedEndpointRate, add_comm]

theorem hasDerivAt_retainedEndpointRate (n : ℕ) (L : ℝ) (hL : 0 < L) (H : Op)
    {a b v w : ℝ → R3} {z q : R3} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hb : HasDerivAt b (w t) t)
    (hv : HasDerivAt v z t) (hw : HasDerivAt w q t) :
    HasDerivAt (fun τ ↦ retainedEndpointRate (n + 1) L H (a τ) (b τ) (v τ) (w τ))
      (retainedEndpointRate (n + 1) L H (a t) (b t) z q +
        retainedPairCurvature n L H (a t) (b t) (v t) (w t)) t := by
  have h := ((hasDerivAt_pairWeight L hL ha hb).mul
    (hasDerivAt_pairedEndpointRate n H ha hb hv hw)).add
    ((hasDerivAt_pairRate L hL ha hb hv hw).mul
      (hasDerivAt_pairedStretch_constKernel (n + 1) H ha hb))
  apply h.congr_deriv
  simp only [retainedEndpointRate, retainedPairCurvature, show n + 1 + 1 = n + 2 by omega]
  ring

theorem continuous_retainedEndpointRate {X : Type*} [TopologicalSpace X]
    (n : ℕ) (L : ℝ) (hL : 0 < L) {H : X → Op} {a b v w : X → R3}
    (hH : Continuous H) (ha : Continuous a) (hb : Continuous b)
    (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ retainedEndpointRate n L (H x) (a x) (b x) (v x) (w x)) := by
  have hQ : Continuous (fun x ↦ pairedStretch (2 * (n + 1)) (H x) (a x) (b x)) :=
    (contDiff_pairedStretch_even (n + 1)).continuous.comp
      (f := fun x ↦ (H x, (a x, b x))) (hH.prodMk (ha.prodMk hb))
  exact (((contDiff_pairWeight L hL).continuous.comp (ha.prodMk hb)).mul
    (continuous_pairedEndpointRate n hH ha hb hv hw)).add
    ((continuous_pairRate L hL ha hb hv hw).mul hQ)

theorem continuous_retainedPairCurvature {X : Type*} [TopologicalSpace X]
    (n : ℕ) (L : ℝ) (hL : 0 < L) {H : X → Op} {a b v w : X → R3}
    (hH : Continuous H) (ha : Continuous a) (hb : Continuous b)
    (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ retainedPairCurvature n L (H x) (a x) (b x) (v x) (w x)) := by
  have hQ : Continuous (fun x ↦ pairedStretch (2 * (n + 2)) (H x) (a x) (b x)) :=
    (contDiff_pairedStretch_even (n + 2)).continuous.comp
      (f := fun x ↦ (H x, (a x, b x))) (hH.prodMk (ha.prodMk hb))
  exact ((((contDiff_pairWeight L hL).continuous.comp (ha.prodMk hb)).mul
    (continuous_pairedCurvature n hH ha hb hv hw)).add
    (((continuous_pairRate L hL ha hb hv hw).const_mul 2).mul
      (continuous_pairedEndpointRate (n + 1) hH ha hb hv hw))).add
    ((continuous_pairCurvature L hL ha hb hv hw).mul hQ)

theorem retainedEndpointRate_sum {ι : Type*} (J : Finset ι) (n : ℕ) (L : ℝ) (H : Op)
    (a b : R3) (v w : ι → R3) :
    retainedEndpointRate n L H a b (∑ j ∈ J, v j) (∑ j ∈ J, w j) =
      ∑ j ∈ J, retainedEndpointRate n L H a b (v j) (w j) := by
  simp only [retainedEndpointRate, pairedEndpointRate_sum, pairRate_sum,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]

theorem retainedPairCurvature_same_value (n : ℕ) (L : ℝ) (H : Op) (a v w : R3) :
    retainedPairCurvature n L H a a v w =
      pairWeight L a a * pairedCurvature n H a a v w := by
  simp [retainedPairCurvature, pairedEndpointRate, pairedStretch]

theorem retainedPairCurvature_same_value_eq_increment (n : ℕ) (L : ℝ) (H : Op) (a v w : R3) :
    retainedPairCurvature n L H a a v w =
      pairWeight L a a * (2 * ⟪cross (v - w) a, H (evenRadialRate (n + 1) a (v - w))⟫) := by
  rw [retainedPairCurvature_same_value, pairedCurvature_same_value]

theorem retainedPairCurvature_scalar_identity (n : ℕ) (L : ℝ) (a b v w : R3) (c : ℝ) :
    retainedPairCurvature n L (c • ContinuousLinearMap.id ℝ R3) a b v w = 0 := by
  simp [retainedPairCurvature, pairedCurvature_scalar_identity,
    pairedEndpointRate_scalar_identity, pairedStretch_scalar_identity]

end Mettapedia.Analysis.SmoothAmplitudePairing
