import Mettapedia.Analysis.SignedCrossKernelRateDecomposition
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! # Signed moving-kernel rates and convergent operator series

The kernel derivative and both endpoint rates are kept signed. Convergent
operator and derivative series transfer through their continuous linear
pairings. No absolute-value estimate or strain hypothesis is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open EuclideanCrossProduct RadialPower
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def pairedMaterialRate (n : ℕ) (H Hdot : Op) (a b da db : R3) : ℝ :=
  pairedStretch (2 * (n + 1)) Hdot a b + pairedEndpointRate n H a b da db

theorem pairedMaterialRate_self (n : ℕ) (H Hdot : Op) (a da db : R3) :
    pairedMaterialRate n H Hdot a a da db = 0 := by
  simp [pairedMaterialRate, pairedStretch, pairedEndpointRate]

theorem hasDerivAt_pairedStretch_movingKernel (n : ℕ) {a b : ℝ → R3} {H : ℝ → Op}
    {da db : R3} {Hdot : Op} {t : ℝ} (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hH : HasDerivAt H Hdot t) :
    HasDerivAt (fun τ ↦ pairedStretch (2 * (n + 1)) (H τ) (a τ) (b τ))
      (pairedMaterialRate n (H t) Hdot (a t) (b t) da db) t := by
  have hc := hasDerivAt_cross ha hb
  have hr := (hasDerivAt_radialPower_even n ha).sub (hasDerivAt_radialPower_even n hb)
  apply (hc.inner ℝ (hH.clm_apply hr)).congr_deriv
  simp only [pairedMaterialRate, pairedStretch, pairedEndpointRate, Pi.sub_apply, inner_add_right]
  ring

theorem hasSum_pairedMaterialRate {ι : Type*} (n : ℕ) {H Hdot : ι → Op} {K Kdot : Op}
    (hH : HasSum H K) (hHdot : HasSum Hdot Kdot) (a b da db : R3) :
    HasSum (fun i ↦ pairedMaterialRate n (H i) (Hdot i) a b da db)
      (pairedMaterialRate n K Kdot a b da db) := by
  let F := radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b
  let dF := evenRadialRate n a da - evenRadialRate n b db
  have hk := (innerSL ℝ (cross a b)).hasSum ((ContinuousLinearMap.apply ℝ R3 F).hasSum hHdot)
  have he := (innerSL ℝ (cross da b + cross a db)).hasSum
    ((ContinuousLinearMap.apply ℝ R3 F).hasSum hH)
  have hr := (innerSL ℝ (cross a b)).hasSum ((ContinuousLinearMap.apply ℝ R3 dF).hasSum hH)
  exact hk.add (he.add hr)

end Mettapedia.Analysis.SignedCrossKernel
