import Mettapedia.Analysis.SignedCrossKernel
import Mettapedia.Analysis.SignedCrossKernelFreezing
import Mettapedia.Analysis.UnitTorusPairIntegration

/-!
# Signed cross-increment cancellation and its variable-background remainder

An even mean-zero operator kernel annihilating a vector field cancels the
integrated cross-increment form at constant background. At variable background
the exact remainder contains a background increment. No absolute-value bound,
positivity assertion, or Navier–Stokes regularity hypothesis is built in.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SolenoidalCrossIncrement

open MeasureTheory EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

private theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E]
    {f : T3 → E} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_kernel_increment_eq_zero (K : T3 → Op) (hK : Continuous K)
    (hmean : (∫ h : T3, K h) = 0) (g : T3 → R3) (hg : Continuous g)
    (hconv : ∀ x, (∫ h : T3, K h (g (x - h))) = 0) (x : T3) :
    (∫ y : T3, K (x - y) (g x - g y)) = 0 := by
  have hc : Continuous (fun h : T3 ↦ K h (g (x - h))) :=
    hK.clm_apply (hg.comp (continuous_const.sub continuous_id))
  calc
    _ = ∫ h : T3, K h (g x - g (x - h)) := by
      simpa only [sub_sub_cancel] using
        (integral_sub_left_eq_self (fun y : T3 ↦ K (x - y) (g x - g y)) volume x).symm
    _ = (∫ h : T3, K h) (g x) - ∫ h : T3, K h (g (x - h)) := by
      simp only [map_sub]
      rw [integral_sub (integrable_of_continuous (hK.clm_apply continuous_const))
        (integrable_of_continuous hc), ContinuousLinearMap.integral_apply
          (integrable_of_continuous hK)]
    _ = 0 := by rw [hmean, hconv]; simp

theorem integral_inner_cross_increment_eq_zero (K : T3 → Op) (hK : Continuous K)
    (hmean : (∫ h : T3, K h) = 0) (g : T3 → R3) (hg : Continuous g)
    (hconv : ∀ x, (∫ h : T3, K h (g (x - h))) = 0) (x : T3) (q : R3) :
    (∫ y : T3, ⟪cross (g x) q, K (x - y) (g x - g y)⟫) = 0 := by
  have hc : Continuous (fun y : T3 ↦ K (x - y) (g x - g y)) :=
    (hK.comp (continuous_const.sub continuous_id)).clm_apply (continuous_const.sub hg)
  have h := (innerSL ℝ (cross (g x) q)).integral_comp_comm (integrable_of_continuous hc)
  simpa only [innerSL_apply_apply, integral_kernel_increment_eq_zero K hK hmean g hg hconv x,
    inner_zero_right] using h

set_option maxHeartbeats 600000 in
theorem integral_cross_increment_eq_background_increment
    (K : T3 → Op) (hK : Continuous K) (heven : ∀ h, K (-h) = K h)
    (hmean : (∫ h : T3, K h) = 0) (g q : T3 → R3) (hg : Continuous g) (hq : Continuous q)
    (hconv : ∀ x, (∫ h : T3, K h (g (x - h))) = 0) :
    (∫ x : T3, ∫ y : T3, ⟪cross (g x - g y) (q x), K (x - y) (g x - g y)⟫) =
      ∫ x : T3, ∫ y : T3, ⟪cross (g x) (q y - q x), K (x - y) (g x - g y)⟫ := by
  let A (x y : T3) := ⟪cross (g x) (q x), K (x - y) (g x - g y)⟫
  let B (x y : T3) := ⟪cross (g y) (q x), K (x - y) (g x - g y)⟫
  let C (x y : T3) := ⟪cross (g x) (q y), K (x - y) (g x - g y)⟫
  have hKg : Continuous (fun p : T3 × T3 ↦ K (p.1 - p.2) (g p.1 - g p.2)) :=
    (hK.comp (continuous_fst.sub continuous_snd)).clm_apply
      ((hg.comp continuous_fst).sub (hg.comp continuous_snd))
  have hA : Continuous A.uncurry :=
    (SignedCrossKernel.continuous_cross.comp
      ((hg.comp continuous_fst).prodMk (hq.comp continuous_fst))).inner hKg
  have hB : Continuous B.uncurry :=
    (SignedCrossKernel.continuous_cross.comp
      ((hg.comp continuous_snd).prodMk (hq.comp continuous_fst))).inner hKg
  have hC : Continuous C.uncurry :=
    (SignedCrossKernel.continuous_cross.comp
      ((hg.comp continuous_fst).prodMk (hq.comp continuous_snd))).inner hKg
  have hAz (x : T3) : (∫ y : T3, A x y) = 0 :=
    integral_inner_cross_increment_eq_zero K hK hmean g hg hconv x (q x)
  have hAi (x : T3) : Integrable (A x) :=
    integrable_of_continuous (hA.comp (continuous_const.prodMk continuous_id))
  have hBi (x : T3) : Integrable (B x) :=
    integrable_of_continuous (hB.comp (continuous_const.prodMk continuous_id))
  have hCi (x : T3) : Integrable (C x) :=
    integrable_of_continuous (hC.comp (continuous_const.prodMk continuous_id))
  have hswap (x y : T3) : B y x = -C x y := by
    dsimp [B, C]
    rw [show y - x = -(x - y) by abel, heven,
      show g y - g x = -(g x - g y) by abel, map_neg, inner_neg_right]
  have hBC : (∫ x : T3, ∫ y : T3, B x y) = -(∫ x : T3, ∫ y : T3, C x y) := by
    rw [integral_integral_swap
      (hB.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    simp_rw [hswap, integral_neg]
  calc
    _ = -(∫ x : T3, ∫ y : T3, B x y) := by
      simp only [cross_sub_left, inner_sub_left]
      change (∫ x : T3, ∫ y : T3, A x y - B x y) = _
      have hi (x : T3) : (∫ y : T3, A x y - B x y) = -(∫ y : T3, B x y) := by
        rw [integral_sub (hAi x) (hBi x), hAz, zero_sub]
      simp_rw [hi, integral_neg]
    _ = ∫ x : T3, ∫ y : T3, C x y := by rw [hBC, neg_neg]
    _ = _ := by
      simp only [cross_sub_right, inner_sub_left]
      change _ = ∫ x : T3, ∫ y : T3, C x y - A x y
      apply integral_congr_ae
      filter_upwards [] with x
      rw [integral_sub (hCi x) (hAi x), hAz, sub_zero]

theorem integral_cross_increment_constant_eq_zero
    (K : T3 → Op) (hK : Continuous K) (heven : ∀ h, K (-h) = K h)
    (hmean : (∫ h : T3, K h) = 0) (g : T3 → R3) (hg : Continuous g)
    (hconv : ∀ x, (∫ h : T3, K h (g (x - h))) = 0) (q : R3) :
    (∫ x : T3, ∫ y : T3, ⟪cross (g x - g y) q, K (x - y) (g x - g y)⟫) = 0 := by
  simpa only [sub_self, cross_zero, inner_zero_left, integral_zero] using
    integral_cross_increment_eq_background_increment K hK heven hmean g (fun _ ↦ q)
      hg continuous_const hconv

set_option maxHeartbeats 600000 in
/-- The full curvature, after solenoidal cancellation, retains background,
amplitude, and endpoint-mismatch channels. -/
theorem integral_pairedCurvature_eq_channels
    (n : ℕ) (K : T3 → Op) (hK : Continuous K) (heven : ∀ h, K (-h) = K h)
    (hmean : (∫ h : T3, K h) = 0) (a g : T3 → R3) (ha : Continuous a) (hg : Continuous g)
    (hconv : ∀ x, (∫ h : T3, K h (g (x - h))) = 0) :
    (∫ x : T3, ∫ y : T3, SignedCrossKernel.pairedCurvature n (K (x - y))
      (a x) (a y) (g x) (g y)) =
      2 * (∫ x : T3, ∫ y : T3,
        ⟪cross (g x) (RadialPower.radialPower (2 * (n + 2)) (a y) -
          RadialPower.radialPower (2 * (n + 2)) (a x)), K (x - y) (g x - g y)⟫) +
      (∫ x : T3, ∫ y : T3, SignedCrossKernel.amplitudeCurvature n (K (x - y))
        (a x) (g x) (g y)) +
      (∫ x : T3, ∫ y : T3, SignedCrossKernel.endpointCurvatureRemainder n (K (x - y))
        (a x) (a y) (g x) (g y)) := by
  let q (x : T3) := RadialPower.radialPower (2 * (n + 2)) (a x)
  have hq : Continuous q := (RadialPower.continuous_radialPower _).comp ha
  let f (p : T3 × T3) := ⟪cross (g p.1 - g p.2) (q p.1),
    K (p.1 - p.2) (g p.1 - g p.2)⟫
  let m (p : T3 × T3) := SignedCrossKernel.amplitudeCurvature n (K (p.1 - p.2))
    (a p.1) (g p.1) (g p.2)
  let r (p : T3 × T3) := SignedCrossKernel.endpointCurvatureRemainder n (K (p.1 - p.2))
    (a p.1) (a p.2) (g p.1) (g p.2)
  have hf : Continuous f :=
    (SignedCrossKernel.continuous_cross.comp
      (((hg.comp continuous_fst).sub (hg.comp continuous_snd)).prodMk
        (hq.comp continuous_fst))).inner
      ((hK.comp (continuous_fst.sub continuous_snd)).clm_apply
        ((hg.comp continuous_fst).sub (hg.comp continuous_snd)))
  have hm : Continuous m := SignedCrossKernel.continuous_amplitudeCurvature n
    (hK.comp (continuous_fst.sub continuous_snd)) (ha.comp continuous_fst)
    (hg.comp continuous_fst) (hg.comp continuous_snd)
  have hr : Continuous r := SignedCrossKernel.continuous_endpointCurvatureRemainder n
    (hK.comp (continuous_fst.sub continuous_snd)) (ha.comp continuous_fst)
    (ha.comp continuous_snd) (hg.comp continuous_fst) (hg.comp continuous_snd)
  have hfi := hf.integrable_of_hasCompactSupport (μ := (volume : Measure T3).prod volume)
    (HasCompactSupport.of_compactSpace _)
  have hmi := hm.integrable_of_hasCompactSupport (μ := (volume : Measure T3).prod volume)
    (HasCompactSupport.of_compactSpace _)
  have hri := hr.integrable_of_hasCompactSupport (μ := (volume : Measure T3).prod volume)
    (HasCompactSupport.of_compactSpace _)
  have he (x y : T3) : SignedCrossKernel.pairedCurvature n (K (x - y)) (a x) (a y) (g x) (g y) =
      2 * f (x, y) + m (x, y) + r (x, y) := by
    rw [SignedCrossKernel.pairedCurvature_eq_frozen_add_remainder,
      SignedCrossKernel.pairedCurvature_same_value_eq_channels]
  simp_rw [he]
  rw [integral_integral_add (f := fun p ↦ 2 * f p + m p) ((hfi.const_mul 2).add hmi) hri,
    integral_integral_add (hfi.const_mul 2) hmi]
  simp only [f, integral_const_mul]
  rw [integral_cross_increment_eq_background_increment K hK heven hmean g q hg hq hconv]

end Mettapedia.Analysis.SolenoidalCrossIncrement
