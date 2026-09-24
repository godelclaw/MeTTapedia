import Mettapedia.Analysis.SignedCrossKernelCurvature

/-!
# Increment and isotropic cancellations in paired-source curvature

Endpoint coincidence does not imply gradient coincidence. The exact
diagonal formula retains the gradient increment. Isotropic kernel action
vanishes for arbitrary endpoint values and gradients.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open RadialPower EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

theorem pairedCurvature_eq_increments (n : ℕ) (H : Op) (a b v w : R3) :
    pairedCurvature n H a b v w =
      2 * ⟪cross (v - w) w, H (radialPower (2 * (n + 2)) a - radialPower (2 * (n + 2)) b)⟫ +
      2 * ⟪cross (v - w) b + cross (a - b) w,
        H (evenRadialRate (n + 1) a v - evenRadialRate (n + 1) b w)⟫ +
      ⟪cross (a - b) b, H (evenRadialCurvature n a v - evenRadialCurvature n b w)⟫ := by
  have h₁ : cross (v - w) w = cross v w := by simp [cross]
  have h₂ : cross (v - w) b + cross (a - b) w = cross v b + cross a w := by
    have hs (p q r : R3) : cross (p - q) r = cross p r - cross q r := by simp [cross]
    rw [hs, hs, cross_swap b w]
    module
  have h₃ : cross (a - b) b = cross a b := by simp [cross]
  rw [h₁, h₂, h₃]
  rfl

theorem pairedCurvature_same_value (n : ℕ) (H : Op) (a v w : R3) :
    pairedCurvature n H a a v w =
      2 * ⟪cross (v - w) a, H (evenRadialRate (n + 1) a (v - w))⟫ := by
  rw [pairedCurvature_eq_increments]
  have hr : evenRadialRate (n + 1) a v - evenRadialRate (n + 1) a w =
      evenRadialRate (n + 1) a (v - w) := by
    simp only [evenRadialRate, inner_sub_right, smul_sub, mul_sub, sub_smul]
    module
  rw [hr]
  simp

theorem pairedEndpointRate_scalar_identity (n : ℕ) (a b v w : R3) (c : ℝ) :
    pairedEndpointRate n (c • ContinuousLinearMap.id ℝ R3) a b v w = 0 := by
  have ha : HasDerivAt (fun t : ℝ ↦ a + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add a
  have hb : HasDerivAt (fun t : ℝ ↦ b + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add b
  have hd := hasDerivAt_pairedStretch_constKernel n (c • ContinuousLinearMap.id ℝ R3) ha hb
  simp only [zero_smul, add_zero, pairedStretch_scalar_identity] at hd
  exact hd.unique (hasDerivAt_const 0 (0 : ℝ))

theorem abs_pairedCurvature_same_value_le (n : ℕ) (H : Op) (a v w : R3) :
    |pairedCurvature n H a a v w| ≤
      2 * (2 * (n + 2) + 1 : ℝ) * ‖a‖ ^ (2 * (n + 2)) *
        ‖cross (v - w) a‖ * ‖H‖ * ‖v - w‖ := by
  rw [pairedCurvature_same_value, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * (‖cross (v - w) a‖ * ‖H (evenRadialRate (n + 1) a (v - w))‖) := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ ≤ 2 * (‖cross (v - w) a‖ *
        (‖H‖ * ((2 * (n + 2) + 1 : ℝ) * ‖a‖ ^ (2 * (n + 2)) * ‖v - w‖))) := by
      gcongr
      exact (H.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (by simpa only [show n + 1 + 1 = n + 2 by omega, Nat.cast_add, Nat.cast_one,
            show (n : ℝ) + 1 + 1 = n + 2 by ring]
          using (norm_evenRadialRate_le (n + 1) a (v - w))) (norm_nonneg H))
    _ = _ := by ring

theorem pairedCurvature_scalar_identity (n : ℕ) (a b v w : R3) (c : ℝ) :
    pairedCurvature n (c • ContinuousLinearMap.id ℝ R3) a b v w = 0 := by
  have ha : HasDerivAt (fun t : ℝ ↦ a + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add a
  have hb : HasDerivAt (fun t : ℝ ↦ b + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add b
  have hd := hasDerivAt_pairedEndpointRate n (c • ContinuousLinearMap.id ℝ R3)
    ha hb (hasDerivAt_const 0 v) (hasDerivAt_const 0 w)
  simp only [zero_smul, add_zero, pairedEndpointRate_scalar_identity, zero_add] at hd
  exact hd.unique (hasDerivAt_const 0 (0 : ℝ))

theorem pairedCurvature_add_scalar_identity (n : ℕ) (H : Op) (a b v w : R3) (c : ℝ) :
    pairedCurvature n (H + c • ContinuousLinearMap.id ℝ R3) a b v w =
      pairedCurvature n H a b v w := by
  have he : pairedCurvature n (H + c • ContinuousLinearMap.id ℝ R3) a b v w =
      pairedCurvature n H a b v w +
        pairedCurvature n (c • ContinuousLinearMap.id ℝ R3) a b v w := by
    simp only [pairedCurvature, add_apply, inner_add_right]
    ring
  rw [he, pairedCurvature_scalar_identity, add_zero]

theorem pairedCurvature_neg_all (n : ℕ) (H : Op) (a b v w : R3) :
    pairedCurvature n H (-a) (-b) (-v) (-w) = -pairedCurvature n H a b v w := by
  have hr (p q : R3) : evenRadialRate (n + 1) (-p) (-q) = -evenRadialRate (n + 1) p q := by
    simp only [evenRadialRate, norm_neg, inner_neg_neg, smul_neg]
    module
  have hc (p q : R3) : evenRadialCurvature n (-p) (-q) = -evenRadialCurvature n p q := by
    simp only [evenRadialCurvature, norm_neg, inner_neg_neg, smul_neg]
    module
  have hx (p q : R3) : cross (-p) (-q) = cross p q := by simp [cross]
  simp only [pairedCurvature, hx, hr, hc, radialPower, norm_neg, smul_neg,
    map_sub, map_neg, inner_sub_right, inner_neg_right]
  ring

end Mettapedia.Analysis.SignedCrossKernel
