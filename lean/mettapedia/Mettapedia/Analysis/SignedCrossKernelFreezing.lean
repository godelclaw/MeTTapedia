import Mettapedia.Analysis.SignedCrossKernelCurvatureIncrement

/-!
# Freezing the endpoint value in signed paired curvature

The frozen-value curvature has an isotropic derivative term and an amplitude
derivative term. The explicit freezing remainder vanishes at equal endpoint
values, even when their derivatives differ. No sign is assigned to a channel.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open RadialPower EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def amplitudeCurvature (n : ℕ) (H : Op) (a v w : R3) : ℝ :=
  2 * (2 * (n + 2) : ℝ) * ‖a‖ ^ (2 * (n + 1)) * ⟪a, v - w⟫ *
    ⟪cross (v - w) a, H a⟫

def endpointCurvatureRemainder (n : ℕ) (H : Op) (a b v w : R3) : ℝ :=
  2 * ⟪cross v w, H (radialPower (2 * (n + 2)) a - radialPower (2 * (n + 2)) b)⟫ +
    2 * ⟪cross v (b - a), H (evenRadialRate (n + 1) a (v - w))⟫ +
    2 * ⟪cross v b + cross a w,
      H (evenRadialRate (n + 1) a w - evenRadialRate (n + 1) b w)⟫ +
    ⟪cross a b, H (evenRadialCurvature n a v - evenRadialCurvature n b w)⟫

theorem pairedCurvature_same_value_eq_channels (n : ℕ) (H : Op) (a v w : R3) :
    pairedCurvature n H a a v w =
      2 * ⟪cross (v - w) (radialPower (2 * (n + 2)) a), H (v - w)⟫ +
        amplitudeCurvature n H a v w := by
  rw [pairedCurvature_same_value]
  simp only [evenRadialRate, radialPower, amplitudeCurvature, map_add, map_smul,
    inner_add_right, inner_smul_right, cross_smul_right, inner_smul_left, conj_trivial,
    show n + 1 + 1 = n + 2 by omega, Nat.cast_add, Nat.cast_one]
  ring

theorem pairedCurvature_eq_frozen_add_remainder (n : ℕ) (H : Op) (a b v w : R3) :
    pairedCurvature n H a b v w =
      pairedCurvature n H a a v w + endpointCurvatureRemainder n H a b v w := by
  have hr : evenRadialRate (n + 1) a (v - w) =
      evenRadialRate (n + 1) a v - evenRadialRate (n + 1) a w := by
    simp only [evenRadialRate, inner_sub_right, smul_sub, mul_sub, sub_smul]
    module
  rw [pairedCurvature_same_value, hr]
  simp only [pairedCurvature, endpointCurvatureRemainder, hr,
    cross_sub_left, cross_sub_right, map_sub, inner_sub_right, inner_sub_left, inner_add_left]
  rw [cross_swap a w]
  simp only [inner_neg_left]
  ring

theorem endpointCurvatureRemainder_same_value (n : ℕ) (H : Op) (a v w : R3) :
    endpointCurvatureRemainder n H a a v w = 0 := by
  simp [endpointCurvatureRemainder]

theorem continuous_amplitudeCurvature {X : Type*} [TopologicalSpace X]
    (n : ℕ) {H : X → Op} {a v w : X → R3}
    (hH : Continuous H) (ha : Continuous a) (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ amplitudeCurvature n (H x) (a x) (v x) (w x)) := by
  unfold amplitudeCurvature
  exact (((continuous_const.mul continuous_const).mul (ha.norm.pow _)).mul
    (ha.inner (hv.sub hw))).mul
      ((continuous_cross.comp ((hv.sub hw).prodMk ha)).inner (hH.clm_apply ha))

theorem continuous_endpointCurvatureRemainder {X : Type*} [TopologicalSpace X]
    (n : ℕ) {H : X → Op} {a b v w : X → R3}
    (hH : Continuous H) (ha : Continuous a) (hb : Continuous b)
    (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ endpointCurvatureRemainder n (H x) (a x) (b x) (v x) (w x)) := by
  have he (x : X) : endpointCurvatureRemainder n (H x) (a x) (b x) (v x) (w x) =
      pairedCurvature n (H x) (a x) (b x) (v x) (w x) -
        pairedCurvature n (H x) (a x) (a x) (v x) (w x) := by
    rw [pairedCurvature_eq_frozen_add_remainder]
    ring
  simp_rw [he]
  exact (continuous_pairedCurvature n hH ha hb hv hw).sub
    (continuous_pairedCurvature n hH ha ha hv hw)

end Mettapedia.Analysis.SignedCrossKernel
