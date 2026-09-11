import Mettapedia.Analysis.EuclideanCrossProduct
import Mettapedia.Analysis.RadialPower
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Signed exchange cancellation for cross-product kernels

Exchanging the two vector inputs of an even strain kernel turns the sum
of weighted stretching terms into one signed radial-power difference.
This identity retains the collinearity cancellation before estimating
absolute values. No kernel-size or dynamical bound is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open scoped RealInnerProductSpace Matrix
open MeasureTheory EuclideanCrossProduct RadialPower

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def weightedStretch (n : ℕ) (H : R3 →L[ℝ] R3) (a b : R3) : ℝ :=
  ‖a‖ ^ n * ⟪cross a b, H a⟫

def pairedStretch (n : ℕ) (H : R3 →L[ℝ] R3) (a b : R3) : ℝ :=
  ⟪cross a b, H (radialPower n a - radialPower n b)⟫

theorem weightedStretch_add_swap (n : ℕ) (H : R3 →L[ℝ] R3) (a b : R3) :
    weightedStretch n H a b + weightedStretch n H b a = pairedStretch n H a b := by
  simp only [weightedStretch, pairedStretch, radialPower, map_sub, map_smul,
    cross_swap a b, inner_neg_left, inner_sub_right, real_inner_smul_right]
  ring

theorem pairedStretch_swap (n : ℕ) (H : R3 →L[ℝ] R3) (a b : R3) :
    pairedStretch n H b a = pairedStretch n H a b := by
  rw [← weightedStretch_add_swap, ← weightedStretch_add_swap]
  exact add_comm _ _

theorem pairedStretch_collinear (n : ℕ) (H : R3 →L[ℝ] R3) (a : R3) (r s : ℝ) :
    pairedStretch n H (r • a) (s • a) = 0 := by
  simp only [pairedStretch, cross_smul_left, cross_smul_right, cross_self, smul_zero, inner_zero_left]

/-- Isotropic action is orthogonal to the cross product at both endpoints. -/
theorem pairedStretch_scalar_identity (n : ℕ) (a b : R3) (c : ℝ) :
    pairedStretch n (c • ContinuousLinearMap.id ℝ R3) a b = 0 := by
  have ha : ⟪cross a b, a⟫ = 0 :=
    (real_inner_comm (cross a b) a).symm.trans (inner_self_cross a b)
  have hb : ⟪cross a b, b⟫ = 0 :=
    (real_inner_comm (cross a b) b).symm.trans (inner_cross_self a b)
  simp only [pairedStretch, smul_apply, ContinuousLinearMap.id_apply, radialPower,
    inner_sub_right, real_inner_smul_right, ha, hb]
  ring

theorem pairedStretch_add_scalar_identity (n : ℕ) (H : R3 →L[ℝ] R3)
    (a b : R3) (c : ℝ) :
    pairedStretch n (H + c • ContinuousLinearMap.id ℝ R3) a b = pairedStretch n H a b := by
  have h := pairedStretch_scalar_identity n a b c
  change ⟪cross a b, (H + c • ContinuousLinearMap.id ℝ R3)
    (radialPower n a - radialPower n b)⟫ = _
  rw [add_apply, inner_add_right]
  change pairedStretch n H a b + pairedStretch n (c • ContinuousLinearMap.id ℝ R3) a b = _
  rw [h, add_zero]

theorem abs_pairedStretch_le (n : ℕ) (H : R3 →L[ℝ] R3) (a b : R3) :
    |pairedStretch n H a b| ≤
      ‖cross a b‖ * ‖H‖ * ‖radialPower n a - radialPower n b‖ := by
  calc
    _ ≤ ‖cross a b‖ * ‖H (radialPower n a - radialPower n b)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖cross a b‖ * (‖H‖ * ‖radialPower n a - radialPower n b‖) :=
      mul_le_mul_of_nonneg_left (H.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

theorem continuous_cross : Continuous (fun p : R3 × R3 ↦ cross p.1 p.2) := by
  unfold cross
  simp only [cross_apply]
  fun_prop

section Integration

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [SecondCountableTopology X]
  (μ : Measure X) [IsFiniteMeasure μ]
  (H : X → X → R3 →L[ℝ] R3) (w : X → R3)
  (hH : Continuous H.uncurry) (hw : Continuous w)

include hH hw

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [SecondCountableTopology X] in
theorem continuous_weightedStretch (n : ℕ) :
    Continuous (fun p : X × X ↦ weightedStretch n (H p.1 p.2) (w p.1) (w p.2)) := by
  have ha : Continuous (fun p : X × X ↦ w p.1) := hw.comp continuous_fst
  have hb : Continuous (fun p : X × X ↦ w p.2) := hw.comp continuous_snd
  exact (ha.norm.pow n).mul ((continuous_cross.comp (ha.prodMk hb)).inner (hH.clm_apply ha))

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [SecondCountableTopology X] in
theorem continuous_pairedStretch (n : ℕ) :
    Continuous (fun p : X × X ↦ pairedStretch n (H p.1 p.2) (w p.1) (w p.2)) := by
  have ha : Continuous (fun p : X × X ↦ w p.1) := hw.comp continuous_fst
  have hb : Continuous (fun p : X × X ↦ w p.2) := hw.comp continuous_snd
  exact (continuous_cross.comp (ha.prodMk hb)).inner
    (hH.clm_apply (((continuous_radialPower n).comp ha).sub ((continuous_radialPower n).comp hb)))

theorem integral_weightedStretch_eq_half_pair (n : ℕ) (hs : ∀ x y, H y x = H x y) :
    (∫ x, ∫ y, weightedStretch n (H x y) (w x) (w y) ∂μ ∂μ) =
      (1 / 2 : ℝ) * ∫ x, ∫ y, pairedStretch n (H x y) (w x) (w y) ∂μ ∂μ := by
  have hi : Integrable (fun p : X × X ↦ weightedStretch n (H p.1 p.2) (w p.1) (w p.2)) (μ.prod μ) :=
    (continuous_weightedStretch H w hH hw n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj := hi.swap
  change Integrable (fun p : X × X ↦ weightedStretch n (H p.2 p.1) (w p.2) (w p.1)) (μ.prod μ) at hj
  have hp : Integrable (fun p : X × X ↦ pairedStretch n (H p.1 p.2) (w p.1) (w p.2)) (μ.prod μ) :=
    (continuous_pairedStretch H w hH hw n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (∫ p : X × X, pairedStretch n (H p.1 p.2) (w p.1) (w p.2) ∂μ.prod μ) =
      (∫ p : X × X, weightedStretch n (H p.1 p.2) (w p.1) (w p.2) ∂μ.prod μ) +
      (∫ p : X × X, weightedStretch n (H p.2 p.1) (w p.2) (w p.1) ∂μ.prod μ) := by
    rw [← integral_add hi hj]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [hs p.1 p.2, weightedStretch_add_swap]
  have hswap := integral_prod_swap (μ := μ) (ν := μ)
    (fun p : X × X ↦ weightedStretch n (H p.1 p.2) (w p.1) (w p.2))
  simp only [Prod.fst_swap, Prod.snd_swap] at hswap
  rw [hswap] at he
  rw [integral_prod _ hi, integral_prod _ hp] at he
  linarith only [he]

end Integration

end Mettapedia.Analysis.SignedCrossKernel
