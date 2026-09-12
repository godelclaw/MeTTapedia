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

def radialCost (n : ℕ) (H : R3 →L[ℝ] R3) (a b : R3) : ℝ :=
  min ‖a‖ ‖b‖ * ‖H‖ * ‖radialPower n a - radialPower n b‖ ^ 2

def lowAmplitudeWeight (L : ℝ) (a b : R3) : ℝ := L / max L (min ‖a‖ ‖b‖)

def highAmplitudeStretch (n : ℕ) (L : ℝ) (H : R3 →L[ℝ] R3) (a b : R3) : ℝ :=
  (1 - lowAmplitudeWeight L a b) * pairedStretch n H a b

theorem lowAmplitudeWeight_nonneg (L : ℝ) (hL : 0 < L) (a b : R3) :
    0 ≤ lowAmplitudeWeight L a b := div_nonneg hL.le (hL.le.trans (le_max_left _ _))

theorem lowAmplitudeWeight_le_one (L : ℝ) (hL : 0 < L) (a b : R3) :
    lowAmplitudeWeight L a b ≤ 1 := by
  apply (div_le_one (hL.trans_le (le_max_left _ _))).mpr
  exact le_max_left _ _

theorem lowAmplitudeWeight_mul_min_le (L : ℝ) (hL : 0 < L) (a b : R3) :
    lowAmplitudeWeight L a b * min ‖a‖ ‖b‖ ≤ L := by
  have hd : 0 < max L (min ‖a‖ ‖b‖) := hL.trans_le (le_max_left _ _)
  calc
    _ ≤ lowAmplitudeWeight L a b * max L (min ‖a‖ ‖b‖) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (lowAmplitudeWeight_nonneg L hL a b)
    _ = L := div_mul_cancel₀ L hd.ne'

theorem continuous_lowAmplitudeWeight (L : ℝ) (hL : 0 < L) :
    Continuous (fun p : R3 × R3 ↦ lowAmplitudeWeight L p.1 p.2) :=
  continuous_const.div (continuous_const.max (continuous_fst.norm.min continuous_snd.norm))
    (fun _ ↦ (hL.trans_le (le_max_left _ _)).ne')

theorem highAmplitudeStretch_eq_zero_of_min_le (n : ℕ) (L : ℝ) (hL : 0 < L)
    (H : R3 →L[ℝ] R3) (a b : R3) (h : min ‖a‖ ‖b‖ ≤ L) :
    highAmplitudeStretch n L H a b = 0 := by
  simp only [highAmplitudeStretch, lowAmplitudeWeight, max_eq_left h,
    div_self hL.ne', sub_self, zero_mul]

theorem pairedStretch_sub_highAmplitudeStretch (n : ℕ) (L : ℝ)
    (H : R3 →L[ℝ] R3) (a b : R3) :
    pairedStretch n H a b - highAmplitudeStretch n L H a b =
      lowAmplitudeWeight L a b * pairedStretch n H a b := by
  unfold highAmplitudeStretch
  ring

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

theorem norm_cross_le_min_norm_mul_sub (a b : R3) :
    ‖cross a b‖ ≤ min ‖a‖ ‖b‖ * ‖a - b‖ := by
  have hleft : cross a (b - a) = cross a b := by simp [cross]
  have hright : cross (a - b) b = cross a b := by simp [cross]
  rcases le_total ‖a‖ ‖b‖ with hab | hab
  · simpa only [hleft, min_eq_left hab, norm_sub_rev] using norm_cross_le a (b - a)
  · simpa only [hright, min_eq_right hab, mul_comm] using norm_cross_le (a - b) b

/-- The remaining amplitude is the smaller endpoint norm, not a supremum.
At radial weight six, the square on the right is the cubic radial increment. -/
theorem abs_pairedStretch_double_le (n : ℕ) (H : R3 →L[ℝ] R3) (a b : R3) :
    |pairedStretch (2 * n) H a b| ≤
      4 * min ‖a‖ ‖b‖ * ‖H‖ * ‖radialPower n a - radialPower n b‖ ^ 2 := by
  calc
    _ ≤ ‖cross a b‖ * ‖H‖ * ‖radialPower (2 * n) a - radialPower (2 * n) b‖ :=
      abs_pairedStretch_le _ H a b
    _ ≤ (min ‖a‖ ‖b‖ * ‖a - b‖) * ‖H‖ *
        (2 * max ‖a‖ ‖b‖ ^ n * ‖radialPower n a - radialPower n b‖) := by
      gcongr
      · exact norm_cross_le_min_norm_mul_sub a b
      · exact norm_radialPower_double_sub_le n a b
    _ = (2 * min ‖a‖ ‖b‖ * ‖H‖ * ‖radialPower n a - radialPower n b‖) *
        (max ‖a‖ ‖b‖ ^ n * ‖a - b‖) := by ring
    _ ≤ (2 * min ‖a‖ ‖b‖ * ‖H‖ * ‖radialPower n a - radialPower n b‖) *
        (2 * ‖radialPower n a - radialPower n b‖) :=
      mul_le_mul_of_nonneg_left (max_norm_pow_mul_norm_sub_le n a b) (by positivity)
    _ = _ := by ring

theorem abs_lowAmplitudeWeight_mul_pairedStretch_double_le (n : ℕ) (L : ℝ) (hL : 0 < L)
    (H : R3 →L[ℝ] R3) (a b : R3) :
    |lowAmplitudeWeight L a b * pairedStretch (2 * n) H a b| ≤
      4 * L * ‖H‖ * ‖radialPower n a - radialPower n b‖ ^ 2 := by
  rw [abs_mul, abs_of_nonneg (lowAmplitudeWeight_nonneg L hL a b)]
  calc
    _ ≤ lowAmplitudeWeight L a b *
        (4 * min ‖a‖ ‖b‖ * ‖H‖ * ‖radialPower n a - radialPower n b‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (abs_pairedStretch_double_le n H a b)
        (lowAmplitudeWeight_nonneg L hL a b)
    _ = (lowAmplitudeWeight L a b * min ‖a‖ ‖b‖) *
        (4 * ‖H‖ * ‖radialPower n a - radialPower n b‖ ^ 2) := by ring
    _ ≤ L * (4 * ‖H‖ * ‖radialPower n a - radialPower n b‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (lowAmplitudeWeight_mul_min_le L hL a b) (by positivity)
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

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [SecondCountableTopology X] in
theorem continuous_radialCost (n : ℕ) :
    Continuous (fun p : X × X ↦ radialCost n (H p.1 p.2) (w p.1) (w p.2)) := by
  have ha : Continuous (fun p : X × X ↦ w p.1) := hw.comp continuous_fst
  have hb : Continuous (fun p : X × X ↦ w p.2) := hw.comp continuous_snd
  exact ((ha.norm.min hb.norm).mul hH.norm).mul
    ((((continuous_radialPower n).comp ha).sub ((continuous_radialPower n).comp hb)).norm.pow 2)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [SecondCountableTopology X] in
theorem continuous_highAmplitudeStretch (n : ℕ) (L : ℝ) (hL : 0 < L) :
    Continuous (fun p : X × X ↦ highAmplitudeStretch n L (H p.1 p.2) (w p.1) (w p.2)) :=
  (continuous_const.sub ((continuous_lowAmplitudeWeight L hL).comp
    ((hw.comp continuous_fst).prodMk (hw.comp continuous_snd)))).mul
      (continuous_pairedStretch H w hH hw n)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [SecondCountableTopology X] in
theorem continuous_bareRadialCost (n : ℕ) :
    Continuous (fun p : X × X ↦ ‖H p.1 p.2‖ *
      ‖radialPower n (w p.1) - radialPower n (w p.2)‖ ^ 2) :=
  hH.norm.mul ((((continuous_radialPower n).comp (hw.comp continuous_fst)).sub
    ((continuous_radialPower n).comp (hw.comp continuous_snd))).norm.pow 2)

/-- Only the bounded-amplitude part is estimated; the high-amplitude term stays signed. -/
theorem abs_integral_paired_sub_high_le (n : ℕ) (L : ℝ) (hL : 0 < L) :
    |(∫ x, ∫ y, pairedStretch (2 * n) (H x y) (w x) (w y) ∂μ ∂μ) -
      (∫ x, ∫ y, highAmplitudeStretch (2 * n) L (H x y) (w x) (w y) ∂μ ∂μ)| ≤
      4 * L * ∫ x, ∫ y, ‖H x y‖ * ‖radialPower n (w x) - radialPower n (w y)‖ ^ 2 ∂μ ∂μ := by
  have hp := (continuous_pairedStretch H w hH hw (2 * n)).integrable_of_hasCompactSupport
    (μ := μ.prod μ) (HasCompactSupport.of_compactSpace _)
  have hh := (continuous_highAmplitudeStretch H w hH hw (2 * n) L hL).integrable_of_hasCompactSupport
    (μ := μ.prod μ) (HasCompactSupport.of_compactSpace _)
  have hb := (continuous_bareRadialCost H w hH hw n).integrable_of_hasCompactSupport
    (μ := μ.prod μ) (HasCompactSupport.of_compactSpace _)
  rw [← integral_prod _ hp, ← integral_prod _ hh, ← integral_prod _ hb, ← integral_sub hp hh]
  apply abs_integral_le_integral_abs.trans
  rw [← integral_const_mul]
  apply integral_mono (hp.sub hh).abs (hb.const_mul (4 * L))
  intro p
  change |pairedStretch (2 * n) (H p.1 p.2) (w p.1) (w p.2) -
    highAmplitudeStretch (2 * n) L (H p.1 p.2) (w p.1) (w p.2)| ≤ _
  rw [pairedStretch_sub_highAmplitudeStretch]
  simpa only [mul_assoc] using
    abs_lowAmplitudeWeight_mul_pairedStretch_double_le n L hL (H p.1 p.2) (w p.1) (w p.2)

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

/-- Exchange precedes the absolute-value estimate, retaining the smaller endpoint amplitude. -/
theorem abs_integral_weightedStretch_double_le (n : ℕ) (hs : ∀ x y, H y x = H x y) :
    |∫ x, ∫ y, weightedStretch (2 * n) (H x y) (w x) (w y) ∂μ ∂μ| ≤
      2 * ∫ x, ∫ y, radialCost n (H x y) (w x) (w y) ∂μ ∂μ := by
  have hp : Integrable (fun p : X × X ↦ pairedStretch (2 * n) (H p.1 p.2) (w p.1) (w p.2))
      (μ.prod μ) := (continuous_pairedStretch H w hH hw _).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hc : Integrable (fun p : X × X ↦ radialCost n (H p.1 p.2) (w p.1) (w p.2))
      (μ.prod μ) := (continuous_radialCost H w hH hw n).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [integral_weightedStretch_eq_half_pair μ H w hH hw _ hs,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← integral_prod _ hp, ← integral_prod _ hc]
  have hbound : (∫ p : X × X, |pairedStretch (2 * n) (H p.1 p.2) (w p.1) (w p.2)| ∂μ.prod μ) ≤
      4 * ∫ p : X × X, radialCost n (H p.1 p.2) (w p.1) (w p.2) ∂μ.prod μ := by
    rw [← integral_const_mul]
    apply integral_mono hp.abs (hc.const_mul 4)
    intro p
    simpa only [radialCost, mul_assoc] using abs_pairedStretch_double_le n (H p.1 p.2) (w p.1) (w p.2)
  have ha := abs_integral_le_integral_abs (μ := μ.prod μ)
    (f := fun p : X × X ↦ pairedStretch (2 * n) (H p.1 p.2) (w p.1) (w p.2))
  linarith only [ha, hbound]

end Integration

end Mettapedia.Analysis.SignedCrossKernel
