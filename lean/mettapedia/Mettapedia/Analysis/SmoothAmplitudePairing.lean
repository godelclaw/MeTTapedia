import Mettapedia.Analysis.SmoothAmplitudeCutoff
import Mettapedia.Analysis.SignedCrossKernelRegularity
import Mettapedia.Analysis.SignedCrossKernelIntegrable

/-!
# Smooth amplitude retention in the signed cross-kernel pairing

The retained source is smooth for every even radial exponent. Its
complement has the same radial-increment payment as the sharp-threshold
split, without assuming a sign for the pairing or the retained source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SmoothAmplitudePairing

open MeasureTheory SignedCrossKernel SmoothAmplitudeCutoff RadialPower EuclideanCrossProduct
open scoped ContDiff RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def retainedStretch (n : ℕ) (L : ℝ) (H : Op) (a b : R3) : ℝ :=
  pairWeight L a b * pairedStretch n H a b

theorem pairedStretch_sub_retainedStretch (n : ℕ) (L : ℝ) (H : Op) (a b : R3) :
    pairedStretch n H a b - retainedStretch n L H a b =
      complementWeight L a b * pairedStretch n H a b := by
  unfold retainedStretch complementWeight
  ring

theorem complementWeight_le_lowAmplitudeWeight (L : ℝ) (hL : 0 < L) (a b : R3) :
    complementWeight L a b ≤ lowAmplitudeWeight L a b := by
  by_cases hm : min ‖a‖ ‖b‖ ≤ L
  · simpa only [lowAmplitudeWeight, max_eq_left hm, div_self hL.ne'] using
      complementWeight_le_one L a b
  · have hLm : L ≤ min ‖a‖ ‖b‖ := (le_of_not_ge hm)
    rw [lowAmplitudeWeight, max_eq_right hLm]
    exact (le_div_iff₀ (hL.trans_le hLm)).mpr (complementWeight_mul_min_le L hL a b)

theorem abs_pairedStretch_sub_retainedStretch_le (n : ℕ) (L : ℝ) (hL : 0 < L)
    (H : Op) (a b : R3) :
    |pairedStretch (2 * n) H a b - retainedStretch (2 * n) L H a b| ≤
      4 * L * ‖H‖ * ‖radialPower n a - radialPower n b‖ ^ 2 := by
  rw [pairedStretch_sub_retainedStretch, abs_mul,
    abs_of_nonneg (complementWeight_nonneg L hL a b)]
  calc
    _ ≤ complementWeight L a b *
        (4 * min ‖a‖ ‖b‖ * ‖H‖ * ‖radialPower n a - radialPower n b‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (abs_pairedStretch_double_le n H a b)
        (complementWeight_nonneg L hL a b)
    _ = (complementWeight L a b * min ‖a‖ ‖b‖) *
        (4 * ‖H‖ * ‖radialPower n a - radialPower n b‖ ^ 2) := by ring
    _ ≤ L * (4 * ‖H‖ * ‖radialPower n a - radialPower n b‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (complementWeight_mul_min_le L hL a b) (by positivity)
    _ = _ := by ring

theorem retainedStretch_swap (n : ℕ) (L : ℝ) (H : Op) (a b : R3) :
    retainedStretch n L H b a = retainedStretch n L H a b := by
  rw [retainedStretch, pairWeight_swap, pairedStretch_swap]
  rfl

theorem contDiff_retainedStretch_even (n : ℕ) (L : ℝ) (hL : 0 < L) :
    ContDiff ℝ ∞ (fun p : Op × (R3 × R3) ↦ retainedStretch (2 * n) L p.1 p.2.1 p.2.2) :=
  ((contDiff_pairWeight L hL).comp contDiff_snd).mul (contDiff_pairedStretch_even n)

theorem contDiff_retainedStretch_comp_even {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (k n : ℕ) (L : ℝ) (hL : 0 < L)
    {K : X → Op} {a b : X → R3} (hK : ContDiff ℝ k K)
    (ha : ContDiff ℝ k a) (hb : ContDiff ℝ k b) :
    ContDiff ℝ k (fun x ↦ retainedStretch (2 * n) L (K x) (a x) (b x)) := by
  have hf : ContDiff ℝ k
      (fun p : Op × (R3 × R3) ↦ retainedStretch (2 * n) L p.1 p.2.1 p.2.2) :=
    (contDiff_retainedStretch_even n L hL).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
  exact hf.comp (f := fun x ↦ (K x, (a x, b x))) (hK.prodMk (ha.prodMk hb))

theorem locallyLipschitz_retainedStretch_even {X : Type*} [PseudoEMetricSpace X]
    (n : ℕ) (L : ℝ) (hL : 0 < L) {K : X → Op} {a b : X → R3}
    (hK : LocallyLipschitz K) (ha : LocallyLipschitz a) (hb : LocallyLipschitz b) :
    LocallyLipschitz (fun x ↦ retainedStretch (2 * n) L (K x) (a x) (b x)) := by
  have hf : LocallyLipschitz
      (fun p : Op × (R3 × R3) ↦ retainedStretch (2 * n) L p.1 p.2.1 p.2.2) :=
    ((contDiff_retainedStretch_even n L hL).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).locallyLipschitz
  exact hf.comp (g := fun x ↦ (K x, (a x, b x))) (hK.prodMk (ha.prodMk hb))

theorem continuous_retainedStretch {X : Type*} [TopologicalSpace X]
    (n : ℕ) (L : ℝ) (hL : 0 < L) {H : X → Op} {a b : X → R3}
    (hH : Continuous H) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x ↦ retainedStretch n L (H x) (a x) (b x)) :=
  ((contDiff_pairWeight L hL).continuous.comp (ha.prodMk hb)).mul
    ((continuous_cross.comp (ha.prodMk hb)).inner
      (hH.clm_apply (((continuous_radialPower n).comp ha).sub ((continuous_radialPower n).comp hb))))

theorem abs_integral_paired_sub_retained_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (H : X → X → Op) (w : X → R3)
    (n : ℕ) (L : ℝ) (hL : 0 < L)
    (hp : Integrable (fun p : X × X ↦ pairedStretch (2 * n) (H p.1 p.2)
      (w p.1) (w p.2)) (μ.prod μ))
    (hr : Integrable (fun p : X × X ↦ retainedStretch (2 * n) L (H p.1 p.2)
      (w p.1) (w p.2)) (μ.prod μ))
    (hb : Integrable (fun p : X × X ↦ ‖H p.1 p.2‖ *
      ‖radialPower n (w p.1) - radialPower n (w p.2)‖ ^ 2) (μ.prod μ)) :
    |(∫ x, ∫ y, pairedStretch (2 * n) (H x y) (w x) (w y) ∂μ ∂μ) -
      (∫ x, ∫ y, retainedStretch (2 * n) L (H x y) (w x) (w y) ∂μ ∂μ)| ≤
      4 * L * ∫ x, ∫ y, ‖H x y‖ * ‖radialPower n (w x) - radialPower n (w y)‖ ^ 2 ∂μ ∂μ := by
  rw [← integral_prod _ hp, ← integral_prod _ hr, ← integral_prod _ hb, ← integral_sub hp hr]
  apply abs_integral_le_integral_abs.trans
  rw [← integral_const_mul]
  apply integral_mono (hp.sub hr).abs (hb.const_mul (4 * L))
  intro p
  simpa only [mul_assoc, Pi.sub_apply] using
    abs_pairedStretch_sub_retainedStretch_le n L hL (H p.1 p.2) (w p.1) (w p.2)

end Mettapedia.Analysis.SmoothAmplitudePairing
