import Mettapedia.Analysis.HighAmplitudeWeightRegularity
import Mettapedia.Analysis.EuclideanCrossProductCalculus
import Mettapedia.Analysis.RadialPowerRegularity
import Mettapedia.Analysis.LocallyLipschitz

/-! # Smooth signed pairing and absolutely continuous cutoff paths -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open scoped ContDiff
open RadialPower EuclideanCrossProduct
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem contDiff_pairedStretch_even (n : ℕ) :
    ContDiff ℝ ∞ (fun p : (R3 →L[ℝ] R3) × (R3 × R3) ↦
      pairedStretch (2 * n) p.1 p.2.1 p.2.2) := by
  unfold pairedStretch
  apply ContDiff.inner
  · exact contDiff_cross.comp (contDiff_snd : ContDiff ℝ ∞
      (fun p : (R3 →L[ℝ] R3) × (R3 × R3) ↦ p.2))
  · exact contDiff_fst.clm_apply
      (((contDiff_radialPower_even n).comp (contDiff_fst.comp contDiff_snd)).sub
        ((contDiff_radialPower_even n).comp (contDiff_snd.comp contDiff_snd)))

theorem locallyLipschitz_pairedStretch_even {X : Type*} [PseudoMetricSpace X]
    (n : ℕ) {H : X → R3 →L[ℝ] R3} {u v : X → R3}
    (hH : LocallyLipschitz H) (hu : LocallyLipschitz u) (hv : LocallyLipschitz v) :
    LocallyLipschitz (fun t ↦ pairedStretch (2 * n) (H t) (u t) (v t)) := by
  have hF : LocallyLipschitz (fun p : (R3 →L[ℝ] R3) × (R3 × R3) ↦
      pairedStretch (2 * n) p.1 p.2.1 p.2.2) :=
    ((contDiff_pairedStretch_even n).of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).locallyLipschitz
  exact hF.comp (g := fun t ↦ (H t, (u t, v t))) (hH.prodMk (hu.prodMk hv))

theorem locallyLipschitz_highAmplitudeStretch_even {X : Type*} [PseudoMetricSpace X]
    (n : ℕ) {L : ℝ} (hL : 0 < L) {H : X → R3 →L[ℝ] R3} {u v : X → R3}
    (hH : LocallyLipschitz H) (hu : LocallyLipschitz u) (hv : LocallyLipschitz v) :
    LocallyLipschitz (fun t ↦ highAmplitudeStretch (2 * n) L (H t) (u t) (v t)) := by
  have hw : LocallyLipschitz (fun t ↦ 1 - lowAmplitudeWeight L (u t) (v t)) :=
    (lipschitzWith_highAmplitudeWeight L hL).locallyLipschitz.comp
      (g := fun t ↦ (u t, v t)) (hu.prodMk hv)
  exact hw.mul_algebra (locallyLipschitz_pairedStretch_even n hH hu hv)

theorem absolutelyContinuousOnInterval_highAmplitudeStretch_even (n : ℕ)
    {H : ℝ → R3 →L[ℝ] R3} {u v : ℝ → R3} {a b L : ℝ} (hL : 0 < L)
    (hH : LocallyLipschitz H) (hu : LocallyLipschitz u) (hv : LocallyLipschitz v) :
    AbsolutelyContinuousOnInterval
      (fun t ↦ highAmplitudeStretch (2 * n) L (H t) (u t) (v t)) a b := by
  exact absolutelyContinuousOnInterval_highAmplitudeProduct hL
    (AbsolutelyContinuousComposition.of_locallyLipschitz hu)
    (AbsolutelyContinuousComposition.of_locallyLipschitz hv)
    (AbsolutelyContinuousComposition.of_locallyLipschitz
      (locallyLipschitz_pairedStretch_even n hH hu hv))

end Mettapedia.Analysis.SignedCrossKernel
