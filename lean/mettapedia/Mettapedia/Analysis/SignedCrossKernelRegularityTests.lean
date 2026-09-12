import Mettapedia.Analysis.SignedCrossKernelRegularity

/-! Cutoff regularity checks without excluding threshold or tie intervals. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.Analysis SignedCrossKernel
local notation "R3" => EuclideanSpace ℝ (Fin 3)

example {u : ℝ → R3} {a b L : ℝ} (hL : 0 < L)
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ 1 - lowAmplitudeWeight L (u t) (-u t)) a b :=
  absolutelyContinuousOnInterval_highAmplitudeWeight hL hu hu.neg

example (u : R3) (a b L : ℝ) (hL : 0 < L) :
    (∫ t in a..b, deriv (fun _ : ℝ ↦ 1 - lowAmplitudeWeight L u u) t) = 0 := by
  rw [integral_deriv_highAmplitudeWeight_eq_sub hL
    (AbsolutelyContinuousComposition.of_locallyLipschitz (LocallyLipschitz.const u))
    (AbsolutelyContinuousComposition.of_locallyLipschitz (LocallyLipschitz.const u))]
  exact sub_self _

example {u v : ℝ → R3} {H : ℝ → R3 →L[ℝ] R3} {a b L : ℝ}
    (hL : 0 < L) (hu : LocallyLipschitz u) (hv : LocallyLipschitz v)
    (hH : LocallyLipschitz H) :
    (∫ t in a..b, deriv (fun τ ↦ highAmplitudeStretch 6 L (H τ) (u τ) (v τ)) t) =
      highAmplitudeStretch 6 L (H b) (u b) (v b) - highAmplitudeStretch 6 L (H a) (u a) (v a) :=
  (absolutelyContinuousOnInterval_highAmplitudeStretch_even 3 hL hH hu hv).integral_deriv_eq_sub

#print axioms Mettapedia.Analysis.AbsolutelyContinuousComposition.comp_lipschitz
#print axioms Mettapedia.Analysis.AbsolutelyContinuousComposition.prodMk
#print axioms Mettapedia.Analysis.AbsolutelyContinuousComposition.of_locallyLipschitz
#print axioms Mettapedia.Analysis.AbsolutelyContinuousComposition.congr
#print axioms Mettapedia.Analysis.RadialPower.contDiff_radialPower_even
#print axioms Mettapedia.Analysis.SignedCrossKernel.lipschitzWith_one_sub_div_max
#print axioms Mettapedia.Analysis.SignedCrossKernel.lipschitzWith_highAmplitudeWeight
#print axioms Mettapedia.Analysis.SignedCrossKernel.absolutelyContinuousOnInterval_highAmplitudeWeight
#print axioms Mettapedia.Analysis.SignedCrossKernel.integral_deriv_highAmplitudeWeight_eq_sub
#print axioms Mettapedia.Analysis.SignedCrossKernel.absolutelyContinuousOnInterval_highAmplitudeProduct
#print axioms Mettapedia.Analysis.SignedCrossKernel.contDiff_pairedStretch_even
#print axioms Mettapedia.Analysis.SignedCrossKernel.locallyLipschitz_pairedStretch_even
#print axioms Mettapedia.Analysis.SignedCrossKernel.absolutelyContinuousOnInterval_highAmplitudeStretch_even
