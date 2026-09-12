import Mettapedia.Analysis.HighAmplitudeWeightChainRule

/-! Threshold, tie, and endpoint-exchange checks for the cutoff rate. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.Analysis SignedCrossKernel
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

example (L : ℝ) (a b : R3) : highAmplitudeWeightRate L a b 0 0 = 0 := by
  simp [highAmplitudeWeightRate]

example (L : ℝ) (a b v w : R3) (h : min ‖a‖ ‖b‖ = L) :
    highAmplitudeWeightRate L a b v w = 0 := by
  simp only [highAmplitudeWeightRate, h, lt_self_iff_false, ↓reduceIte]

-- A branch-selected algebraic rate need not be symmetric away from the
-- differentiable-contact hypotheses. This does not describe an NS solution.
example (a : R3) (ha : ‖a‖ = 1) :
    highAmplitudeWeightRate (1 / 2) a a a 0 = 1 / 2 ∧
      highAmplitudeWeightRate (1 / 2) a a 0 a = 0 := by
  simp [highAmplitudeWeightRate, ha]
  norm_num

example {a b : ℝ → R3} {t L : ℝ} (hL : 0 < L)
    (hmin : min ‖a t‖ ‖b t‖ = L)
    (hd : DifferentiableAt ℝ (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ)) t) :
    deriv (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ)) t = 0 :=
  (hasDerivAt_highAmplitudeWeight_of_min_le hL hmin.le hd).deriv

#print axioms Mettapedia.Analysis.DerivativeContact.eq_of_eventually_le_of_eq
#print axioms Mettapedia.Analysis.SignedCrossKernel.hasDerivAt_highAmplitudeWeight_of_left_le
#print axioms Mettapedia.Analysis.SignedCrossKernel.hasDerivAt_highAmplitudeWeight_of_min_le
#print axioms Mettapedia.Analysis.SignedCrossKernel.hasDerivAt_highAmplitudeWeight_of_differentiable
#print axioms Mettapedia.Analysis.SignedCrossKernel.ae_hasDerivAt_highAmplitudeWeight
#print axioms Mettapedia.Analysis.SignedCrossKernel.highAmplitudeWeightRate_swap_of_differentiable
#print axioms Mettapedia.Analysis.SignedCrossKernel.endpointWeightRates_eq_of_tie
