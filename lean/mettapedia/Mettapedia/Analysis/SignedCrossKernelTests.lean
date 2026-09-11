import Mettapedia.Analysis.SignedCrossKernel

/-! Regression checks for signed endpoint exchange and its exact null cases. -/

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace
open Mettapedia.Analysis.EuclideanCrossProduct Mettapedia.Analysis.RadialPower
open Mettapedia.Analysis.SignedCrossKernel

local notation "R3" => EuclideanSpace ℝ (Fin 3)

example (n : ℕ) (H : R3 →L[ℝ] R3) (a : R3) :
    pairedStretch n H a a = 0 ∧ pairedStretch n H a (-a) = 0 := by
  constructor
  · simpa using pairedStretch_collinear n H a 1 1
  · simpa using pairedStretch_collinear n H a 1 (-1)

example (n : ℕ) (H : R3 →L[ℝ] R3) (a : R3) :
    pairedStretch n H a 0 = 0 ∧ pairedStretch n H 0 a = 0 := by
  simp [pairedStretch]

example (n : ℕ) (H : R3 →L[ℝ] R3) (a b : R3) :
    weightedStretch n H a b + weightedStretch n H b a =
      ⟪cross a b, H (‖a‖ ^ n • a - ‖b‖ ^ n • b)⟫ :=
  weightedStretch_add_swap n H a b

example (n : ℕ) (H : R3 →L[ℝ] R3) (a b : R3) (c : ℝ) :
    pairedStretch n (H + c • ContinuousLinearMap.id ℝ R3) b a =
      pairedStretch n H a b := by
  rw [pairedStretch_add_scalar_identity, pairedStretch_swap]

example (n : ℕ) (a b : R3) :
    pairedStretch n (ContinuousLinearMap.id ℝ R3) a b = 0 := by
  simpa using pairedStretch_scalar_identity n a b 1

#print axioms Mettapedia.Analysis.SignedCrossKernel.weightedStretch_add_swap
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedStretch_swap
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedStretch_collinear
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedStretch_scalar_identity
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedStretch_add_scalar_identity
#print axioms Mettapedia.Analysis.SignedCrossKernel.abs_pairedStretch_le
#print axioms Mettapedia.Analysis.SignedCrossKernel.integral_weightedStretch_eq_half_pair
