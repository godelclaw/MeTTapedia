import Mettapedia.Computability.PNP.ExactZABCompressionObstructionSparseThreshold

/-!
# Exact ZAB compression obstruction: decision-list layers

This module contains the exact affine-decision-list and exact decision-list
target/recovery/ERM-family surface bounds.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n p r k : ℕ} {Index : Type*}

theorem ExactZABAffineDecisionListTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactZABAffineDecisionListTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ p * ((r + (k + k)) + 2) + 1 := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := p * ((r + (k + k)) + 2) + 1) (Index := Index)
      hsurj h.compressionTarget

theorem ExactZABAffineDecisionListTargetData.not_surjective_predict_of_budget_lt
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactZABAffineDecisionListTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hbudget : p * ((r + (k + k)) + 2) + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactZABAffineDecisionListRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineDecisionListRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ p * ((r + (k + k)) + 2) + 1 := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactZABAffineDecisionListRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineDecisionListRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : p * ((r + (k + k)) + 2) + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

theorem ExactZABDecisionListTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactZABDecisionListTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) zfeat G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r + 2 * k + 1 := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := r + 2 * k + 1) (Index := Index)
      hsurj h.compressionTarget_twoMul

theorem ExactZABDecisionListTargetData.not_surjective_predict_of_budget_lt
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactZABDecisionListTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) zfeat G)
    (hbudget : r + 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem exactZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
    (hr : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    r + 2 * k + 1 < 2 ^ (n + 2 * k) := by
  have hle : r + 2 * k + 1 ≤ n + 2 * k + 1 := by
    exact Nat.succ_le_succ (Nat.add_le_add_right hr (2 * k))
  exact lt_of_le_of_lt hle <|
    exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
      (r := n) (k := k) hwidth

theorem ExactZABDecisionListTargetData.not_surjective_predict_of_le_of_two_le
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactZABDecisionListTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) zfeat G)
    (hr : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact
    h.not_surjective_predict_of_budget_lt
      (exactZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
        (n := n) (r := r) (k := k) hr hwidth)

theorem ExactZABDecisionListRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r + 2 * k + 1 := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactZABDecisionListRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : r + 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

theorem ExactZABDecisionListRecoveryData.not_surjective_predict_of_le_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hr : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_le_of_two_le hr hwidth

theorem exactZABDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict) :
    2 ^ (n + 2 * k) ≤ r + 2 * k + 1 := by
  let hdata :=
    exactZABDecisionListERMTargetData
      (Z := BitVec n) (r := r) (k := k) (Index := Index) zfeat samples
  exact hdata.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem exactZABDecisionListERMFamily_not_surjective_of_budget_lt
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hbudget : r + 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    exactZABDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (r := r) (k := k) (Index := Index) zfeat samples hsurj

theorem exactZABDecisionListERMFamily_not_surjective_of_le_of_two_le
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hr : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict := by
  exact
    exactZABDecisionListERMFamily_not_surjective_of_budget_lt
      (n := n) (r := r) (k := k) (Index := Index) zfeat samples
      (exactZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
        (n := n) (r := r) (k := k) hr hwidth)

end

end Mettapedia.Computability.PNP
