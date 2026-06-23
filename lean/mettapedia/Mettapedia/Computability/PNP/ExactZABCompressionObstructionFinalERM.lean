import Mettapedia.Computability.PNP.ExactZABCompressionObstructionDecisionList

/-!
# Exact ZAB compression obstruction: final ERM recovery layer

This module lifts the exact decision-list target obstruction through the final
non-shared exact ZAB ERM recovery interface.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n r k : ℕ} {Index : Type*}

theorem ExactZABERMRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r + 2 * k + 1 := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactZABERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : r + 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

theorem ExactZABERMRecoveryData.not_surjective_predict_of_le_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hr : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_le_of_two_le hr hwidth

end

end Mettapedia.Computability.PNP
