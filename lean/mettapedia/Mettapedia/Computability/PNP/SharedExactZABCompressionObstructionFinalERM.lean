import Mettapedia.Computability.PNP.SharedExactZABCompressionObstructionDecisionList
import Mettapedia.Computability.PNP.SharedExactZABERMInterface

/-!
# P vs NP crux: final shared exact ZAB ERM obstruction

This module records the final `BitVec n` exact-surface obstruction for the
named shared-basis exact ERM family and manuscript-facing ERM recovery data.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n p r k : ℕ} {Index : Type*}

/-- The same exact-surface lower bound for the named shared-basis exact ERM
family wrapper itself. -/
theorem sharedExactZABAffineDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          zfeat features samples).predict) :
    2 ^ (n + 2 * k) ≤ p + 1 := by
  exact
    (sharedExactZABAffineDecisionListERMTargetData
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).bitVecSurfaceCard_le_of_surjective_predict
      hsurj

/-- Therefore the named shared-basis exact ERM family cannot be surjective once
its linear budget sits below the full exact-surface threshold. -/
theorem sharedExactZABAffineDecisionListERMFamily_not_surjective_of_budget_lt
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hbudget : p + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          zfeat features samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    sharedExactZABAffineDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples hsurj

/-- In particular, the shared-basis exact ERM family itself cannot be
surjective when `p ≤ n + 2k` and the full exact visible width `n + 2k` is at
least `2`. -/
theorem sharedExactZABAffineDecisionListERMFamily_not_surjective_of_le_of_two_le
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hfeat : p ≤ n + 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          zfeat features samples).predict := by
  exact
    sharedExactZABAffineDecisionListERMFamily_not_surjective_of_budget_lt
      (n := n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples
      (sharedExactZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
        (n := n) (p := p) (k := k) hfeat hwidth)

/-- The final shared-basis exact ERM interface inherits the same
budget-threshold obstruction. -/
theorem SharedExactZABERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : p + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- And likewise under the natural width hypotheses `p ≤ n + 2k` and
`2 ≤ n + 2k`. -/
theorem SharedExactZABERMRecoveryData.not_surjective_predict_of_le_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hfeat : p ≤ n + 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_le_of_two_le hfeat hwidth

end

end Mettapedia.Computability.PNP
