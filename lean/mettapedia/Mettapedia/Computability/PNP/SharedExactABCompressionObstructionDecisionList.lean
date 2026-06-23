import Mettapedia.Computability.PNP.SharedExactABCompressionObstructionFeatureERM
import Mettapedia.Computability.PNP.SharedExactABERMInterfaceConsequences

/-!
# BitVec surface bounds for shared exact decision-list ERM wrappers

This module carries the decision-list budget-threshold obstruction and the
final shared exact ERM wrapper consequences.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n r k : ℕ} {Index : Type*}

/-- A shared raw exact `(a, b)` decision-list target on `BitVec n` still has to
pay the full exact visible surface cardinality `2^(n + 2k)` if it were
surjective. -/
theorem SharedABDecisionListTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedABDecisionListTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r + 1 := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := r + 1) (Index := Index)
      hsurj h.compressionTarget

/-- Hence any shared raw exact `(a, b)` target with budget below the full
exact-surface threshold cannot be surjective. -/
theorem SharedABDecisionListTargetData.not_surjective_predict_of_budget_lt
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedABDecisionListTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hbudget : r + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- A simple sufficient condition for the shared raw exact budget `r + 1` to
sit below the full `BitVec n` truth-table threshold. -/
theorem sharedExactABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
    (hfeat : r ≤ 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    r + 1 < 2 ^ (n + 2 * k) := by
  have hle1 : r + 1 ≤ 2 * k + 1 := Nat.succ_le_succ hfeat
  have hle2 : 2 * k + 1 ≤ n + 2 * k + 1 := by
    exact Nat.succ_le_succ (Nat.le_add_left (2 * k) n)
  exact lt_of_le_of_lt (le_trans hle1 hle2) <|
    exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
      (r := n) (k := k) hwidth

/-- Hence a shared raw exact `(a, b)` target cannot be surjective when the
shared-feature count is at most the raw visible width `2k` and the full exact
surface width `n + 2k` is at least `2`. -/
theorem SharedABDecisionListTargetData.not_surjective_predict_of_le_of_two_le
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedABDecisionListTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hfeat : r ≤ 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact
    h.not_surjective_predict_of_budget_lt
      (sharedExactABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
        (n := n) (r := r) (k := k) hfeat hwidth)

/-- The same contradiction applies to the recovery wrapper, since it already
packages the same exact compression target. -/
theorem SharedABDecisionListRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ features G q)
    (hbudget : r + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- And likewise under the natural width hypothesis `r ≤ 2k` with
`2 ≤ n + 2k`. -/
theorem SharedABDecisionListRecoveryData.not_surjective_predict_of_le_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ features G q)
    (hfeat : r ≤ 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_le_of_two_le hfeat hwidth

/-- The same exact-surface lower bound for the named shared raw exact ERM
family wrapper itself. -/
theorem sharedExactABAffineDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactABAffineDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) features samples).predict) :
    2 ^ (n + 2 * k) ≤ r + 1 := by
  exact
    (sharedExactABAffineDecisionListERMTargetData
      (Z := BitVec n) (r := r) (k := k) (Index := Index) features samples).bitVecSurfaceCard_le_of_surjective_predict
      hsurj

/-- Therefore the named shared raw exact ERM family cannot be surjective once
its linear budget sits below the full exact-surface threshold. -/
theorem sharedExactABAffineDecisionListERMFamily_not_surjective_of_budget_lt
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hbudget : r + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective
        (sharedExactABAffineDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) features samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    sharedExactABAffineDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (r := r) (k := k) (Index := Index) features samples hsurj

/-- In particular, the shared raw exact ERM family itself cannot be surjective
when `r ≤ 2k` and the full exact visible width `n + 2k` is at least `2`. -/
theorem sharedExactABAffineDecisionListERMFamily_not_surjective_of_le_of_two_le
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hfeat : r ≤ 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective
        (sharedExactABAffineDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) features samples).predict := by
  exact
    sharedExactABAffineDecisionListERMFamily_not_surjective_of_budget_lt
      (n := n) (r := r) (k := k) (Index := Index) features samples
      (sharedExactABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
      (n := n) (r := r) (k := k) hfeat hwidth)

/-- The final shared raw exact ERM interface inherits the same budget-threshold
obstruction. -/
theorem SharedExactABERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hbudget : r + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- And likewise under the natural width hypotheses `r ≤ 2k` and
`2 ≤ n + 2k`. -/
theorem SharedExactABERMRecoveryData.not_surjective_predict_of_le_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hfeat : r ≤ 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_le_of_two_le hfeat hwidth

end

end Mettapedia.Computability.PNP
