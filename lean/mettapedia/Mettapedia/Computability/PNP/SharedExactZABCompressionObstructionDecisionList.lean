import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.SharedExactZABCompressionObstructionFeatureERM
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceData
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceAffineFeature
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceSparseThreshold
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceDecisionList
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceDecisionListRecovery

/-!
# P vs NP crux: shared exact ZAB decision-list obstruction

This module records the `BitVec n` exact-surface cardinality obstruction for
shared-basis exact `(zfeat(z), a, b)` decision-list targets and recovery data.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n p r k : ℕ} {Index : Type*}

/-- A shared-basis exact `(zfeat(z), a, b)` decision-list target on `BitVec n`
still has to pay the full exact visible surface cardinality `2^(n + 2k)` if it
were surjective. -/
theorem SharedExactZABDecisionListTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ p + 1 := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := p + 1) (Index := Index)
      hsurj h.compressionTarget

/-- Hence any shared-basis exact `(zfeat(z), a, b)` target with budget below
the full exact-surface threshold cannot be surjective. -/
theorem SharedExactZABDecisionListTargetData.not_surjective_predict_of_budget_lt
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hbudget : p + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- A simple sufficient condition for the shared-basis exact budget `p + 1` to
sit below the full `BitVec n` truth-table threshold. -/
theorem sharedExactZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
    (hfeat : p ≤ n + 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    p + 1 < 2 ^ (n + 2 * k) := by
  have hle : p + 1 ≤ n + 2 * k + 1 := Nat.succ_le_succ hfeat
  exact lt_of_le_of_lt hle <|
    exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
      (r := n) (k := k) hwidth

/-- Hence a shared-basis exact `(zfeat(z), a, b)` target cannot be surjective
when the shared-feature count is at most the full exact visible width
`n + 2k` and that width is at least `2`. -/
theorem SharedExactZABDecisionListTargetData.not_surjective_predict_of_le_of_two_le
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hfeat : p ≤ n + 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact
    h.not_surjective_predict_of_budget_lt
      (sharedExactZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
        (n := n) (p := p) (k := k) hfeat hwidth)

/-- The same contradiction applies to the recovery wrapper, since it already
packages the same exact compression target. -/
theorem SharedExactZABDecisionListRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (hbudget : p + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- And likewise under the natural width hypothesis `p ≤ n + 2k` with
`2 ≤ n + 2k`. -/
theorem SharedExactZABDecisionListRecoveryData.not_surjective_predict_of_le_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (hfeat : p ≤ n + 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_le_of_two_le hfeat hwidth

end

end Mettapedia.Computability.PNP
