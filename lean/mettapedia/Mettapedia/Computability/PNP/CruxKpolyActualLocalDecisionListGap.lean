import Mettapedia.Computability.PNP.ActualSwitchedLocalZABDecisionListWidthObstruction


/-!
# PNP `Kpoly` actual-local decision-list gap anchors

Actual-local ZAB decision-list width-gap consequences, including the full-rule bit-vector endpoint.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: surjective actual-local exact ZAB decision-list
data already forces the shared extractor width to absorb the full exact-visible
surface gap `|surface| - (2k + 1)`. -/
theorem kpolyCoverage_anchor_actualSwitchedLocal_zabDecisionList_visibleCardGapLowerBound_of_surjective_predict
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {zfeat : Z → BitVec r}
    (h : ActualSwitchedLocalInterface.ZABDecisionListData T zfeat)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) - (2 * k + 1) ≤ r :=
  h.visibleCardGapLowerBound_of_surjective_predict hsurj

/-- Route-coverage anchor: equivalently, a surjective actual-local family
cannot carry exact ZAB decision-list data below that visible-surface gap. -/
theorem kpolyCoverage_anchor_actualSwitchedLocal_not_nonempty_zabDecisionListData_of_surjective_predict_of_lt_visibleCardGap
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hgap : r < Fintype.card (ExactVisiblePostSwitchSurface Z k) - (2 * k + 1)) :
    ¬ Nonempty (ActualSwitchedLocalInterface.ZABDecisionListData T zfeat) :=
  ActualSwitchedLocalInterface.not_nonempty_zabDecisionListData_of_surjective_predict_of_lt_visibleCardGap
    (T := T) zfeat hsurj hgap

/-- Route-coverage anchor: on bit-valued latent data, the full-rule actual
switched-local family already refutes the exact ZAB route whenever extractor
width stays below the truth-table gap `2^(n + 2k) - (2k + 1)`. -/
theorem kpolyCoverage_anchor_fullRuleActualSwitchedLocal_not_nonempty_zabDecisionListData_of_extractorWidth_lt_truthTableGap
    {n k r : ℕ}
    (zfeat : BitVec n → BitVec r)
    (hgap : r < 2 ^ (n + 2 * k) - (2 * k + 1)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface (BitVec n) k) zfeat) :=
  ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_extractorWidth_lt_truthTableGap
    (n := n) (k := k) (r := r) zfeat hgap

end Mettapedia.Computability.PNP
