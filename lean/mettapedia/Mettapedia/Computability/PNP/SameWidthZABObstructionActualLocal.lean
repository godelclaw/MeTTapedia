import Mettapedia.Computability.PNP.ActualSwitchedLocalZABDecisionListWidthObstruction
import Mettapedia.Computability.PNP.SameWidthZABObstructionExactERM

/-!
# Same-width exact ZAB obstruction: actual-local interface consequence

This module lifts the same-width exact-ZAB budget obstruction through the
actual switched-local interface.
-/

namespace Mettapedia.Computability.PNP
namespace ActualSwitchedLocalInterface

section ActualLocal

universe u v

variable {n k : ℕ} {Index : Type u} {Block : Type v}

theorem not_nonempty_zabDecisionListData_of_surjective_predict_of_sameWidth
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (zfeat : BitVec n → BitVec n)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hvisible : 2 ≤ n + 2 * k) :
    ¬ Nonempty (ZABDecisionListData T zfeat) := by
  exact
    not_nonempty_zabDecisionListData_of_surjective_predict_of_extractorWidth_lt_truthTableGap
      (T := T) zfeat hsurj
      (sameWidthExtractor_lt_truthTableGap_of_two_le_visibleWidth
        (n := n) (k := k) hvisible)

theorem fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_sameWidth
    (zfeat : BitVec n → BitVec n)
    (hvisible : 2 ≤ n + 2 * k) :
    ¬ Nonempty
        (ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface (BitVec n) k) zfeat) := by
  exact
    not_nonempty_zabDecisionListData_of_surjective_predict_of_sameWidth
      (T := fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)
      hvisible

end ActualLocal

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
