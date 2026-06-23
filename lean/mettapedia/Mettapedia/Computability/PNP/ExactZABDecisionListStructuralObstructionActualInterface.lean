import Mettapedia.Computability.PNP.ActualSwitchedLocalStructure
import Mettapedia.Computability.PNP.ExactZABDecisionListStructuralObstructionCore

/-!
# PNP crux: actual-local interface wrappers for raw exact ZAB obstruction

This module lifts the raw exact ZAB decision-list structural obstruction to the
manuscript-facing `ActualSwitchedLocalInterface` wrapper.
-/

namespace Mettapedia.Computability.PNP

namespace ActualSwitchedLocalInterface

theorem not_nonempty_zabDecisionListData_of_surjective_predict_of_pos_widths
    {n r k : ℕ} {Index Block : Type*}
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    (zfeat : BitVec n → BitVec r)
    (hn : 0 < n)
    (hk : 0 < k)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    ¬ Nonempty (ZABDecisionListData T zfeat) := by
  rintro ⟨hdata⟩
  exact
    not_realizedByRawExactZABDecisionListFamily_of_surjective_predict_of_pos_widths
      (n := n) (r := r) (k := k) zfeat hn hk hsurj hdata.realized

theorem fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_pos_widths
    {n r k : ℕ}
    (zfeat : BitVec n → BitVec r)
    (hn : 0 < n)
    (hk : 0 < k) :
    ¬ Nonempty
        (ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface (BitVec n) k) zfeat) := by
  exact
    not_nonempty_zabDecisionListData_of_surjective_predict_of_pos_widths
      (n := n) (r := r) (k := k)
      (T := fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat hn hk
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
