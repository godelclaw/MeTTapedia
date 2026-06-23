import Mettapedia.Computability.PNP.CruxSynthesisRegressionKpolyBridgeExamplesData
import Mettapedia.Computability.PNP.CruxKpolyActualLocalDecisionListGap
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdActualLocal
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdSurjective

/-!
# Kpoly bridge example width anchors

Regression anchors for extractor-width consequences of the concrete full-rule examples.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_full_rule_actual_local_zab_data_forces_three_extractor_bits_regression
    {r : ℕ}
    {zfeat : BitVec 2 → BitVec r}
    (h :
      ActualSwitchedLocalInterface.ZABDecisionListData
        (fullRuleActualSwitchedLocalInterface (BitVec 2) 0) zfeat) :
    3 ≤ r := by
  exact
    kpolyCoverage_anchor_actualSwitchedLocal_zabDecisionList_visibleCardGapLowerBound_of_surjective_predict
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (zfeat := zfeat)
      h
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)

theorem kpoly_anchor_full_rule_actual_local_not_zab_data_below_truth_table_gap_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
          (fun z : BitVec 2 => z)) := by
  exact
    kpolyCoverage_anchor_fullRuleActualSwitchedLocal_not_nonempty_zabDecisionListData_of_extractorWidth_lt_truthTableGap
      (n := 2) (k := 0) (r := 2) (fun z : BitVec 2 => z) (by norm_num)

theorem kpoly_anchor_full_rule_actual_local_shared_sparse_threshold_erm_data_forces_positive_extractor_width_regression
    {r : ℕ}
    {zfeat : BitVec 2 → BitVec r}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
          zfeat)) :
    1 ≤ r := by
  have hwidth :
      2 ≤ 2 * r + 2 * 0 + 1 := by
    exact
      kpolyCoverage_anchor_surjectiveActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData
        (k := 0) (r := r)
        (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
        (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
        zfeat
        h
  omega

theorem kpoly_anchor_full_rule_actual_local_no_extractor_shared_sparse_threshold_erm_data_below_half_width_regression :
    ¬ ∃ zfeat : BitVec 2 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
            (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
            zfeat) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2) (k := 0) (r := 0)
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
      (by omega)

end Mettapedia.Computability.PNP.CruxSynthesisRegression
