import Mettapedia.Computability.PNP.CruxSynthesisRegressionKpolyBridgeExamplesData
import Mettapedia.Computability.PNP.CruxKpolyActualLocalRecoveryPayload

/-!
# Kpoly bridge example payload-card anchors

Regression anchors showing payload predictor-card and finite-probe obstructions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_full_rule_actual_local_recovery_payload_predictor_card_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3PureMeasureActualSparseRecoveryPayloadBridge
          (fullRuleActualSwitchedLocalInterface (Fin 3) 0)
          fin3ToBitVec0ActualSparseRecoveryPayloadBridge
          0) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_predictorCard
      (μ := fin3PureMeasureActualSparseRecoveryPayloadBridge)
      (T := fullRuleActualSwitchedLocalInterface (Fin 3) 0)
      (zfeat := fin3ToBitVec0ActualSparseRecoveryPayloadBridge)
      (q := 0)
      fullRuleActualSwitchedLocalInterface_lt_predictorCard_fin3k0r0_payload_bridge_regression
      (fullRuleActualSwitchedLocalInterface_surjective (Fin 3) 0)

theorem kpoly_anchor_full_rule_actual_local_no_extractor_recovery_payload_predictor_card_regression :
    ¬ ∃ zfeat : Fin 3 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            fin3PureMeasureActualSparseRecoveryPayloadBridge
            (fullRuleActualSwitchedLocalInterface (Fin 3) 0)
            zfeat
            0) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_predictorCard
      (μ := fin3PureMeasureActualSparseRecoveryPayloadBridge)
      (T := fullRuleActualSwitchedLocalInterface (Fin 3) 0)
      (r := 0)
      (q := 0)
      fullRuleActualSwitchedLocalInterface_lt_predictorCard_fin3k0r0_payload_bridge_regression
      (fullRuleActualSwitchedLocalInterface_surjective (Fin 3) 0)

theorem kpoly_anchor_full_rule_actual_local_recovery_payload_injective_probe_card_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3PureMeasureActualSparseRecoveryPayloadBridge
          (fullRuleActualSwitchedLocalInterface (Fin 3) 0)
          fin3ToBitVec0ActualSparseRecoveryPayloadBridge
          0) := by
  exact
    kpolyCoverage_anchor_actualLocal_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
      (μ := fin3PureMeasureActualSparseRecoveryPayloadBridge)
      (T := fullRuleActualSwitchedLocalInterface (Fin 3) 0)
      (zfeat := fin3ToBitVec0ActualSparseRecoveryPayloadBridge)
      (q := 0)
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge_injective
      (fun p => (fullRuleActualSwitchedLocalInterface_surjective (Fin 3) 0)
        (fin5ProbeFamilyActualSparseRecoveryPayloadBridge p))
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge_lt_card_regression

theorem kpoly_anchor_full_rule_actual_local_no_extractor_recovery_payload_injective_probe_card_regression :
    ¬ ∃ zfeat : Fin 3 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            fin3PureMeasureActualSparseRecoveryPayloadBridge
            (fullRuleActualSwitchedLocalInterface (Fin 3) 0)
            zfeat
            0) := by
  exact
    kpolyCoverage_anchor_actualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
      (μ := fin3PureMeasureActualSparseRecoveryPayloadBridge)
      (T := fullRuleActualSwitchedLocalInterface (Fin 3) 0)
      (r := 0)
      (q := 0)
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge_injective
      (fun p => (fullRuleActualSwitchedLocalInterface_surjective (Fin 3) 0)
        (fin5ProbeFamilyActualSparseRecoveryPayloadBridge p))
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge_lt_card_regression

end Mettapedia.Computability.PNP.CruxSynthesisRegression
