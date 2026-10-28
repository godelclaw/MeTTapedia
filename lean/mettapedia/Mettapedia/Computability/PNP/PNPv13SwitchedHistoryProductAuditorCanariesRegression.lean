import Mettapedia.Computability.PNP.PNPv13SwitchedHistoryProductAuditorCanaries

/-!
# Regression checks for switched-history product auditor canaries
-/

namespace Mettapedia.Computability.PNP.PNPv13SwitchedHistoryProductAuditorCanariesRegression

open Mettapedia.Computability.PNP

theorem conditional_product_positive_regression :
    switchedHistoryConditionalProductAudit.allConditionalHalfClears = true ∧
      switchedHistoryConditionalProductAudit.productBoundClears = true ∧
      switchedHistoryConditionalProductAudit.clearsSequentialProductGate = true := by
  exact switchedHistoryConditionalProduct_lab_positive_canary

theorem global_average_only_negative_regression :
    switchedHistoryGlobalAverageOnlyAudit.allGlobalHalfClears = true ∧
      switchedHistoryGlobalAverageOnlyAudit.allConditionalHalfClears = false ∧
      switchedHistoryGlobalAverageOnlyAudit.productBoundClears = false ∧
      switchedHistoryGlobalAverageOnlyAudit.clearsSequentialProductGate = false := by
  exact switchedHistoryGlobalAverageOnly_negative_canary

theorem repeated_step_negative_regression :
    switchedHistoryFirstPrefixHalfStep.conditionalHalfClears = true ∧
      switchedHistoryGlobalHalfTotalPrefixStep.totalOnPrefix = true ∧
      switchedHistoryGlobalHalfTotalPrefixStep.conditionalHalfClears = false ∧
      switchedHistoryRepeatedStepAudit.allConditionalHalfClears = false ∧
      switchedHistoryRepeatedStepAudit.productBoundClears = false := by
  exact switchedHistoryRepeatedStep_negative_canary

theorem finite_image_gate_positive_regression :
    switchedHistoryFiniteImageGateAudit.productSuccessClears = true ∧
      switchedHistoryFiniteImageGateAudit.finiteImageCoverClears = true ∧
      switchedHistoryFiniteImageGateAudit.clearsFiniteImageGate = true := by
  exact switchedHistoryFiniteImageGate_lab_positive_canary

theorem product_success_only_negative_regression :
    switchedHistoryProductSuccessOnlyAudit.productSuccessClears = true ∧
      switchedHistoryProductSuccessOnlyAudit.finiteImageCoverClears = false ∧
      switchedHistoryProductSuccessOnlyAudit.clearsFiniteImageGate = false := by
  exact switchedHistoryProductSuccessOnly_negative_canary

theorem switched_history_product_guardrails_regression :
    switchedHistoryConditionalProductAudit.clearsSequentialProductGate = true ∧
      switchedHistoryGlobalAverageOnlyAudit.allGlobalHalfClears = true ∧
      switchedHistoryGlobalAverageOnlyAudit.clearsSequentialProductGate = false ∧
      switchedHistoryRepeatedStepAudit.clearsSequentialProductGate = false ∧
      switchedHistoryProductSuccessOnlyAudit.productSuccessClears = true ∧
      switchedHistoryProductSuccessOnlyAudit.clearsFiniteImageGate = false := by
  exact switchedHistoryProductAuditorCanaries_guardrails

end Mettapedia.Computability.PNP.PNPv13SwitchedHistoryProductAuditorCanariesRegression
