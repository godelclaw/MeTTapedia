/-!
# PNP v13 switched-history product auditor canaries

This module mirrors the finite private validation lab for switched-history
product arguments.  The product route is prefix-sensitive: global half-success
averages do not replace conditional sequential half-success checks, and product
success alone does not replace the finite predictor-image theorem needed by the
Kpoly bridge.
-/

namespace Mettapedia.Computability.PNP

/-- One finite switched-history product step in the auditor. -/
structure SwitchedHistoryProductStepAudit where
  prefixCount : Nat
  successCount : Nat
  globalUniverseCount : Nat
  globalSuccessCount : Nat
deriving DecidableEq, Repr

namespace SwitchedHistoryProductStepAudit

/-- The prefix-relative conditional half-success check. -/
def conditionalHalfClears (step : SwitchedHistoryProductStepAudit) : Bool :=
  decide (2 * step.successCount ≤ step.prefixCount)

/-- The weaker global half-success check. -/
def globalHalfClears (step : SwitchedHistoryProductStepAudit) : Bool :=
  decide (2 * step.globalSuccessCount ≤ step.globalUniverseCount)

/-- Whether the step succeeds on the whole current prefix. -/
def totalOnPrefix (step : SwitchedHistoryProductStepAudit) : Bool :=
  decide (step.successCount = step.prefixCount)

end SwitchedHistoryProductStepAudit

/-- Finite switched-history sequence audited by the canaries. -/
structure SwitchedHistoryProductAudit where
  initialCount : Nat
  finalCount : Nat
  steps : List SwitchedHistoryProductStepAudit
deriving DecidableEq, Repr

namespace SwitchedHistoryProductAudit

/-- Every step clears the prefix-relative conditional half-success check. -/
def allConditionalHalfClears (audit : SwitchedHistoryProductAudit) : Bool :=
  audit.steps.all SwitchedHistoryProductStepAudit.conditionalHalfClears

/-- Every step clears the weaker global half-success check. -/
def allGlobalHalfClears (audit : SwitchedHistoryProductAudit) : Bool :=
  audit.steps.all SwitchedHistoryProductStepAudit.globalHalfClears

/-- The finite tower product inequality for the audited sequence. -/
def productBoundClears (audit : SwitchedHistoryProductAudit) : Bool :=
  decide (2 ^ audit.steps.length * audit.finalCount ≤ audit.initialCount)

/-- Sequential product clearance requires conditional steps and the product bound. -/
def clearsSequentialProductGate (audit : SwitchedHistoryProductAudit) : Bool :=
  audit.allConditionalHalfClears && audit.productBoundClears

end SwitchedHistoryProductAudit

/-- First positive canary step: half of a four-point prefix succeeds. -/
def switchedHistoryFirstPrefixHalfStep : SwitchedHistoryProductStepAudit where
  prefixCount := 4
  successCount := 2
  globalUniverseCount := 4
  globalSuccessCount := 2

/-- Second positive canary step: half of the remaining two-point prefix succeeds. -/
def switchedHistorySecondPrefixHalfStep : SwitchedHistoryProductStepAudit where
  prefixCount := 2
  successCount := 1
  globalUniverseCount := 4
  globalSuccessCount := 2

/-- Negative canary step: globally half, but total on the current prefix. -/
def switchedHistoryGlobalHalfTotalPrefixStep : SwitchedHistoryProductStepAudit where
  prefixCount := 2
  successCount := 2
  globalUniverseCount := 4
  globalSuccessCount := 2

/-- Positive finite canary: two conditional half-success steps clear. -/
def switchedHistoryConditionalProductAudit : SwitchedHistoryProductAudit where
  initialCount := 4
  finalCount := 1
  steps := [switchedHistoryFirstPrefixHalfStep,
    switchedHistorySecondPrefixHalfStep]

/-- Negative finite canary: global half averages do not give conditional halves. -/
def switchedHistoryGlobalAverageOnlyAudit : SwitchedHistoryProductAudit where
  initialCount := 4
  finalCount := 2
  steps := [switchedHistoryFirstPrefixHalfStep,
    switchedHistoryGlobalHalfTotalPrefixStep]

/-- Negative finite canary: repeating a positive event makes the second step total. -/
def switchedHistoryRepeatedStepAudit : SwitchedHistoryProductAudit where
  initialCount := 4
  finalCount := 2
  steps := [switchedHistoryFirstPrefixHalfStep,
    switchedHistoryGlobalHalfTotalPrefixStep]

/-- Product-success versus finite-image gate audit. -/
structure SwitchedHistoryFiniteImageGateAudit where
  productSuccessClears : Bool
  finiteImageCoverClears : Bool
deriving DecidableEq, Repr

namespace SwitchedHistoryFiniteImageGateAudit

/-- The Kpoly finite-image gate clears only when both checks are present. -/
def clearsFiniteImageGate (audit : SwitchedHistoryFiniteImageGateAudit) : Bool :=
  audit.productSuccessClears && audit.finiteImageCoverClears

end SwitchedHistoryFiniteImageGateAudit

/-- Positive finite-image gate canary: both product success and finite image hold. -/
def switchedHistoryFiniteImageGateAudit : SwitchedHistoryFiniteImageGateAudit where
  productSuccessClears := true
  finiteImageCoverClears := true

/-- Negative finite-image gate canary: product success without finite image. -/
def switchedHistoryProductSuccessOnlyAudit : SwitchedHistoryFiniteImageGateAudit where
  productSuccessClears := true
  finiteImageCoverClears := false

/-- Positive lab canary: conditional prefix halves clear the product gate. -/
theorem switchedHistoryConditionalProduct_lab_positive_canary :
    switchedHistoryConditionalProductAudit.allConditionalHalfClears = true ∧
      switchedHistoryConditionalProductAudit.productBoundClears = true ∧
      switchedHistoryConditionalProductAudit.clearsSequentialProductGate = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- Negative lab canary: global averages do not replace conditional checks. -/
theorem switchedHistoryGlobalAverageOnly_negative_canary :
    switchedHistoryGlobalAverageOnlyAudit.allGlobalHalfClears = true ∧
      switchedHistoryGlobalAverageOnlyAudit.allConditionalHalfClears = false ∧
      switchedHistoryGlobalAverageOnlyAudit.productBoundClears = false ∧
      switchedHistoryGlobalAverageOnlyAudit.clearsSequentialProductGate = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Negative lab canary: a repeated positive event blocks the second conditional. -/
theorem switchedHistoryRepeatedStep_negative_canary :
    switchedHistoryFirstPrefixHalfStep.conditionalHalfClears = true ∧
      switchedHistoryGlobalHalfTotalPrefixStep.totalOnPrefix = true ∧
      switchedHistoryGlobalHalfTotalPrefixStep.conditionalHalfClears = false ∧
      switchedHistoryRepeatedStepAudit.allConditionalHalfClears = false ∧
      switchedHistoryRepeatedStepAudit.productBoundClears = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Positive lab canary: product success plus finite image clears the gate. -/
theorem switchedHistoryFiniteImageGate_lab_positive_canary :
    switchedHistoryFiniteImageGateAudit.productSuccessClears = true ∧
      switchedHistoryFiniteImageGateAudit.finiteImageCoverClears = true ∧
      switchedHistoryFiniteImageGateAudit.clearsFiniteImageGate = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- Negative lab canary: product success alone does not clear finite image. -/
theorem switchedHistoryProductSuccessOnly_negative_canary :
    switchedHistoryProductSuccessOnlyAudit.productSuccessClears = true ∧
      switchedHistoryProductSuccessOnlyAudit.finiteImageCoverClears = false ∧
      switchedHistoryProductSuccessOnlyAudit.clearsFiniteImageGate = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- The switched-history product canaries enforce both anti-smuggling guards. -/
theorem switchedHistoryProductAuditorCanaries_guardrails :
    switchedHistoryConditionalProductAudit.clearsSequentialProductGate = true ∧
      switchedHistoryGlobalAverageOnlyAudit.allGlobalHalfClears = true ∧
      switchedHistoryGlobalAverageOnlyAudit.clearsSequentialProductGate = false ∧
      switchedHistoryRepeatedStepAudit.clearsSequentialProductGate = false ∧
      switchedHistoryProductSuccessOnlyAudit.productSuccessClears = true ∧
      switchedHistoryProductSuccessOnlyAudit.clearsFiniteImageGate = false := by
  exact
    ⟨switchedHistoryConditionalProduct_lab_positive_canary.2.2,
      switchedHistoryGlobalAverageOnly_negative_canary.1,
      switchedHistoryGlobalAverageOnly_negative_canary.2.2.2,
      rfl,
      switchedHistoryProductSuccessOnly_negative_canary.1,
      switchedHistoryProductSuccessOnly_negative_canary.2.2⟩

end Mettapedia.Computability.PNP
