import Mettapedia.QuantumTheory.YangMills.ProofState

/-!
# Yang-Mills reflection-positivity gate canaries

This module records finite canaries for the reflection-positivity interface
inside the constructive-QFT gate.  It does not construct a continuum
Yang-Mills theory or an OS reconstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Finite Boolean audit for the local reflection-positivity interface gate. -/
structure YangMillsReflectionPositivityCanaryAudit where
  routeKey : String
  sampleNonnegative : Bool
  reflectionPositiveFunctional : Bool
  reflectionPositiveCone : Bool
deriving Repr

/-- The local finite reflection-positivity gate clears only when both
constructive interfaces are represented. -/
def YangMillsReflectionPositivityCanaryAudit.ClearsGate
    (audit : YangMillsReflectionPositivityCanaryAudit) : Bool :=
  audit.reflectionPositiveFunctional && audit.reflectionPositiveCone

/-- A blocked local reflection-positivity gate. -/
def YangMillsReflectionPositivityCanaryAudit.Blocked
    (audit : YangMillsReflectionPositivityCanaryAudit) : Bool :=
  !audit.ClearsGate

/-- A finite sample nonnegativity flag with no constructive
reflection-positivity interface. -/
def YangMillsReflectionPositivityCanaryAudit.SampleFlagOnly
    (audit : YangMillsReflectionPositivityCanaryAudit) : Bool :=
  audit.sampleNonnegative &&
    !(audit.reflectionPositiveFunctional || audit.reflectionPositiveCone)

/-- Positive canary: both reflection-positivity interfaces are supplied. -/
def toyYangMillsReflectionFunctionalAndConeAudit :
    YangMillsReflectionPositivityCanaryAudit where
  routeKey := "toy-yang-mills-reflection-functional-and-cone"
  sampleNonnegative := true
  reflectionPositiveFunctional := true
  reflectionPositiveCone := true

/-- Negative canary: finite sample nonnegativity alone. -/
def toyYangMillsReflectionSampleFlagOnlyAudit :
    YangMillsReflectionPositivityCanaryAudit where
  routeKey := "toy-yang-mills-reflection-sample-flag-only"
  sampleNonnegative := true
  reflectionPositiveFunctional := false
  reflectionPositiveCone := false

/-- Negative canary: the functional interface without the cone interface. -/
def toyYangMillsReflectionFunctionalOnlyAudit :
    YangMillsReflectionPositivityCanaryAudit where
  routeKey := "toy-yang-mills-reflection-functional-only"
  sampleNonnegative := true
  reflectionPositiveFunctional := true
  reflectionPositiveCone := false

/-- Negative canary: the cone interface without the functional interface. -/
def toyYangMillsReflectionConeOnlyAudit :
    YangMillsReflectionPositivityCanaryAudit where
  routeKey := "toy-yang-mills-reflection-cone-only"
  sampleNonnegative := true
  reflectionPositiveFunctional := false
  reflectionPositiveCone := true

theorem yangMillsReflectionFunctionalAndCone_bool_positive_canary :
    toyYangMillsReflectionFunctionalAndConeAudit.ClearsGate = true := by
  rfl

theorem yangMillsReflectionSampleFlagOnly_bool_negative_canary :
    toyYangMillsReflectionSampleFlagOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionSampleFlagOnlyAudit.Blocked = true ∧
      toyYangMillsReflectionSampleFlagOnlyAudit.SampleFlagOnly = true := by
  exact ⟨rfl, ⟨rfl, rfl⟩⟩

theorem yangMillsReflectionFunctionalOnly_bool_negative_canary :
    toyYangMillsReflectionFunctionalOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionFunctionalOnlyAudit.Blocked = true := by
  exact ⟨rfl, rfl⟩

theorem yangMillsReflectionConeOnly_bool_negative_canary :
    toyYangMillsReflectionConeOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionConeOnlyAudit.Blocked = true := by
  exact ⟨rfl, rfl⟩

theorem yangMillsReflectionPositivity_bool_guardrails :
    toyYangMillsReflectionFunctionalAndConeAudit.ClearsGate = true ∧
      toyYangMillsReflectionSampleFlagOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionSampleFlagOnlyAudit.Blocked = true ∧
      toyYangMillsReflectionSampleFlagOnlyAudit.SampleFlagOnly = true ∧
      toyYangMillsReflectionFunctionalOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionFunctionalOnlyAudit.Blocked = true ∧
      toyYangMillsReflectionConeOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionConeOnlyAudit.Blocked = true := by
  exact
    ⟨yangMillsReflectionFunctionalAndCone_bool_positive_canary,
      yangMillsReflectionSampleFlagOnly_bool_negative_canary.1,
      yangMillsReflectionSampleFlagOnly_bool_negative_canary.2.1,
      yangMillsReflectionSampleFlagOnly_bool_negative_canary.2.2,
      yangMillsReflectionFunctionalOnly_bool_negative_canary.1,
      yangMillsReflectionFunctionalOnly_bool_negative_canary.2,
      yangMillsReflectionConeOnly_bool_negative_canary.1,
      yangMillsReflectionConeOnly_bool_negative_canary.2⟩

/-- Interface canary matching the positive Boolean reflection-positivity audit. -/
def toyYangMillsReflectionFunctionalAndConeWorldInterfaces :
    YangMillsConstructiveRouteWorldInterfaces where
  routeKey := "toy-yang-mills-reflection-functional-and-cone"
  supplied := [.reflectionPositiveFunctional, .reflectionPositiveCone]

/-- Interface canary matching the functional-only negative audit. -/
def toyYangMillsReflectionFunctionalOnlyWorldInterfaces :
    YangMillsConstructiveRouteWorldInterfaces where
  routeKey := "toy-yang-mills-reflection-functional-only"
  supplied := [.reflectionPositiveFunctional]

/-- Interface canary matching the cone-only negative audit. -/
def toyYangMillsReflectionConeOnlyWorldInterfaces :
    YangMillsConstructiveRouteWorldInterfaces where
  routeKey := "toy-yang-mills-reflection-cone-only"
  supplied := [.reflectionPositiveCone]

theorem toyYangMillsReflectionFunctionalAndConeWorldInterfaces_clears_reflectionPositivity :
    toyYangMillsReflectionFunctionalAndConeWorldInterfaces.missingFor
      .reflectionPositivity = [] := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    YangMillsConstructiveCheck.requiredWorldInterfaces,
    toyYangMillsReflectionFunctionalAndConeWorldInterfaces]

theorem toyYangMillsReflectionFunctionalAndConeWorldInterfaces_not_clearsAll :
    ¬ toyYangMillsReflectionFunctionalAndConeWorldInterfaces.ClearsAll := by
  intro hclears
  have hcontinuum := hclears.1
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    YangMillsConstructiveCheck.requiredWorldInterfaces,
    toyYangMillsReflectionFunctionalAndConeWorldInterfaces] at hcontinuum

theorem toyYangMillsReflectionFunctionalOnlyWorldInterfaces_missing_reflectionPositivity :
    toyYangMillsReflectionFunctionalOnlyWorldInterfaces.missingFor
      .reflectionPositivity = [.reflectionPositiveCone] := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    YangMillsConstructiveCheck.requiredWorldInterfaces,
    toyYangMillsReflectionFunctionalOnlyWorldInterfaces]

theorem toyYangMillsReflectionFunctionalOnlyWorldInterfaces_not_clears_reflectionPositivity :
    toyYangMillsReflectionFunctionalOnlyWorldInterfaces.missingFor
      .reflectionPositivity ≠ [] := by
  rw [toyYangMillsReflectionFunctionalOnlyWorldInterfaces_missing_reflectionPositivity]
  simp

theorem toyYangMillsReflectionConeOnlyWorldInterfaces_missing_reflectionPositivity :
    toyYangMillsReflectionConeOnlyWorldInterfaces.missingFor
      .reflectionPositivity = [.reflectionPositiveFunctional] := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    YangMillsConstructiveCheck.requiredWorldInterfaces,
    toyYangMillsReflectionConeOnlyWorldInterfaces]

theorem toyYangMillsReflectionConeOnlyWorldInterfaces_not_clears_reflectionPositivity :
    toyYangMillsReflectionConeOnlyWorldInterfaces.missingFor
      .reflectionPositivity ≠ [] := by
  rw [toyYangMillsReflectionConeOnlyWorldInterfaces_missing_reflectionPositivity]
  simp

/-- Finite canary packet confirmed by the ignored reflection-positivity
validation lab. -/
def currentYangMillsReflectionPositivityCanaryAuditPacket : Prop :=
  toyYangMillsReflectionFunctionalAndConeAudit.ClearsGate = true ∧
    toyYangMillsReflectionSampleFlagOnlyAudit.ClearsGate = false ∧
    toyYangMillsReflectionFunctionalOnlyAudit.ClearsGate = false ∧
    toyYangMillsReflectionConeOnlyAudit.ClearsGate = false ∧
    toyYangMillsReflectionFunctionalAndConeWorldInterfaces.missingFor
      .reflectionPositivity = [] ∧
    ¬ toyYangMillsReflectionFunctionalAndConeWorldInterfaces.ClearsAll ∧
    toyYangMillsReflectionFunctionalOnlyWorldInterfaces.missingFor
      .reflectionPositivity = [.reflectionPositiveCone] ∧
    toyYangMillsReflectionConeOnlyWorldInterfaces.missingFor
      .reflectionPositivity = [.reflectionPositiveFunctional] ∧
    currentYangMillsConstructiveWorldInterfaces.missingFor
      .reflectionPositivity =
        YangMillsConstructiveCheck.reflectionPositivity.requiredWorldInterfaces ∧
    yangMillsReflectionPositivityCanaryNode.status = .checked

theorem currentYangMillsReflectionPositivityCanaryAudit :
    currentYangMillsReflectionPositivityCanaryAuditPacket := by
  unfold currentYangMillsReflectionPositivityCanaryAuditPacket
  exact
    ⟨yangMillsReflectionFunctionalAndCone_bool_positive_canary,
      yangMillsReflectionSampleFlagOnly_bool_negative_canary.1,
      yangMillsReflectionFunctionalOnly_bool_negative_canary.1,
      yangMillsReflectionConeOnly_bool_negative_canary.1,
      toyYangMillsReflectionFunctionalAndConeWorldInterfaces_clears_reflectionPositivity,
      toyYangMillsReflectionFunctionalAndConeWorldInterfaces_not_clearsAll,
      toyYangMillsReflectionFunctionalOnlyWorldInterfaces_missing_reflectionPositivity,
      toyYangMillsReflectionConeOnlyWorldInterfaces_missing_reflectionPositivity,
      currentYangMillsConstructiveWorldInterfaces_missing_reflectionPositivity,
      yangMillsReflectionPositivityCanaryNode_checked⟩

end YangMills
end QuantumTheory
end Mettapedia
