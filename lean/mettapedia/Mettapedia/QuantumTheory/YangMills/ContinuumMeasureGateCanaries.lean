import Mettapedia.QuantumTheory.YangMills.ProofState

/-!
# Yang-Mills continuum-measure gate canaries

This module records finite canaries for the continuum-measure interface inside
the constructive-QFT gate.  It does not construct a continuum Yang-Mills
measure.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Finite Boolean audit for the local continuum-measure interface gate. -/
structure YangMillsContinuumMeasureCanaryAudit where
  routeKey : String
  finiteSamplesAvailable : Bool
  latticeFieldFamilySampler : Bool
  continuumMeasureTightness : Bool
  continuumMeasureLimit : Bool
deriving Repr

/-- The local finite continuum-measure gate clears only when the sampler,
tightness, and limit interfaces are all represented. -/
def YangMillsContinuumMeasureCanaryAudit.ClearsGate
    (audit : YangMillsContinuumMeasureCanaryAudit) : Bool :=
  audit.latticeFieldFamilySampler &&
    audit.continuumMeasureTightness &&
    audit.continuumMeasureLimit

/-- A blocked local continuum-measure gate. -/
def YangMillsContinuumMeasureCanaryAudit.Blocked
    (audit : YangMillsContinuumMeasureCanaryAudit) : Bool :=
  !audit.ClearsGate

/-- Finite samples plus a sampler interface, with no tightness or limit. -/
def YangMillsContinuumMeasureCanaryAudit.SamplerOnly
    (audit : YangMillsContinuumMeasureCanaryAudit) : Bool :=
  audit.finiteSamplesAvailable &&
    audit.latticeFieldFamilySampler &&
    !audit.continuumMeasureTightness &&
    !audit.continuumMeasureLimit

/-- Positive canary: sampler, tightness, and limit interfaces are supplied. -/
def toyYangMillsContinuumMeasureFullStackAudit :
    YangMillsContinuumMeasureCanaryAudit where
  routeKey := "toy-yang-mills-continuum-measure-full-stack"
  finiteSamplesAvailable := true
  latticeFieldFamilySampler := true
  continuumMeasureTightness := true
  continuumMeasureLimit := true

/-- Negative canary: finite samples and a sampler alone. -/
def toyYangMillsContinuumMeasureSamplerOnlyAudit :
    YangMillsContinuumMeasureCanaryAudit where
  routeKey := "toy-yang-mills-continuum-measure-sampler-only"
  finiteSamplesAvailable := true
  latticeFieldFamilySampler := true
  continuumMeasureTightness := false
  continuumMeasureLimit := false

/-- Negative canary: sampler plus tightness without a represented limit. -/
def toyYangMillsContinuumMeasureTightnessWithoutLimitAudit :
    YangMillsContinuumMeasureCanaryAudit where
  routeKey := "toy-yang-mills-continuum-measure-tightness-without-limit"
  finiteSamplesAvailable := true
  latticeFieldFamilySampler := true
  continuumMeasureTightness := true
  continuumMeasureLimit := false

/-- Negative canary: sampler plus limit without tightness. -/
def toyYangMillsContinuumMeasureLimitWithoutTightnessAudit :
    YangMillsContinuumMeasureCanaryAudit where
  routeKey := "toy-yang-mills-continuum-measure-limit-without-tightness"
  finiteSamplesAvailable := true
  latticeFieldFamilySampler := true
  continuumMeasureTightness := false
  continuumMeasureLimit := true

theorem yangMillsContinuumMeasureFullStack_bool_positive_canary :
    toyYangMillsContinuumMeasureFullStackAudit.ClearsGate = true := by
  rfl

theorem yangMillsContinuumMeasureSamplerOnly_bool_negative_canary :
    toyYangMillsContinuumMeasureSamplerOnlyAudit.ClearsGate = false ∧
      toyYangMillsContinuumMeasureSamplerOnlyAudit.Blocked = true ∧
      toyYangMillsContinuumMeasureSamplerOnlyAudit.SamplerOnly = true := by
  exact ⟨rfl, ⟨rfl, rfl⟩⟩

theorem yangMillsContinuumMeasureTightnessWithoutLimit_bool_negative_canary :
    toyYangMillsContinuumMeasureTightnessWithoutLimitAudit.ClearsGate = false ∧
      toyYangMillsContinuumMeasureTightnessWithoutLimitAudit.Blocked = true := by
  exact ⟨rfl, rfl⟩

theorem yangMillsContinuumMeasureLimitWithoutTightness_bool_negative_canary :
    toyYangMillsContinuumMeasureLimitWithoutTightnessAudit.ClearsGate = false ∧
      toyYangMillsContinuumMeasureLimitWithoutTightnessAudit.Blocked = true := by
  exact ⟨rfl, rfl⟩

theorem yangMillsContinuumMeasure_bool_guardrails :
    toyYangMillsContinuumMeasureFullStackAudit.ClearsGate = true ∧
      toyYangMillsContinuumMeasureSamplerOnlyAudit.ClearsGate = false ∧
      toyYangMillsContinuumMeasureSamplerOnlyAudit.Blocked = true ∧
      toyYangMillsContinuumMeasureSamplerOnlyAudit.SamplerOnly = true ∧
      toyYangMillsContinuumMeasureTightnessWithoutLimitAudit.ClearsGate =
        false ∧
      toyYangMillsContinuumMeasureTightnessWithoutLimitAudit.Blocked = true ∧
      toyYangMillsContinuumMeasureLimitWithoutTightnessAudit.ClearsGate =
        false ∧
      toyYangMillsContinuumMeasureLimitWithoutTightnessAudit.Blocked = true := by
  exact
    ⟨yangMillsContinuumMeasureFullStack_bool_positive_canary,
      yangMillsContinuumMeasureSamplerOnly_bool_negative_canary.1,
      yangMillsContinuumMeasureSamplerOnly_bool_negative_canary.2.1,
      yangMillsContinuumMeasureSamplerOnly_bool_negative_canary.2.2,
      yangMillsContinuumMeasureTightnessWithoutLimit_bool_negative_canary.1,
      yangMillsContinuumMeasureTightnessWithoutLimit_bool_negative_canary.2,
      yangMillsContinuumMeasureLimitWithoutTightness_bool_negative_canary.1,
      yangMillsContinuumMeasureLimitWithoutTightness_bool_negative_canary.2⟩

/-- Interface canary matching the positive Boolean continuum-measure audit. -/
def toyYangMillsContinuumMeasureFullStackWorldInterfaces :
    YangMillsConstructiveRouteWorldInterfaces where
  routeKey := "toy-yang-mills-continuum-measure-full-stack"
  supplied :=
    [ .latticeFieldFamilySampler
    , .continuumMeasureTightness
    , .continuumMeasureLimit
    ]

/-- Interface canary matching the sampler-only negative audit. -/
def toyYangMillsContinuumMeasureSamplerOnlyWorldInterfaces :
    YangMillsConstructiveRouteWorldInterfaces where
  routeKey := "toy-yang-mills-continuum-measure-sampler-only"
  supplied := [.latticeFieldFamilySampler]

/-- Interface canary matching tightness without limit. -/
def toyYangMillsContinuumMeasureTightnessWithoutLimitWorldInterfaces :
    YangMillsConstructiveRouteWorldInterfaces where
  routeKey := "toy-yang-mills-continuum-measure-tightness-without-limit"
  supplied := [.latticeFieldFamilySampler, .continuumMeasureTightness]

/-- Interface canary matching limit without tightness. -/
def toyYangMillsContinuumMeasureLimitWithoutTightnessWorldInterfaces :
    YangMillsConstructiveRouteWorldInterfaces where
  routeKey := "toy-yang-mills-continuum-measure-limit-without-tightness"
  supplied := [.latticeFieldFamilySampler, .continuumMeasureLimit]

theorem toyYangMillsContinuumMeasureFullStackWorldInterfaces_clears_continuumMeasure :
    toyYangMillsContinuumMeasureFullStackWorldInterfaces.missingFor
      .continuumMeasure = [] := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    YangMillsConstructiveCheck.requiredWorldInterfaces,
    toyYangMillsContinuumMeasureFullStackWorldInterfaces]

theorem toyYangMillsContinuumMeasureFullStackWorldInterfaces_not_clearsAll :
    ¬ toyYangMillsContinuumMeasureFullStackWorldInterfaces.ClearsAll := by
  intro hclears
  have hcovariance := hclears.2.1
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    YangMillsConstructiveCheck.requiredWorldInterfaces,
    toyYangMillsContinuumMeasureFullStackWorldInterfaces] at hcovariance

theorem toyYangMillsContinuumMeasureSamplerOnlyWorldInterfaces_missing_continuumMeasure :
    toyYangMillsContinuumMeasureSamplerOnlyWorldInterfaces.missingFor
      .continuumMeasure =
        [.continuumMeasureTightness, .continuumMeasureLimit] := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    YangMillsConstructiveCheck.requiredWorldInterfaces,
    toyYangMillsContinuumMeasureSamplerOnlyWorldInterfaces]

theorem toyYangMillsContinuumMeasureTightnessWithoutLimitWorldInterfaces_missing_continuumMeasure :
    toyYangMillsContinuumMeasureTightnessWithoutLimitWorldInterfaces.missingFor
      .continuumMeasure = [.continuumMeasureLimit] := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    YangMillsConstructiveCheck.requiredWorldInterfaces,
    toyYangMillsContinuumMeasureTightnessWithoutLimitWorldInterfaces]

theorem toyYangMillsContinuumMeasureLimitWithoutTightnessWorldInterfaces_missing_continuumMeasure :
    toyYangMillsContinuumMeasureLimitWithoutTightnessWorldInterfaces.missingFor
      .continuumMeasure = [.continuumMeasureTightness] := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    YangMillsConstructiveCheck.requiredWorldInterfaces,
    toyYangMillsContinuumMeasureLimitWithoutTightnessWorldInterfaces]

/-- Finite canary packet confirmed by the ignored continuum-measure validation
lab. -/
def currentYangMillsContinuumMeasureCanaryAuditPacket : Prop :=
  toyYangMillsContinuumMeasureFullStackAudit.ClearsGate = true ∧
    toyYangMillsContinuumMeasureSamplerOnlyAudit.ClearsGate = false ∧
    toyYangMillsContinuumMeasureTightnessWithoutLimitAudit.ClearsGate =
      false ∧
    toyYangMillsContinuumMeasureLimitWithoutTightnessAudit.ClearsGate =
      false ∧
    toyYangMillsContinuumMeasureFullStackWorldInterfaces.missingFor
      .continuumMeasure = [] ∧
    ¬ toyYangMillsContinuumMeasureFullStackWorldInterfaces.ClearsAll ∧
    toyYangMillsContinuumMeasureSamplerOnlyWorldInterfaces.missingFor
      .continuumMeasure =
        [.continuumMeasureTightness, .continuumMeasureLimit] ∧
    toyYangMillsContinuumMeasureTightnessWithoutLimitWorldInterfaces.missingFor
      .continuumMeasure = [.continuumMeasureLimit] ∧
    toyYangMillsContinuumMeasureLimitWithoutTightnessWorldInterfaces.missingFor
      .continuumMeasure = [.continuumMeasureTightness] ∧
    currentYangMillsConstructiveWorldInterfaces.missingFor .continuumMeasure =
      YangMillsConstructiveCheck.continuumMeasure.requiredWorldInterfaces ∧
    yangMillsContinuumMeasureCanaryNode.status = .checked

theorem currentYangMillsContinuumMeasureCanaryAudit :
    currentYangMillsContinuumMeasureCanaryAuditPacket := by
  unfold currentYangMillsContinuumMeasureCanaryAuditPacket
  exact
    ⟨yangMillsContinuumMeasureFullStack_bool_positive_canary,
      yangMillsContinuumMeasureSamplerOnly_bool_negative_canary.1,
      yangMillsContinuumMeasureTightnessWithoutLimit_bool_negative_canary.1,
      yangMillsContinuumMeasureLimitWithoutTightness_bool_negative_canary.1,
      toyYangMillsContinuumMeasureFullStackWorldInterfaces_clears_continuumMeasure,
      toyYangMillsContinuumMeasureFullStackWorldInterfaces_not_clearsAll,
      toyYangMillsContinuumMeasureSamplerOnlyWorldInterfaces_missing_continuumMeasure,
      toyYangMillsContinuumMeasureTightnessWithoutLimitWorldInterfaces_missing_continuumMeasure,
      toyYangMillsContinuumMeasureLimitWithoutTightnessWorldInterfaces_missing_continuumMeasure,
      currentYangMillsConstructiveWorldInterfaces_missing_continuumMeasure,
      yangMillsContinuumMeasureCanaryNode_checked⟩

end YangMills
end QuantumTheory
end Mettapedia
