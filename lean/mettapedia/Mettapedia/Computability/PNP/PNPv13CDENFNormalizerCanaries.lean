import Mettapedia.Computability.PNP.PNPv13EvidenceNormalization

/-!
# PNP v13 CD-ENF normalizer canaries

This module mirrors the finite private validation lab for the CD evidence
normalizer.  A target-relevant raw leaf must normalize to a neutral, safe, or
hidden-gauge class.  Any target-relevant residual leaf is a concrete proof
obligation, recorded with the raw atom, source, and branch context.
-/

namespace Mettapedia.Computability.PNP

/-- Raw atoms seen by the finite CD-ENF normalizer canary. -/
inductive CDENFRawAtom where
  | neutralContext
  | safeBuffer
  | hiddenGauge
  | positiveResidual
deriving DecidableEq, Repr

/-- Normal classes allowed by the CD-ENF evidence-normalization boundary. -/
inductive CDENFAtomClass where
  | neutral
  | safe
  | gauge
  | residual
deriving DecidableEq, Repr

/-- Public source tag for a finite CD-ENF leaf. -/
inductive CDENFLeafSource where
  | contextQuotient
  | safeBufferEnvelope
  | hiddenGaugeFreshness
  | positiveCorrelationTail
  | offTargetNoise
deriving DecidableEq, Repr

/-- Minimal branch context needed by the residual report. -/
inductive CDENFBranchContext where
  | targetMessageBranch
  | offTargetBranch
deriving DecidableEq, Repr

/-- A raw CD-ENF leaf before target-relevant residual detection. -/
structure CDENFLeaf where
  rawAtom : CDENFRawAtom
  source : CDENFLeafSource
  branchContext : CDENFBranchContext
deriving DecidableEq, Repr

/-- A concrete target-relevant residual proof obligation. -/
structure CDENFResidualReport where
  rawAtom : CDENFRawAtom
  source : CDENFLeafSource
  branchContext : CDENFBranchContext
deriving DecidableEq, Repr

/-- The finite CD-ENF normalizer used by the validation lab canaries. -/
def normalizeCDENFRawAtom : CDENFRawAtom → CDENFAtomClass
  | .neutralContext => .neutral
  | .safeBuffer => .safe
  | .hiddenGauge => .gauge
  | .positiveResidual => .residual

/-- The target-allowed normal classes are exactly Neutral, Safe, and Gauge. -/
def CDENFAtomClass.TargetAllowed (cls : CDENFAtomClass) : Prop :=
  cls = .neutral ∨ cls = .safe ∨ cls = .gauge

/-- Target relevance is a branch-context property, not a raw-atom class. -/
def CDENFLeaf.TargetRelevant (leaf : CDENFLeaf) : Prop :=
  leaf.branchContext = .targetMessageBranch

/-- Normal class assigned to a finite CD-ENF leaf. -/
def CDENFLeaf.normalClass (leaf : CDENFLeaf) : CDENFAtomClass :=
  normalizeCDENFRawAtom leaf.rawAtom

/-- A target-relevant residual report, when one survives normalization. -/
def CDENFLeaf.targetResidualReport? (leaf : CDENFLeaf) :
    Option CDENFResidualReport :=
  match leaf.branchContext with
  | .targetMessageBranch =>
      match leaf.normalClass with
      | .residual =>
          some
            { rawAtom := leaf.rawAtom
              source := leaf.source
              branchContext := leaf.branchContext }
      | .neutral => none
      | .safe => none
      | .gauge => none
  | .offTargetBranch => none

/-- Collect every surviving target-relevant residual proof obligation. -/
def CDENFResidualReports : List CDENFLeaf → List CDENFResidualReport
  | [] => []
  | leaf :: leaves =>
      match leaf.targetResidualReport? with
      | some report => report :: CDENFResidualReports leaves
      | none => CDENFResidualReports leaves

/-- The finite detector clears exactly when no target-relevant residual remains. -/
def CDENFAllTargetRelevantLeavesInAllowedClasses
    (leaves : List CDENFLeaf) : Prop :=
  CDENFResidualReports leaves = []

/-- Neutral target leaf used by the positive and negative canaries. -/
def cdenfNeutralTargetLeaf : CDENFLeaf where
  rawAtom := .neutralContext
  source := .contextQuotient
  branchContext := .targetMessageBranch

/-- Safe-buffer target leaf used by the positive and negative canaries. -/
def cdenfSafeTargetLeaf : CDENFLeaf where
  rawAtom := .safeBuffer
  source := .safeBufferEnvelope
  branchContext := .targetMessageBranch

/-- Hidden-gauge target leaf used by the positive canary. -/
def cdenfGaugeTargetLeaf : CDENFLeaf where
  rawAtom := .hiddenGauge
  source := .hiddenGaugeFreshness
  branchContext := .targetMessageBranch

/-- A residual leaf outside the target branch. -/
def cdenfOffTargetResidualLeaf : CDENFLeaf where
  rawAtom := .positiveResidual
  source := .offTargetNoise
  branchContext := .offTargetBranch

/-- A residual leaf on the target branch; this is the negative canary. -/
def cdenfTargetResidualLeaf : CDENFLeaf where
  rawAtom := .positiveResidual
  source := .positiveCorrelationTail
  branchContext := .targetMessageBranch

/-- Report produced by the target residual canary. -/
def cdenfTargetResidualReport : CDENFResidualReport where
  rawAtom := .positiveResidual
  source := .positiveCorrelationTail
  branchContext := .targetMessageBranch

/-- Positive finite canary: all target-relevant leaves are neutral/safe/gauge. -/
def cdenfPositiveCanaryLeaves : List CDENFLeaf :=
  [cdenfNeutralTargetLeaf, cdenfSafeTargetLeaf, cdenfGaugeTargetLeaf,
    cdenfOffTargetResidualLeaf]

/-- Negative finite canary: one target-relevant residual survives. -/
def cdenfNegativeCanaryLeaves : List CDENFLeaf :=
  [cdenfNeutralTargetLeaf, cdenfTargetResidualLeaf, cdenfSafeTargetLeaf]

/-- The positive lab canary clears with an empty target-residual report. -/
theorem cdenfNormalizer_lab_positive_canary :
    CDENFAllTargetRelevantLeavesInAllowedClasses cdenfPositiveCanaryLeaves ∧
      CDENFResidualReports cdenfPositiveCanaryLeaves = [] := by
  exact ⟨rfl, rfl⟩

/-- The negative lab canary reports the concrete target-relevant residual. -/
theorem cdenfNormalizer_lab_negative_canary :
    CDENFResidualReports cdenfNegativeCanaryLeaves =
        [cdenfTargetResidualReport] ∧
      ¬ CDENFAllTargetRelevantLeavesInAllowedClasses
        cdenfNegativeCanaryLeaves := by
  constructor
  · rfl
  · intro hclear
    change [cdenfTargetResidualReport] = [] at hclear
    cases hclear

/-- The residual report pins the raw atom, source, and minimal branch context. -/
theorem cdenfNormalizer_lab_negative_report_pinpoints_obligation :
    cdenfTargetResidualReport.rawAtom = .positiveResidual ∧
      cdenfTargetResidualReport.source = .positiveCorrelationTail ∧
      cdenfTargetResidualReport.branchContext = .targetMessageBranch := by
  exact ⟨rfl, rfl, rfl⟩

/-- Off-target residual noise is not a target CD-ENF residual obligation. -/
theorem cdenfNormalizer_offTargetResidual_not_target_obligation :
    cdenfOffTargetResidualLeaf.targetResidualReport? = none ∧
      CDENFAllTargetRelevantLeavesInAllowedClasses
        [cdenfOffTargetResidualLeaf] := by
  exact ⟨rfl, rfl⟩

/-- Finite evidence-normalization surface induced by the CD-ENF classes. -/
def cdenfEvidenceSurface : V13EvidenceNormalizationSurface CDENFLeaf where
  targetRelevant := fun leaf => leaf.branchContext = .targetMessageBranch
  neutral := fun leaf => leaf.normalClass = .neutral
  safeBuffer := fun leaf => leaf.normalClass = .safe
  hiddenGauge := fun leaf => leaf.normalClass = .gauge

/-- The target residual canary is a residual atom in the v13 semantic surface. -/
theorem cdenfTargetResidualLeaf_residualAtom :
    cdenfEvidenceSurface.ResidualAtom cdenfTargetResidualLeaf := by
  unfold V13EvidenceNormalizationSurface.ResidualAtom
  change
    cdenfTargetResidualLeaf.branchContext = .targetMessageBranch ∧
      ¬ cdenfTargetResidualLeaf.normalClass = .neutral ∧
      ¬ cdenfTargetResidualLeaf.normalClass = .safe ∧
      ¬ cdenfTargetResidualLeaf.normalClass = .gauge
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro h
    cases h
  · intro h
    cases h
  · intro h
    cases h

/-- The target residual canary blocks v13 non-neutral normalization. -/
theorem cdenfNormalizer_lab_negative_blocks_v13_normalization :
    ¬ cdenfEvidenceSurface.NormalizesNonNeutral := by
  exact
    V13EvidenceNormalizationSurface.not_normalizesNonNeutral_of_residualAtom
      cdenfTargetResidualLeaf_residualAtom

/-- The canaries separate off-target residual noise from target obligations. -/
theorem cdenfNormalizerCanaries_separate_offTarget_from_targetResidual :
    CDENFAllTargetRelevantLeavesInAllowedClasses [cdenfOffTargetResidualLeaf] ∧
      ¬ CDENFAllTargetRelevantLeavesInAllowedClasses [cdenfTargetResidualLeaf] := by
  constructor
  · rfl
  · intro hclear
    change [cdenfTargetResidualReport] = [] at hclear
    cases hclear

end Mettapedia.Computability.PNP
