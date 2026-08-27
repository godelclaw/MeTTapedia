import Mettapedia.Hyperseed.PBitQuantale

/-!
# Structural experiments with a Hyperseed evidence overlay

This file formalizes the exact division of labor proposed in Ben Goertzel's
*Representing Scientific Experiments in MeTTa: SUMO/EXPO Structure with
Hyperseed Epistemic Annotations* (2026): an EXPO-style structural experiment
record is kept separate from claims, evidence-state objects, and the
measurements or assumptions supporting those claims.

Evidence values use the bounded Hyperseed p-bit carrier.  The manuscript's
worked scoring recipe is explicitly illustrative and replaceable, so this
module does not turn that recipe into semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Hyperseed.ExperimentEvidence

open Mettapedia.Hyperseed.PBitQuantale

universe uExperiment uFactor uTarget uHypothesis uResult uTable uMeasurement
  uAssumption uClaim uEvidenceState

/-- The structural layer of a scientific experiment.  The carrier types are
left abstract so the interface can host EXPO/SUMO identifiers, MeTTa atoms, or
another faithful representation. -/
structure ExperimentStructure
    (Experiment : Type uExperiment) (Factor : Type uFactor)
    (Target : Type uTarget) (Hypothesis : Type uHypothesis)
    (Result : Type uResult) (Table : Type uTable)
    (Measurement : Type uMeasurement) where
  experiment : Experiment
  factors : List Factor
  targetVariables : List Target
  hypotheses : List Hypothesis
  results : List Result
  measurementTables : List Table
  measurements : List Measurement

/-- A claim may be supported by a measurement or by an explicit modeling
assumption.  Keeping the sum informative prevents the two kinds of provenance
from being silently identified. -/
inductive EvidenceSource
    (Measurement : Type uMeasurement) (Assumption : Type uAssumption) where
  | measurement : Measurement → EvidenceSource Measurement Assumption
  | assumption : Assumption → EvidenceSource Measurement Assumption
deriving DecidableEq, Repr

/-- One explicit `EvidenceState → Claim` annotation with its p-bit and
`supportedBy` provenance. -/
structure Annotation
    (Claim : Type uClaim) (EvidenceState : Type uEvidenceState)
    (Measurement : Type uMeasurement) (Assumption : Type uAssumption) where
  evidenceState : EvidenceState
  evidenceOf : Claim
  value : PBit
  supportedBy : List (EvidenceSource Measurement Assumption)

/-- The epistemic layer is an occurrence-preserving list of annotations.
Different evidence states for one claim are retained rather than overwritten. -/
structure EvidenceOverlay
    (Claim : Type uClaim) (EvidenceState : Type uEvidenceState)
    (Measurement : Type uMeasurement) (Assumption : Type uAssumption) where
  annotations : List (Annotation Claim EvidenceState Measurement Assumption)

/-- A complete record is the product of the structural and epistemic layers. -/
structure ScientificRecord
    (Experiment : Type uExperiment) (Factor : Type uFactor)
    (Target : Type uTarget) (Hypothesis : Type uHypothesis)
    (Result : Type uResult) (Table : Type uTable)
    (Measurement : Type uMeasurement) (Assumption : Type uAssumption)
    (Claim : Type uClaim) (EvidenceState : Type uEvidenceState) where
  experimentStructure :
    ExperimentStructure Experiment Factor Target Hypothesis Result Table Measurement
  evidence : EvidenceOverlay Claim EvidenceState Measurement Assumption

/-- Add one epistemic annotation without rewriting the experiment structure
or any previous evidence occurrence. -/
def addEvidence
    {Experiment : Type uExperiment} {Factor : Type uFactor}
    {Target : Type uTarget} {Hypothesis : Type uHypothesis}
    {Result : Type uResult} {Table : Type uTable}
    {Measurement : Type uMeasurement} {Assumption : Type uAssumption}
    {Claim : Type uClaim} {EvidenceState : Type uEvidenceState}
    (record : ScientificRecord Experiment Factor Target Hypothesis Result Table
      Measurement Assumption Claim EvidenceState)
    (annotation : Annotation Claim EvidenceState Measurement Assumption) :
    ScientificRecord Experiment Factor Target Hypothesis Result Table
      Measurement Assumption Claim EvidenceState :=
  { record with
    evidence := ⟨record.evidence.annotations ++ [annotation]⟩ }

/-- Updating the Hyperseed overlay cannot alter the EXPO structural object. -/
@[simp] theorem addEvidence_structure
    {Experiment : Type uExperiment} {Factor : Type uFactor}
    {Target : Type uTarget} {Hypothesis : Type uHypothesis}
    {Result : Type uResult} {Table : Type uTable}
    {Measurement : Type uMeasurement} {Assumption : Type uAssumption}
    {Claim : Type uClaim} {EvidenceState : Type uEvidenceState}
    (record : ScientificRecord Experiment Factor Target Hypothesis Result Table
      Measurement Assumption Claim EvidenceState)
    (annotation : Annotation Claim EvidenceState Measurement Assumption) :
    (addEvidence record annotation).experimentStructure =
      record.experimentStructure := by
  rfl

/-- Existing annotation occurrences survive an evidence update. -/
theorem addEvidence_preserves_prior
    {Experiment : Type uExperiment} {Factor : Type uFactor}
    {Target : Type uTarget} {Hypothesis : Type uHypothesis}
    {Result : Type uResult} {Table : Type uTable}
    {Measurement : Type uMeasurement} {Assumption : Type uAssumption}
    {Claim : Type uClaim} {EvidenceState : Type uEvidenceState}
    [DecidableEq Claim] [DecidableEq EvidenceState]
    [DecidableEq Measurement] [DecidableEq Assumption]
    (record : ScientificRecord Experiment Factor Target Hypothesis Result Table
      Measurement Assumption Claim EvidenceState)
    (annotation prior : Annotation Claim EvidenceState Measurement Assumption)
    (member : prior ∈ record.evidence.annotations) :
    prior ∈ (addEvidence record annotation).evidence.annotations := by
  classical
  simp only [addEvidence, List.mem_append, List.mem_singleton]
  exact Or.inl member

/-- The appended annotation is witnessed in the revised overlay. -/
theorem addEvidence_contains_new
    {Experiment : Type uExperiment} {Factor : Type uFactor}
    {Target : Type uTarget} {Hypothesis : Type uHypothesis}
    {Result : Type uResult} {Table : Type uTable}
    {Measurement : Type uMeasurement} {Assumption : Type uAssumption}
    {Claim : Type uClaim} {EvidenceState : Type uEvidenceState}
    [DecidableEq Claim] [DecidableEq EvidenceState]
    [DecidableEq Measurement] [DecidableEq Assumption]
    (record : ScientificRecord Experiment Factor Target Hypothesis Result Table
      Measurement Assumption Claim EvidenceState)
    (annotation : Annotation Claim EvidenceState Measurement Assumption) :
    annotation ∈ (addEvidence record annotation).evidence.annotations := by
  classical
  simp [addEvidence]

/-- Addition invents no annotation other than the one explicitly supplied. -/
theorem addEvidence_no_invention
    {Experiment : Type uExperiment} {Factor : Type uFactor}
    {Target : Type uTarget} {Hypothesis : Type uHypothesis}
    {Result : Type uResult} {Table : Type uTable}
    {Measurement : Type uMeasurement} {Assumption : Type uAssumption}
    {Claim : Type uClaim} {EvidenceState : Type uEvidenceState}
    [DecidableEq Claim] [DecidableEq EvidenceState]
    [DecidableEq Measurement] [DecidableEq Assumption]
    (record : ScientificRecord Experiment Factor Target Hypothesis Result Table
      Measurement Assumption Claim EvidenceState)
    (annotation candidate : Annotation Claim EvidenceState Measurement Assumption)
    (member : candidate ∈ (addEvidence record annotation).evidence.annotations) :
    candidate ∈ record.evidence.annotations ∨ candidate = annotation := by
  classical
  simpa [addEvidence] using member

#print axioms Mettapedia.Hyperseed.ExperimentEvidence.addEvidence_structure
#print axioms Mettapedia.Hyperseed.ExperimentEvidence.addEvidence_preserves_prior
#print axioms Mettapedia.Hyperseed.ExperimentEvidence.addEvidence_no_invention

end Mettapedia.Hyperseed.ExperimentEvidence
