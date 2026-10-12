import Mettapedia.CognitiveArchitecture.Agent.WellbeingAssessment
import Mettapedia.CognitiveArchitecture.Consciousness.InterpretationAssessment

/-!
# Evidence-bearing descriptions and interpretation-relative assessment

The existing provenance-indexed view keeps typed witnesses in its ordered
ledger.  A candidate operational state fits its assignment exactly when all
ledger entries agree with that state's declared observations.  Coverage of the
assignment is what proves the reverse implication; a witness-free description
would not justify it.

This connects evidence-bearing restriction, refinement and composition to
the interpretation-relative possible-outcome framework.  Each candidate
retains one joint state and interpretation witness.  Ledger membership proves
retrieval of a reported value under the supplied evidence family; agreement
with an operational model remains a separate obligation.  Neither establishes
experiential truth without an adequate interpretation and observation model.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Consciousness.AssessmentEvidence

open Mettapedia.CognitiveArchitecture.Agent
open Mettapedia.CognitiveArchitecture.Consciousness.InterpretationAssessment

universe uState uAssessor uInterpretation uQuality uValue uEvidence uHypothesis uOutcome

variable {Owner Revision : Type} {State : Type uState}
  {Assessor : Type uAssessor} {Interpretation : Type uInterpretation} {Quality : Type uQuality}
  {Hypothesis : Type uHypothesis} {Outcome : Type uOutcome}
  {judgment : PatienthoodWellbeing.WellbeingJudgment.{max uAssessor uInterpretation uQuality,
    uValue, uEvidence} (Assessor × Interpretation × Quality) Owner Revision}

/-- Exact ledger agreement and assignment agreement characterize the same
candidate states, because every observed coordinate has existing evidence. -/
theorem compatible_iff_ledger
    (model : Model State (WellbeingAssessment.Key Owner Revision Assessor Interpretation Quality)
      judgment.Value Hypothesis Outcome)
    (view : WellbeingAssessment.View judgment) (state : State) :
    CompatibleState model view.assigned state ↔
      ∀ record ∈ view.ledger, model.observe state record.key = record.value := by
  constructor
  · intro fits record member
    obtain ⟨known, agrees⟩ := view.sound record member
    exact (fits.2 record.key known (Set.mem_univ _)).symm.trans agrees
  · intro agreesWithState
    refine ⟨fun _ _ => Set.mem_univ _, ?_⟩
    intro key known _
    obtain ⟨record, member, equalKey⟩ := view.covered key known
    subst key
    obtain ⟨recorded, agrees⟩ := view.sound record member
    exact agrees.trans (agreesWithState record member).symm

theorem possible_iff_ledger
    (model : Model State (WellbeingAssessment.Key Owner Revision Assessor Interpretation Quality)
      judgment.Value Hypothesis Outcome)
    (admitted : Set Hypothesis) (view : WellbeingAssessment.View judgment) (outcome : Outcome) :
    outcome ∈ possible model admitted view.assigned ↔
      ∃ hypothesis state, hypothesis ∈ admitted ∧
        (∀ record ∈ view.ledger, model.observe state record.key = record.value) ∧
        model.interprets hypothesis state outcome := by
  constructor
  · rintro ⟨hypothesis, state, member, fits, interpreted⟩
    exact ⟨hypothesis, state, member, (compatible_iff_ledger model view state).mp fits, interpreted⟩
  · rintro ⟨hypothesis, state, member, agreesWithState, interpreted⟩
    exact ⟨hypothesis, state, member,
      (compatible_iff_ledger model view state).mpr agreesWithState, interpreted⟩

theorem evidenced_refinement_narrows_possibilities
    (model : Model State (WellbeingAssessment.Key Owner Revision Assessor Interpretation Quality)
      judgment.Value Hypothesis Outcome)
    (admitted : Set Hypothesis) {first second : WellbeingAssessment.View judgment}
    (refines : WellbeingAssessment.View.Refines first second) :
    possible model admitted second.assigned ⊆ possible model admitted first.assigned :=
  possible_antitone_view model admitted refines.1

theorem evidenced_restriction_enlarges_possibilities
    (model : Model State (WellbeingAssessment.Key Owner Revision Assessor Interpretation Quality)
      judgment.Value Hypothesis Outcome)
    (admitted : Set Hypothesis) (view : WellbeingAssessment.View judgment)
    (observed : Set (WellbeingAssessment.Key Owner Revision Assessor Interpretation Quality)) :
    possible model admitted view.assigned ⊆
      possible model admitted (WellbeingAssessment.View.restrict observed view).assigned :=
  evidenced_refinement_narrows_possibilities model admitted
    (WellbeingAssessment.View.restrict_refines observed view)

/-- The typed retrieval witness and agreement with the candidate state are
both present.  Neither one is silently substituted for the other. -/
theorem query_evidence_and_state_agreement
    (model : Model State (WellbeingAssessment.Key Owner Revision Assessor Interpretation Quality)
      judgment.Value Hypothesis Outcome)
    (view : WellbeingAssessment.View judgment) (state : State)
    (fits : CompatibleState model view.assigned state)
    (key : WellbeingAssessment.Key Owner Revision Assessor Interpretation Quality)
    (value : judgment.Value) (read : WellbeingAssessment.View.query view key = some value) :
    Nonempty (judgment.Evidence key.observer key.occurrence value) ∧
      model.observe state key = value := by
  refine ⟨WellbeingAssessment.View.query_supported view key value read, ?_⟩
  have known : key ∈ view.assigned.context := by
    by_contra absent
    rw [(WellbeingAssessment.View.query_eq_none_iff view key).mpr absent] at read
    cases read
  have valueEqual := Option.some.inj
    ((WellbeingAssessment.View.query_of_mem view key known).symm.trans read)
  exact (fits.2 key known (Set.mem_univ _)).symm.trans valueEqual

/-- Compatible ledger composition still requires one jointly fitting state.
Appending the ledgers does not replace that witness with two local states. -/
theorem evidenced_glue_compatible_iff
    (model : Model State (WellbeingAssessment.Key Owner Revision Assessor Interpretation Quality)
      judgment.Value Hypothesis Outcome)
    (first second : WellbeingAssessment.View judgment)
    (compatible : Mettapedia.CategoryTheory.PartialSections.Compatible first.assigned second.assigned)
    (state : State) :
    CompatibleState model (WellbeingAssessment.View.glue first second compatible).assigned state ↔
      CompatibleState model first.assigned state ∧ CompatibleState model second.assigned state :=
  compatibleState_glue model compatible state

/-! ## Typed retrieval evidence and operational agreement differ -/

namespace Controls

open WellbeingAssessment.Controls

def reportModel : Model (AssessmentKey → ReportValue) AssessmentKey ReportValue Unit ReportValue where
  observe state key := state key
  interprets _ state outcome := outcome = state leftKey

def reportedState (key : AssessmentKey) : ReportValue :=
  if key = leftKey then (2, false) else (0, false)

theorem retrieved_report_fits_operational_state :
    CompatibleState reportModel selfAssessment.assigned reportedState := by
  apply (compatible_iff_ledger reportModel selfAssessment reportedState).mpr
  intro record member
  have same : record = row 0 := List.mem_singleton.mp member
  subst record
  change reportedState leftKey = (2, false)
  simp [reportedState]

/-- Another row has genuine retrieval evidence but disagrees with this same
operational state.  Retrieval alone cannot settle that agreement. -/
theorem retrieval_does_not_certify_operational_agreement :
    Nonempty (WellbeingAssessment.Controls.judgment.Evidence
      (row 2).key.observer (row 2).key.occurrence (row 2).value) ∧
      ¬ CompatibleState reportModel conflictingAssessment.assigned reportedState := by
  refine ⟨⟨(row 2).evidence⟩, ?_⟩
  intro fits
  have valueEqual := (compatible_iff_ledger reportModel conflictingAssessment reportedState).mp
    fits (row 2) (List.mem_singleton.mpr rfl)
  change reportedState leftKey = (7, false) at valueEqual
  simp [reportedState] at valueEqual

theorem compatible_report_has_joint_outcome_witness :
    (2, false) ∈ possible reportModel Set.univ selfAssessment.assigned := by
  refine ⟨(), reportedState, Set.mem_univ _, retrieved_report_fits_operational_state, ?_⟩
  change (2, false) = reportedState leftKey
  simp [reportedState]

end Controls

end Mettapedia.CognitiveArchitecture.Consciousness.AssessmentEvidence
