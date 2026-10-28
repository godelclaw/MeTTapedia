import CodingAgent
import ContextProjection

/-!
# Memory retrieval at a bounded decision boundary

This adapter contract separates vector candidates from complete observations.
It reuses the event projection and brokered coding-agent models. Numerical
distance calculations, retrieval relevance, faithful source revisions and
exhaustive scope enumeration remain external obligations. A provider cannot
establish exhaustive coverage merely by labelling its result complete.

The schema includes the model, tokenizer, input preparation and numerical
representation. Equal dimensions alone do not make embeddings comparable.
Evidence identities are stable under copying; this establishes deduplication,
not statistical independence or a criterion for consciousness.
-/

namespace MemoryRetrievalBoundary

inductive Metric where
  | cosine | squaredEuclidean | innerProduct
deriving Repr, DecidableEq

structure EmbeddingProfile where
  modelRevision : Nat
  tokenizerRevision : Nat
  inputPreparation : Nat
  dimension : Nat
  normalized : Bool
  metric : Metric
  representation : Nat
deriving Repr, DecidableEq

structure Capture where
  request : Nat
  scope : Nat
  sourceRevision : Nat
  profile : EmbeddingProfile
deriving Repr, DecidableEq

inductive Coverage where
  | candidates
  | exhaustive
deriving Repr, DecidableEq

structure Retrieval where
  capture : Capture
  occurrences : List Nat
  coverage : Coverage
deriving Repr, DecidableEq

/-- Equality is checked against the captured request, scope, source version
and complete embedding profile. No live configuration substitutes for it. -/
def observation (current : Capture) (result : Retrieval) :
    ContextProjection.Observation (List Nat) :=
  if current = result.capture then
    if result.occurrences.isEmpty then
      match result.coverage with
      | .candidates => .unavailable
      | .exhaustive => .absent
    else .known result.occurrences
  else .unavailable

def refresh (previous : Option (List Nat)) (current : Capture)
    (result : Retrieval) : Option (List Nat) :=
  ContextProjection.admit previous (observation current result)

theorem mismatched_capture_is_unavailable (current : Capture) (result : Retrieval)
    (different : current ≠ result.capture) :
    observation current result = .unavailable := by
  simp [observation, different]

theorem mismatched_capture_preserves_previous (previous : Option (List Nat))
    (current : Capture) (result : Retrieval) (different : current ≠ result.capture) :
    refresh previous current result = previous := by
  simp [refresh, mismatched_capture_is_unavailable current result different,
    ContextProjection.admit]

theorem changed_model_rejects (current : Capture) (result : Retrieval)
    (different : current.profile.modelRevision ≠ result.capture.profile.modelRevision) :
    observation current result = .unavailable := by
  apply mismatched_capture_is_unavailable
  intro same
  exact different (congrArg (fun c => c.profile.modelRevision) same)

theorem changed_preparation_rejects (current : Capture) (result : Retrieval)
    (different : current.profile.inputPreparation ≠ result.capture.profile.inputPreparation) :
    observation current result = .unavailable := by
  apply mismatched_capture_is_unavailable
  intro same
  exact different (congrArg (fun c => c.profile.inputPreparation) same)

theorem changed_revision_rejects (current : Capture) (result : Retrieval)
    (different : current.sourceRevision ≠ result.capture.sourceRevision) :
    observation current result = .unavailable := by
  apply mismatched_capture_is_unavailable
  intro same
  exact different (congrArg Capture.sourceRevision same)

theorem wrong_request_rejects (current : Capture) (result : Retrieval)
    (different : current.request ≠ result.capture.request) :
    observation current result = .unavailable := by
  apply mismatched_capture_is_unavailable
  intro same
  exact different (congrArg Capture.request same)

theorem wrong_scope_rejects (current : Capture) (result : Retrieval)
    (different : current.scope ≠ result.capture.scope) :
    observation current result = .unavailable := by
  apply mismatched_capture_is_unavailable
  intro same
  exact different (congrArg Capture.scope same)

theorem empty_candidates_are_unavailable (current : Capture) :
    observation current ⟨current, [], .candidates⟩ = .unavailable := by
  simp [observation]

theorem empty_candidates_preserve_previous (previous : Option (List Nat))
    (current : Capture) :
    refresh previous current ⟨current, [], .candidates⟩ = previous := by
  simp [refresh, empty_candidates_are_unavailable, ContextProjection.admit]

theorem current_complete_empty_is_absent (current : Capture) :
    observation current ⟨current, [], .exhaustive⟩ = .absent := by
  simp [observation]

theorem complete_empty_clears_previous (previous : Option (List Nat))
    (current : Capture) :
    refresh previous current ⟨current, [], .exhaustive⟩ = none := by
  simp [refresh, current_complete_empty_is_absent, ContextProjection.admit]

theorem absence_requires_current_complete_empty (current : Capture)
    (result : Retrieval) (absent : observation current result = .absent) :
    current = result.capture ∧ result.occurrences = [] ∧
      result.coverage = .exhaustive := by
  rcases result with ⟨captured, occurrences, coverage⟩
  by_cases same : current = captured
  · subst captured
    cases occurrences <;> cases coverage <;> simp_all [observation]
  · simp [observation, same] at absent

theorem current_candidates_are_known (current : Capture) (head : Nat)
    (tail : List Nat) (coverage : Coverage) :
    observation current ⟨current, head :: tail, coverage⟩ = .known (head :: tail) := by
  simp [observation]

/-- Last-known context and fresh decision input have different roles. A
consumer sees availability even when earlier context rows are retained. -/
structure Readout where
  status : ContextProjection.Observation (List Nat)
  contextRows : Option (List Nat)
  decisionRows : Option (List Nat)
deriving Repr, DecidableEq

def readout (previous : Option (List Nat)) (current : Capture)
    (result : Retrieval) : Readout :=
  let status := observation current result
  { status := status
    contextRows := ContextProjection.admit previous status
    decisionRows := match status with
      | .unavailable => none
      | .absent => some []
      | .known rows => some rows }

theorem stale_result_cannot_supply_decision_rows (previous : Option (List Nat))
    (current : Capture) (result : Retrieval) (different : current ≠ result.capture) :
    (readout previous current result).decisionRows = none := by
  simp [readout, mismatched_capture_is_unavailable current result different]

theorem incomplete_empty_retains_context_without_decision_authority
    (previous : Option (List Nat)) (current : Capture) :
    readout previous current ⟨current, [], .candidates⟩ =
      ⟨.unavailable, previous, none⟩ := by
  simp [readout, empty_candidates_are_unavailable, ContextProjection.admit]

theorem complete_empty_supplies_explicit_absence (previous : Option (List Nat))
    (current : Capture) :
    readout previous current ⟨current, [], .exhaustive⟩ =
      ⟨.absent, none, some []⟩ := by
  simp [readout, current_complete_empty_is_absent, ContextProjection.admit]

/-- This is an evidence identity set, not a count of independent witnesses. -/
abbrev EvidenceSet := Nat → Bool

def insertEvidence (identities : EvidenceSet) (id : Nat) : EvidenceSet :=
  fun queried => if queried = id then true else identities queried

theorem copying_evidence_is_idempotent (identities : EvidenceSet) (id : Nat) :
    insertEvidence (insertEvidence identities id) id = insertEvidence identities id := by
  funext queried
  by_cases same : queried = id <;> simp [insertEvidence, same]

theorem distinct_identity_is_retained (identities : EvidenceSet) (id other : Nat)
    (different : other ≠ id) :
    insertEvidence identities id other = identities other := by
  simp [insertEvidence, different]

/-- A receipt-dependent decision uses the existing latest-event projection.
The Boolean payload abstracts the task-specific predicate, not model prose. -/
def evidenceDecision (required : Nat)
    (ledger : List (ContextProjection.Revision Nat Bool)) : Bool :=
  (ContextProjection.latest required ledger).getD false

theorem relevant_evidence_changes_decision (required : Nat)
    (ledger : List (ContextProjection.Revision Nat Bool)) (verdict : Bool) :
    evidenceDecision required (ledger ++ [⟨required, verdict⟩]) = verdict := by
  simp [evidenceDecision, ContextProjection.newest_revision_wins]

theorem unrelated_evidence_preserves_decision (required other : Nat)
    (different : other ≠ required)
    (ledger : List (ContextProjection.Revision Nat Bool)) (verdict : Bool) :
    evidenceDecision required (ledger ++ [⟨other, verdict⟩]) =
      evidenceDecision required ledger := by
  unfold evidenceDecision
  rw [ContextProjection.unrelated_revision_does_not_change_projection
      required other different ledger verdict]

/-- The disconnected implementation matches one ordinary run but fails the
intervention that supplies the required successful evidence. -/
theorem matching_one_report_does_not_establish_mediation :
    evidenceDecision 0 [] = false ∧
      evidenceDecision 0 [⟨0, true⟩] ≠ false := by
  decide

/-- The source-faithful coding-loop model permits an unverified final answer.
Its correlated-feedback properties do not supply task acceptance. -/
theorem coding_loop_completion_is_not_evidence_acceptance :
    ∃ state : CodingAgent.State, state.phase = .done 7 ∧
      ¬ state.history.any CodingAgent.isToolEvidence :=
  CodingAgent.unverified_answer_is_reachable

private def profile : EmbeddingProfile := ⟨1, 2, 3, 1024, true, .cosine, 4⟩
private def current : Capture := ⟨5, 6, 7, profile⟩

#guard observation current ⟨current, [], .candidates⟩ == .unavailable
#guard observation current ⟨current, [], .exhaustive⟩ == .absent
#guard refresh (some [9]) current ⟨current, [], .candidates⟩ == some [9]
#guard refresh (some [9]) current ⟨{ current with sourceRevision := 8 }, [], .exhaustive⟩ == some [9]
#guard observation current ⟨{ current with request := 8 }, [9], .exhaustive⟩ == .unavailable
#guard observation current ⟨{ current with profile := { profile with modelRevision := 8 } }, [9], .exhaustive⟩ == .unavailable
#guard observation current ⟨{ current with profile := { profile with inputPreparation := 8 } }, [9], .exhaustive⟩ == .unavailable
#guard observation current ⟨{ current with scope := 8 }, [], .exhaustive⟩ == .unavailable
#guard evidenceDecision 0 [⟨1, true⟩] == false
#guard evidenceDecision 0 [⟨0, false⟩, ⟨0, true⟩] == true
#guard (readout (some [9]) current ⟨current, [], .candidates⟩).decisionRows == none
#guard (readout (some [9]) current ⟨{ current with sourceRevision := 8 }, [10], .exhaustive⟩).contextRows == some [9]
#guard (readout (some [9]) current ⟨{ current with sourceRevision := 8 }, [10], .exhaustive⟩).decisionRows == none

end MemoryRetrievalBoundary
