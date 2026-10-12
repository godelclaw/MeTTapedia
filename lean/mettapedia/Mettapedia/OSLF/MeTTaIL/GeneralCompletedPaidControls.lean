import Mettapedia.OSLF.MeTTaIL.GeneralCompletedFrontierControls
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrencePaidReadouts

/-!
# Paid native evidence from a completed authored frontier

The two retained authored occurrences have the same target and distinct
declaration origins. Each actual occurrence is offered to a paid delivery and
inspection protocol. The endpoint supplies the learner's answer while the
complete paid receipt retains the occurrence, conversion witnesses and paid
path. Its native readout keeps the occurrence and current-target certificate.

Delivery costs two units and inspection costs three. A five-unit purse
is consumed by a completed verdict. Four units deliver the target but do
not fund inspection, so the silent result leaves both hypotheses standing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralCompletedPaidControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Causality
open GeneralCompletedFrontierControls (done completed request)
open GeneralOccurrencePaidReadouts

def matchesOccurrence (slot : Fin 2)
    (answer : GeneralOccurrenceFrontier.Answer (request true)) : Bool :=
  decide (answer.val.firing.job.declaration.declarationIndex = slot.val ∧
    answer.val.target = done)

def occurrenceIndex (slot : Fin 2) : Nat :=
  (completed true).answers.findIdx (matchesOccurrence slot)

theorem occurrenceIndex_lt (slot : Fin 2) :
    occurrenceIndex slot < (completed true).answers.length := by
  apply List.findIdx_lt_length_of_exists
  obtain ⟨answer, member, origin, target⟩ :=
    GeneralCompletedFrontierControls.completed_occurrence_exists slot
  exact ⟨answer, member, by simp only [matchesOccurrence, decide_eq_true_eq]; exact ⟨origin, target⟩⟩

def occurrence (slot : Fin 2) : GeneralOccurrenceFrontier.Answer (request true) :=
  (completed true).answers[occurrenceIndex slot]'(occurrenceIndex_lt slot)

theorem occurrence_found (slot : Fin 2) :
    (completed true).answers[occurrenceIndex slot]? = some (occurrence slot) :=
  List.getElem?_eq_getElem (occurrenceIndex_lt slot)

theorem occurrence_readouts (slot : Fin 2) :
    (occurrence slot).val.firing.job.declaration.declarationIndex = slot.val ∧
      (occurrence slot).val.target = done := by
  have found : matchesOccurrence slot (occurrence slot) = true :=
    List.findIdx_getElem (w := occurrenceIndex_lt slot)
  exact of_decide_eq_true found

theorem occurrence_target (slot : Fin 2) : (occurrence slot).val.target = done :=
  (occurrence_readouts slot).2

theorem occurrence_origin (slot : Fin 2) :
    (occurrence slot).val.firing.job.declaration.declarationIndex = slot.val :=
  (occurrence_readouts slot).1

theorem distinct_occurrences : occurrence ⟨0, by decide⟩ ≠ occurrence ⟨1, by decide⟩ := by
  intro same
  have origins := congrArg (fun answer : GeneralOccurrenceFrontier.Answer (request true) =>
    answer.val.firing.job.declaration.declarationIndex) same
  rw [occurrence_origin, occurrence_origin] at origins
  cases origins

def protocol : Protocol where
  test := fun _ target => decide (target = done)
  deliveryCost := fun _ _ => 2
  inspectionCost := fun _ _ => 3

theorem completed_target_test (slot : Fin 2) :
    protocol.test 0 (occurrence slot).val.target = true := by
  rw [occurrence_target]
  simp [protocol]

def round (slot : Fin 2) (budget : Nat) :=
  paidRound (request true) (completed true) protocol (occurrenceIndex slot) 0 17 3 19 budget

theorem actual_offer (slot : Fin 2) :
    (offer (request true) (completed true) (occurrenceIndex slot) 0 17 3 19).arrival = some done := by
  rw [emitted_offer _ _ _ _ _ _ _ (occurrence slot) (occurrence_found slot),
    occurrence_target]

/-- The record is built from the completed paid execution; only its Boolean
index is rewritten to the proved answer. -/
def paid (slot : Fin 2) :
    PaidFiring (request true) (completed true) protocol 0 17 3 19 true :=
  let executed := completedFiring (request true) (completed true) protocol (occurrenceIndex slot)
    0 17 3 19 5 (occurrence slot) (occurrence_found slot) (by change 2 + 3 ≤ 5; decide)
  { slot := executed.slot
    occurrence := executed.occurrence
    emitted := executed.emitted
    budget := executed.budget
    assay :=
      { round := executed.assay.round
        response := executed.assay.response
        authenticated := executed.assay.authenticated
        readout := executed.assay.readout.trans (completed_target_test slot) } }

theorem paid_retains_occurrence (slot : Fin 2) : (paid slot).occurrence = occurrence slot := rfl

theorem paid_actual_round (slot : Fin 2) : (paid slot).assay.round = round slot 5 := rfl

theorem completed_answer (slot : Fin 2) :
    (paid slot).assay.round.responses = {(17, ComplementaryAssay.verdictOf true, 19, done)} := by
  change (round slot 5).responses = _
  have response := paid_responses (request true) (completed true) protocol (occurrenceIndex slot)
    0 17 3 19 5 (occurrence slot) (occurrence_found slot)
  rw [if_pos (by change 2 + 3 ≤ 5; decide), completed_target_test, occurrence_target] at response
  exact response

theorem exact_spend_and_balance (slot : Fin 2) :
    (paid slot).assay.round.spent = 5 ∧ (paid slot).assay.round.remaining = 0 := by
  have spent := (paid slot).exact_charge
  have ledger := (paid slot).exact_ledger
  change (paid slot).assay.round.spent = 2 + 3 at spent
  change 5 = (paid slot).assay.round.remaining + (paid slot).assay.round.spent at ledger
  exact ⟨spent, by omega⟩

private theorem authenticated_path_has_two_events (protocol : Protocol)
    (offered : ProbeCampaign.Request Nat Pattern Nat Nat) (budget : Nat)
    (value : Pattern) (arrived : offered.arrival = some value)
    (round : ProbeCampaign.Round protocol offered budget)
    (response : ProbeCampaign.Response Pattern Nat) (authenticated : response ∈ round.responses) :
    ((AssayProbeDelivery.paid (protocol.test offered.question)
      (protocol.deliveryCost offered.question) (protocol.inspectionCost offered.question)).pathEntries
      round.path).length = 2 := by
  cases offered with
  | mk question session provider client arrival =>
    cases arrival with
    | none => cases arrived
    | some supplied =>
      have same := Option.some.inj arrived
      subst supplied
      rcases AssayProbeDelivery.offered_path_cases (protocol.test question)
        (protocol.deliveryCost question) (protocol.inspectionCost question)
        session provider client value budget round.path with
        ⟨endpoint, _⟩ | ⟨endpoint, _, _⟩ | ⟨_, entries, _⟩
      · have quiet : round.responses = 0 := by
          simp only [ProbeCampaign.Round.responses, endpoint,
            AssayProbeDelivery.paidOffered, ResourceInteraction.leftPart_marking,
            AssayProbeDelivery.outputs_offered]
        simp only [quiet, Multiset.notMem_zero] at authenticated
      · have quiet : round.responses = 0 := by
          simp only [ProbeCampaign.Round.responses, endpoint,
            AssayProbeDelivery.paidReceived, ResourceInteraction.leftPart_marking,
            AssayProbeDelivery.outputs_received]
        simp only [quiet, Multiset.notMem_zero] at authenticated
      · exact entries

theorem actual_delivery_and_inspection (slot : Fin 2) :
    ((AssayProbeDelivery.paid (protocol.test 0)
      (protocol.deliveryCost 0) (protocol.inspectionCost 0)).pathEntries
      (paid slot).assay.round.path).length = 2 :=
  authenticated_path_has_two_events protocol _ 5 done (actual_offer slot)
    (paid slot).assay.round (paid slot).assay.response (paid slot).assay.authenticated

theorem current_target_native_certificate (slot : Fin 2) :
    protocol.test 0 (paid slot).native.1.val.target = true :=
  (paid slot).native.2.down

theorem completed_description (slot : Fin 2) :
    Mettapedia.OSLF.Framework.PaidInterventionalDescriptions.Round.answer
      (paid slot).assay.round = some true :=
  (Mettapedia.OSLF.Framework.PaidInterventionalDescriptions.Round.answer_some
    (paid slot).assay.round true).mpr
    ⟨(paid slot).assay.response, (paid slot).assay.authenticated, (paid slot).assay.readout⟩

theorem paid_semantic_step (slot : Fin 2) :
    (GeneralOccurrenceSemantics.gslt (request true).plan (request true).bound
      (request true).expected).Step (request true).root done := by
  have step := (paid slot).semantic_step
  simpa only [paid_retains_occurrence, occurrence_target] using step

theorem native_retains_actual_occurrence (slot : Fin 2) :
    (paid slot).native.1 = occurrence slot := rfl

theorem actual_primitive_history (slot : Fin 2) :
    (GeneralOccurrenceNativeReceipts.history (request true).plan (request true).bound
      (request true).expected (paid slot).occurrence).length = 1 :=
  (paid slot).primitive_count

theorem separate_work_and_payment (slot : Fin 2) :
    (paid slot).searchWork = (completed true).work ∧
      (paid slot).administrativeCount = (occurrence slot).val.conversions.length ∧
      (paid slot).assay.round.spent = 5 :=
  ⟨rfl, rfl, (exact_spend_and_balance slot).1⟩

theorem one_below_price_silent (slot : Fin 2) : (round slot 4).responses = 0 :=
  underfunded_silent _ _ _ _ _ _ _ _ _ (occurrence slot) (occurrence_found slot)
    (by change 4 < 2 + 3; decide)

private theorem underfunded_delivery_account (offered : ProbeCampaign.Request Nat Pattern Nat Nat)
    (arrived : offered.arrival = some done) :
    (ProbeCampaign.completedRound protocol offered 4).spent = 2 ∧
      (ProbeCampaign.completedRound protocol offered 4).remaining = 2 ∧
      ((AssayProbeDelivery.paid (protocol.test offered.question)
        (protocol.deliveryCost offered.question) (protocol.inspectionCost offered.question)).pathEntries
        (ProbeCampaign.completedRound protocol offered 4).path).length = 1 := by
  cases offered with
  | mk question session provider client arrival =>
    cases arrival with
    | none => cases arrived
    | some supplied =>
      have same := Option.some.inj arrived
      subst supplied
      refine ⟨?_, ?_, ?_⟩
      · change (ComplementaryAssay.purse 2 + 0).card = 2
        simp only [add_zero, ComplementaryAssay.purse, Multiset.card_replicate]
      · change (ComplementaryAssay.purse 2).card = 2
        simp only [ComplementaryAssay.purse, Multiset.card_replicate]
      · rfl

theorem one_below_price_delivery_only (slot : Fin 2) :
    (round slot 4).spent = 2 ∧ (round slot 4).remaining = 2 ∧
      ((AssayProbeDelivery.paid (protocol.test 0)
        (protocol.deliveryCost 0) (protocol.inspectionCost 0)).pathEntries
        (round slot 4).path).length = 1 :=
  underfunded_delivery_account _ (actual_offer slot)

theorem one_below_price_no_description (slot : Fin 2) :
    Mettapedia.OSLF.Framework.PaidInterventionalDescriptions.Round.answer
      (round slot 4) = none :=
  (Mettapedia.OSLF.Framework.PaidInterventionalDescriptions.Round.answer_none
    (round slot 4)).mpr (one_below_price_silent slot)

def prediction (hypothesis : Bool) (_question : Nat) : Bool := hypothesis

def candidates : Finset Bool := {false, true}

theorem one_below_price_keeps_candidates (slot : Fin 2) :
    Mettapedia.OSLF.Framework.FiniteAssayLearner.revise prediction candidates 0
      (round slot 4).responses = candidates := by
  rw [one_below_price_silent]
  exact Mettapedia.OSLF.Framework.FiniteAssayLearner.silence_preserves _ _ _

theorem genuine_refutation (slot : Fin 2) :
    false ∉ Mettapedia.OSLF.Framework.FiniteAssayLearner.revise prediction candidates 0
      (paid slot).assay.round.responses :=
  genuine_refutation_removes (paid slot) prediction candidates false (by decide)

theorem correct_hypothesis_retained (slot : Fin 2) :
    true ∈ Mettapedia.OSLF.Framework.FiniteAssayLearner.revise prediction candidates 0
      (paid slot).assay.round.responses :=
  correct_hypothesis_survives (paid slot) prediction candidates true
    (by simp [candidates]) rfl

theorem equal_answer_distinct_paid_origins :
    paid ⟨0, by decide⟩ ≠ paid ⟨1, by decide⟩ := by
  intro same
  exact distinct_occurrences (congrArg PaidFiring.occurrence same)

theorem equal_answer_distinct_native_origins :
    (paid ⟨0, by decide⟩).native ≠ (paid ⟨1, by decide⟩).native := by
  intro same
  exact distinct_occurrences (congrArg Sigma.fst same)

theorem equal_answer_distinct_funded_origins :
    introduceFunded (paid ⟨0, by decide⟩) 5 (by decide) ≠
      introduceFunded (paid ⟨1, by decide⟩) 5 (by decide) :=
  equal_answers_distinct_origins _ _ distinct_occurrences 5 (by decide) (by decide)

end Mettapedia.OSLF.MeTTaIL.GeneralCompletedPaidControls
