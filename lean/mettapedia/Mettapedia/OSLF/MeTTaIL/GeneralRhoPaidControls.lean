import Mettapedia.OSLF.MeTTaIL.GeneralRhoFrontierControls
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrencePaidReadouts

/-!
# Paid evidence from original rho communication occurrences

The actual general executor emits the original COMM targets and ordered bag
origins. List selection uses bounds obtained from its checked readouts. Paid
delivery and inspection then retain those occurrences and their primitive
histories. A paused matcher and an underfunded inspection produce no verdict.

These runs discover occurrences before saturation; their paid answers do not
assert that the full frontier is complete. The two duplicate bag occurrences
have equal targets and remain distinct in native and funded receipt families.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho.PaidControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Causality
open GeneralOccurrencePaidReadouts

def source (duplicate : Bool) : Pattern :=
  if duplicate then FrontierControls.duplicates else FrontierControls.rootSource

def target (duplicate : Bool) : Pattern :=
  if duplicate then FrontierControls.duplicateTarget else FrontierControls.rootTarget

def fuel (duplicate : Bool) : Nat := if duplicate then 75 else 40
def count (duplicate : Bool) : Nat := if duplicate then 2 else 1

def request (duplicate : Bool) : GeneralOccurrenceFrontier.Request :=
  FrontierControls.actualRequest (source duplicate)

def discovered (duplicate : Bool) : GeneralOccurrenceFrontier.State (request duplicate) :=
  GeneralOccurrenceFrontier.run (request duplicate) (fuel duplicate)
    (GeneralOccurrenceFrontier.start (request duplicate))

def expectedReadouts (duplicate : Bool) : List FrontierControls.Readout :=
  if duplicate then
    [⟨0, [], [], firstInputTrace, some FrontierControls.receivedBody, target true⟩,
     ⟨0, [], [], secondInputTrace, some FrontierControls.receivedBody, target true⟩]
  else [⟨0, [], [], commTrace, some FrontierControls.receivedBody, target false⟩]

theorem actual_readouts (duplicate : Bool) :
    (discovered duplicate).answers.map (fun answer => FrontierControls.rawReadout answer.val) =
      expectedReadouts duplicate := by
  cases duplicate
  · change (GeneralOccurrenceFrontier.run
      (FrontierControls.actualRequest FrontierControls.rootSource) 40
      (GeneralOccurrenceFrontier.start (FrontierControls.actualRequest FrontierControls.rootSource))).answers.map
        (fun answer => FrontierControls.rawReadout answer.val) =
        [⟨0, [], [], commTrace, some FrontierControls.receivedBody, FrontierControls.rootTarget⟩]
    simpa only [FrontierControls.readouts, List.map_map, Function.comp_def]
      using FrontierControls.actual_received_drop
  · change (GeneralOccurrenceFrontier.run
      (FrontierControls.actualRequest FrontierControls.duplicates) 75
      (GeneralOccurrenceFrontier.start (FrontierControls.actualRequest FrontierControls.duplicates))).answers.map
        (fun answer => FrontierControls.rawReadout answer.val) =
        [⟨0, [], [], firstInputTrace, some FrontierControls.receivedBody, FrontierControls.duplicateTarget⟩,
         ⟨0, [], [], secondInputTrace, some FrontierControls.receivedBody, FrontierControls.duplicateTarget⟩]
    simpa only [FrontierControls.readouts, List.map_map, Function.comp_def]
      using FrontierControls.actual_duplicate_bag_origins

theorem answers_length (duplicate : Bool) : (discovered duplicate).answers.length = count duplicate := by
  have lengths := congrArg List.length (actual_readouts duplicate)
  cases duplicate <;>
    simpa only [List.length_map, expectedReadouts, count, Bool.false_eq_true,
      if_false, if_true, List.length_cons, List.length_nil] using lengths

def occurrence (duplicate : Bool) (slot : Fin (count duplicate)) :
    GeneralOccurrenceFrontier.Answer (request duplicate) :=
  (discovered duplicate).answers[slot.val]'(by rw [answers_length]; exact slot.isLt)

theorem occurrence_found (duplicate : Bool) (slot : Fin (count duplicate)) :
    (discovered duplicate).answers[slot.val]? = some (occurrence duplicate slot) :=
  List.getElem?_eq_getElem (by rw [answers_length]; exact slot.isLt)

theorem actual_targets (duplicate : Bool) :
    (discovered duplicate).answers.map (fun answer => answer.val.target) =
      List.replicate (count duplicate) (target duplicate) := by
  have targets := congrArg (List.map FrontierControls.Readout.target) (actual_readouts duplicate)
  cases duplicate <;>
    simpa only [List.map_map, Function.comp_def, FrontierControls.rawReadout,
      expectedReadouts, count, Bool.false_eq_true, if_false, if_true,
      List.map_cons, List.map_nil, List.replicate_succ, List.replicate_zero] using targets

theorem occurrence_target (duplicate : Bool) (slot : Fin (count duplicate)) :
    (occurrence duplicate slot).val.target = target duplicate := by
  have targets := congrArg (fun values => values[slot.val]?) (actual_targets duplicate)
  simp only [List.getElem?_map, occurrence_found, Option.map_some,
    List.getElem?_replicate_of_lt slot.isLt] at targets
  exact Option.some.inj targets

def protocol (duplicate : Bool) : Protocol where
  test := fun _ value => decide (value = target duplicate)
  deliveryCost := fun _ _ => 2
  inspectionCost := fun _ _ => 3

theorem target_test (duplicate : Bool) (slot : Fin (count duplicate)) :
    (protocol duplicate).test 0 (occurrence duplicate slot).val.target = true := by
  rw [occurrence_target]
  simp only [protocol, decide_true]

def round (duplicate : Bool) (slot : Fin (count duplicate)) (budget : Nat) :=
  paidRound (request duplicate) (discovered duplicate) (protocol duplicate)
    slot.val 0 23 5 29 budget

theorem actual_offer (duplicate : Bool) (slot : Fin (count duplicate)) :
    (offer (request duplicate) (discovered duplicate) slot.val 0 23 5 29).arrival =
      some (target duplicate) := by
  rw [emitted_offer _ _ _ _ _ _ _ (occurrence duplicate slot)
    (occurrence_found duplicate slot), occurrence_target]

def paid (duplicate : Bool) (slot : Fin (count duplicate)) :
    PaidFiring (request duplicate) (discovered duplicate) (protocol duplicate) 0 23 5 29 true :=
  let executed := completedFiring (request duplicate) (discovered duplicate)
    (protocol duplicate) slot.val 0 23 5 29 5 (occurrence duplicate slot)
    (occurrence_found duplicate slot) (by change 2 + 3 ≤ 5; decide)
  { slot := executed.slot
    occurrence := executed.occurrence
    emitted := executed.emitted
    budget := executed.budget
    assay :=
      { round := executed.assay.round
        response := executed.assay.response
        authenticated := executed.assay.authenticated
        readout := executed.assay.readout.trans (target_test duplicate slot) } }

theorem paid_retains_occurrence (duplicate : Bool) (slot : Fin (count duplicate)) :
    (paid duplicate slot).occurrence = occurrence duplicate slot := rfl

theorem paid_actual_round (duplicate : Bool) (slot : Fin (count duplicate)) :
    (paid duplicate slot).assay.round = round duplicate slot 5 := rfl

theorem current_target_native_certificate (duplicate : Bool) (slot : Fin (count duplicate)) :
    (protocol duplicate).test 0 (paid duplicate slot).native.1.val.target = true :=
  (paid duplicate slot).native.2.down

theorem original_comm_target (duplicate : Bool) (slot : Fin (count duplicate)) :
    (paid duplicate slot).native.1.val.target = target duplicate :=
  occurrence_target duplicate slot

theorem actual_primitive_history (duplicate : Bool) (slot : Fin (count duplicate)) :
    (GeneralOccurrenceNativeReceipts.history (request duplicate).plan (request duplicate).bound
      (request duplicate).expected (paid duplicate slot).occurrence).length = 1 :=
  (paid duplicate slot).primitive_count

theorem completed_answer (duplicate : Bool) (slot : Fin (count duplicate)) :
    (paid duplicate slot).assay.round.responses =
      {(23, ComplementaryAssay.verdictOf true, 29, target duplicate)} := by
  change (round duplicate slot 5).responses = _
  have response := paid_responses (request duplicate) (discovered duplicate)
    (protocol duplicate) slot.val 0 23 5 29 5 (occurrence duplicate slot)
    (occurrence_found duplicate slot)
  rw [if_pos (by change 2 + 3 ≤ 5; decide), target_test, occurrence_target] at response
  exact response

theorem exact_spend_and_balance (duplicate : Bool) (slot : Fin (count duplicate)) :
    (paid duplicate slot).assay.round.spent = 5 ∧
      (paid duplicate slot).assay.round.remaining = 0 := by
  have spent := (paid duplicate slot).exact_charge
  have ledger := (paid duplicate slot).exact_ledger
  change (paid duplicate slot).assay.round.spent = 2 + 3 at spent
  change 5 = (paid duplicate slot).assay.round.remaining +
    (paid duplicate slot).assay.round.spent at ledger
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

theorem actual_delivery_and_inspection (duplicate : Bool) (slot : Fin (count duplicate)) :
    ((AssayProbeDelivery.paid ((protocol duplicate).test 0)
      ((protocol duplicate).deliveryCost 0) ((protocol duplicate).inspectionCost 0)).pathEntries
      (paid duplicate slot).assay.round.path).length = 2 :=
  authenticated_path_has_two_events (protocol duplicate) _ 5 (target duplicate)
    (actual_offer duplicate slot) (paid duplicate slot).assay.round
    (paid duplicate slot).assay.response (paid duplicate slot).assay.authenticated

theorem one_below_price_silent (duplicate : Bool) (slot : Fin (count duplicate)) :
    (round duplicate slot 4).responses = 0 :=
  underfunded_silent _ _ _ _ _ _ _ _ _ (occurrence duplicate slot)
    (occurrence_found duplicate slot) (by change 4 < 2 + 3; decide)

private theorem underfunded_delivery_account (duplicate : Bool)
    (offered : ProbeCampaign.Request Nat Pattern Nat Nat)
    (arrived : offered.arrival = some (target duplicate)) :
    (ProbeCampaign.completedRound (protocol duplicate) offered 4).spent = 2 ∧
      (ProbeCampaign.completedRound (protocol duplicate) offered 4).remaining = 2 ∧
      ((AssayProbeDelivery.paid ((protocol duplicate).test offered.question)
        ((protocol duplicate).deliveryCost offered.question)
        ((protocol duplicate).inspectionCost offered.question)).pathEntries
        (ProbeCampaign.completedRound (protocol duplicate) offered 4).path).length = 1 := by
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

theorem one_below_price_delivery_only (duplicate : Bool) (slot : Fin (count duplicate)) :
    (round duplicate slot 4).spent = 2 ∧ (round duplicate slot 4).remaining = 2 ∧
      ((AssayProbeDelivery.paid ((protocol duplicate).test 0)
        ((protocol duplicate).deliveryCost 0) ((protocol duplicate).inspectionCost 0)).pathEntries
        (round duplicate slot 4).path).length = 1 :=
  underfunded_delivery_account duplicate _ (actual_offer duplicate slot)

def prediction (hypothesis : Bool) (_question : Nat) : Bool := hypothesis
def candidates : Finset Bool := {false, true}

theorem one_below_price_keeps_candidates (duplicate : Bool) (slot : Fin (count duplicate)) :
    Mettapedia.OSLF.Framework.FiniteAssayLearner.revise prediction candidates 0
      (round duplicate slot 4).responses = candidates :=
  underfunded_no_elimination _ _ _ _ _ _ _ _ _ (occurrence duplicate slot)
    (occurrence_found duplicate slot) (by change 4 < 2 + 3; decide) prediction candidates

def paused : GeneralOccurrenceFrontier.State (request false) :=
  GeneralOccurrenceFrontier.run (request false) 5 (GeneralOccurrenceFrontier.start (request false))

theorem paused_answers : paused.answers = [] := by
  have readout := FrontierControls.pause_inside_actual_matching.1
  change (paused.answers.map Subtype.val).map FrontierControls.rawReadout = [] at readout
  exact List.map_eq_nil_iff.mp (List.map_eq_nil_iff.mp readout)

theorem paused_matcher : FrontierControls.matcherPending (request false) 5 = true :=
  FrontierControls.pause_inside_actual_matching.2

theorem paused_paid_silent :
    (paidRound (request false) paused (protocol false) 0 0 23 5 29 5).responses = 0 :=
  empty_search_silent _ _ _ _ _ _ _ _ _ paused_answers

theorem paused_keeps_candidates :
    Mettapedia.OSLF.Framework.FiniteAssayLearner.revise prediction candidates 0
      (paidRound (request false) paused (protocol false) 0 0 23 5 29 5).responses = candidates :=
  incomplete_empty_no_elimination _ _ _ _ _ _ _ _ _ paused_answers prediction candidates

theorem whole_state_resume :
    GeneralOccurrenceFrontier.run (request false) 35 paused = discovered false :=
  (GeneralOccurrenceFrontier.run_add _ 5 35 _).symm

theorem duplicate_traces :
    (occurrence true ⟨0, by decide⟩).val.firing.matcherTrace = firstInputTrace ∧
      (occurrence true ⟨1, by decide⟩).val.firing.matcherTrace = secondInputTrace := by
  have first := congrArg (fun values => values[0]?) (actual_readouts true)
  have second := congrArg (fun values => values[1]?) (actual_readouts true)
  simp only [List.getElem?_map, expectedReadouts, if_true, List.getElem?_cons_zero,
    List.getElem?_cons_succ] at first second
  rw [occurrence_found true ⟨0, by decide⟩, Option.map_some] at first
  rw [occurrence_found true ⟨1, by decide⟩, Option.map_some] at second
  exact ⟨congrArg FrontierControls.Readout.matcherTrace (Option.some.inj first),
    congrArg FrontierControls.Readout.matcherTrace (Option.some.inj second)⟩

theorem distinct_duplicate_occurrences :
    occurrence true ⟨0, by decide⟩ ≠ occurrence true ⟨1, by decide⟩ := by
  intro same
  have traces := congrArg (fun answer : GeneralOccurrenceFrontier.Answer (request true) =>
    answer.val.firing.matcherTrace) same
  rw [duplicate_traces.1, duplicate_traces.2] at traces
  have different : firstInputTrace ≠ secondInputTrace := by decide
  exact different traces

theorem duplicate_equal_targets :
    (paid true ⟨0, by decide⟩).native.1.val.target =
      (paid true ⟨1, by decide⟩).native.1.val.target :=
  (original_comm_target true _).trans (original_comm_target true _).symm

theorem duplicate_distinct_native_origins :
    (paid true ⟨0, by decide⟩).native ≠ (paid true ⟨1, by decide⟩).native := by
  intro same
  exact distinct_duplicate_occurrences (congrArg Sigma.fst same)

theorem duplicate_distinct_funded_origins :
    introduceFunded (paid true ⟨0, by decide⟩) 5 (by decide) ≠
      introduceFunded (paid true ⟨1, by decide⟩) 5 (by decide) :=
  equal_answers_distinct_origins _ _ distinct_duplicate_occurrences 5 (by decide) (by decide)

end Mettapedia.OSLF.MeTTaIL.GeneralRho.PaidControls
