import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceModalReadouts
import Mettapedia.OSLF.Framework.PaidInterventionalNativeEvidence

/-!
# Paid delivery of emitted typed occurrence evidence

An actual frontier receipt supplies the offered target. The existing paid
delivery and inspection protocol executes that offer and reads the resulting
response. A native fibre retains the complete operational occurrence and paid
path. Unfinished empty searches and underfunded inspections remain silent.

Search work, equation administration, primitive events and payment each keep
their own account; a supplied price schedule does not equate these measures.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrencePaidReadouts

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralOccurrenceFrontier
open Mettapedia.GSLT.Causality

abbrev Protocol := ProbeCampaign.Protocol Nat Pattern

def offer (request : GeneralOccurrenceFrontier.Request) (state : State request)
    (slot question session provider client : Nat) : ProbeCampaign.Request Nat Pattern Nat Nat where
  question := question
  session := session
  provider := provider
  client := client
  arrival := (state.answers[slot]?).map fun answer => answer.val.target

def paidRound (request : GeneralOccurrenceFrontier.Request) (state : State request)
    (protocol : Protocol) (slot question session provider client budget : Nat) :
    ProbeCampaign.Round protocol (offer request state slot question session provider client) budget :=
  ProbeCampaign.completedRound protocol (offer request state slot question session provider client) budget

theorem empty_offer (request : GeneralOccurrenceFrontier.Request) (state : State request)
    (slot question session provider client : Nat) (empty : state.answers = []) :
    (offer request state slot question session provider client).arrival = none := by
  simp only [offer, empty, List.getElem?_nil, Option.map_none]

theorem missing_offer (request : GeneralOccurrenceFrontier.Request) (state : State request)
    (slot question session provider client : Nat) (missing : state.answers[slot]? = none) :
    (offer request state slot question session provider client).arrival = none := by
  simp only [offer, missing, Option.map_none]

theorem emitted_offer (request : GeneralOccurrenceFrontier.Request) (state : State request)
    (slot question session provider client : Nat) (answer : Answer request)
    (found : state.answers[slot]? = some answer) :
    (offer request state slot question session provider client).arrival = some answer.val.target := by
  simp only [offer, found, Option.map_some]

theorem empty_search_silent (request : GeneralOccurrenceFrontier.Request) (state : State request)
    (protocol : Protocol) (slot question session provider client budget : Nat) (empty : state.answers = []) :
    (paidRound request state protocol slot question session provider client budget).responses = 0 :=
  ProbeCampaign.Round.absent_is_quiet _ (empty_offer request state slot question session provider client empty)

theorem paid_responses (request : GeneralOccurrenceFrontier.Request) (state : State request)
    (protocol : Protocol) (slot question session provider client budget : Nat)
    (answer : Answer request) (found : state.answers[slot]? = some answer) :
    (paidRound request state protocol slot question session provider client budget).responses =
      if protocol.deliveryCost question answer.val.target + protocol.inspectionCost question answer.val.target ≤ budget then
        {(session, ComplementaryAssay.verdictOf (protocol.test question answer.val.target), client, answer.val.target)}
      else 0 := by
  unfold paidRound
  rw [ProbeCampaign.completedRound_responses]
  have offered := emitted_offer request state slot question session provider client answer found
  change AssayProbeDelivery.observed _ _ _ _ _ _ _ _ = _
  rw [offered]
  exact AssayProbeDelivery.observed_some _ _ _ _ _ _ _ _

theorem underfunded_silent (request : GeneralOccurrenceFrontier.Request) (state : State request)
    (protocol : Protocol) (slot question session provider client budget : Nat)
    (answer : Answer request) (found : state.answers[slot]? = some answer)
    (underfunded : budget < protocol.deliveryCost question answer.val.target + protocol.inspectionCost question answer.val.target) :
    (paidRound request state protocol slot question session provider client budget).responses = 0 := by
  rw [paid_responses request state protocol slot question session provider client budget answer found,
    if_neg (by omega)]

structure PaidFiring (request : GeneralOccurrenceFrontier.Request) (state : State request)
    (protocol : Protocol) (question session provider client : Nat) (bit : Bool) where
  slot : Nat
  occurrence : Answer request
  emitted : state.answers[slot]? = some occurrence
  budget : Nat
  assay : Mettapedia.OSLF.Framework.PaidInterventionalDescriptions.CompletedReceipt protocol
    (offer request state slot question session provider client) budget bit

namespace PaidFiring

variable {request : GeneralOccurrenceFrontier.Request} {state : State request} {protocol : Protocol}
variable {question session provider client : Nat} {bit : Bool}

theorem target_certificate (receipt : PaidFiring request state protocol question session provider client bit) :
    protocol.test question receipt.occurrence.val.target = bit := by
  obtain ⟨target, offered, response, _, _, _⟩ :=
    receipt.assay.round.response_sound receipt.assay.response receipt.assay.authenticated
  have actual := emitted_offer request state receipt.slot question session provider client receipt.occurrence receipt.emitted
  have sameTarget := Option.some.inj (actual.symm.trans offered)
  have testReadout := receipt.assay.readout
  rw [response] at testReadout
  simp only [ComplementaryAssay.verdictOf_bit] at testReadout
  simpa only [← sameTarget, offer] using testReadout

def native (receipt : PaidFiring request state protocol question session provider client bit) :
    GeneralOccurrenceNativeReceipts.NativeFamily request.plan request.bound request.expected
      (fun target => PLift (protocol.test question target = bit)) request.root :=
  ⟨receipt.occurrence, ⟨receipt.target_certificate⟩⟩

theorem native_retains_origin (receipt : PaidFiring request state protocol question session provider client bit) :
    receipt.native.1 = receipt.occurrence := rfl

theorem semantic_step (receipt : PaidFiring request state protocol question session provider client bit) :
    (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step
      request.root receipt.occurrence.val.target := emitted_step request receipt.occurrence

theorem exact_ledger (receipt : PaidFiring request state protocol question session provider client bit) :
    receipt.budget = receipt.assay.round.remaining + receipt.assay.round.spent := receipt.assay.round.ledger

theorem exact_charge (receipt : PaidFiring request state protocol question session provider client bit) :
    receipt.assay.round.spent = protocol.deliveryCost question receipt.occurrence.val.target +
      protocol.inspectionCost question receipt.occurrence.val.target := by
  obtain ⟨target, offered, _, _, _, spent⟩ :=
    receipt.assay.round.response_sound receipt.assay.response receipt.assay.authenticated
  have actual := emitted_offer request state receipt.slot question session provider client receipt.occurrence receipt.emitted
  have sameTarget := Option.some.inj (actual.symm.trans offered)
  simpa only [← sameTarget, offer] using spent

def administrativeCount (receipt : PaidFiring request state protocol question session provider client bit) : Nat :=
  receipt.occurrence.val.conversions.length

def searchWork (_receipt : PaidFiring request state protocol question session provider client bit) : Nat := state.work

theorem primitive_count (receipt : PaidFiring request state protocol question session provider client bit) :
    (GeneralOccurrenceNativeReceipts.history request.plan request.bound request.expected receipt.occurrence).length = 1 :=
  GeneralOccurrenceNativeReceipts.primitive_count _ _ _ _

end PaidFiring

def fundedFamily (request : GeneralOccurrenceFrontier.Request) (state : State request)
    (protocol : Protocol) (question session provider client : Nat) :=
  Mettapedia.OSLF.Framework.PaidInterventionalNativeEvidence.fundedFamily
    (PaidFiring request state protocol question session provider client) (fun _ receipt => receipt.budget)

def introduceFunded {request : GeneralOccurrenceFrontier.Request} {state : State request}
    {protocol : Protocol} {question session provider client : Nat} {bit : Bool}
    (receipt : PaidFiring request state protocol question session provider client bit)
    (allowance : Nat) (funded : receipt.budget ≤ allowance) :=
  Mettapedia.OSLF.Framework.PaidInterventionalNativeEvidence.introduce
    (PaidFiring request state protocol question session provider client) (fun _ receipt => receipt.budget)
    allowance bit receipt funded

theorem funded_receipt_injective {request : GeneralOccurrenceFrontier.Request} {state : State request}
    {protocol : Protocol} {question session provider client : Nat} {bit : Bool}
    (first second : PaidFiring request state protocol question session provider client bit)
    (allowance : Nat) (firstFunded : first.budget ≤ allowance) (secondFunded : second.budget ≤ allowance)
    (same : introduceFunded first allowance firstFunded = introduceFunded second allowance secondFunded) : first = second :=
  Mettapedia.OSLF.Framework.PaidInterventionalNativeEvidence.introduce_injective _ _ _ _ _ _ _ _ same

theorem equal_answers_distinct_origins {request : GeneralOccurrenceFrontier.Request} {state : State request}
    {protocol : Protocol} {question session provider client : Nat} {bit : Bool}
    (first second : PaidFiring request state protocol question session provider client bit)
    (different : first.occurrence ≠ second.occurrence)
    (allowance : Nat) (firstFunded : first.budget ≤ allowance) (secondFunded : second.budget ≤ allowance) :
    introduceFunded first allowance firstFunded ≠ introduceFunded second allowance secondFunded := by
  intro same
  exact different (congrArg PaidFiring.occurrence (funded_receipt_injective first second allowance firstFunded secondFunded same))

def completedFiring (request : GeneralOccurrenceFrontier.Request) (state : State request)
    (protocol : Protocol) (slot question session provider client budget : Nat)
    (answer : Answer request) (found : state.answers[slot]? = some answer)
    (affordable : protocol.deliveryCost question answer.val.target + protocol.inspectionCost question answer.val.target ≤ budget) :
    PaidFiring request state protocol question session provider client (protocol.test question answer.val.target) where
  slot := slot
  occurrence := answer
  emitted := found
  budget := budget
  assay :=
    { round := paidRound request state protocol slot question session provider client budget
      response := (session, ComplementaryAssay.verdictOf (protocol.test question answer.val.target), client, answer.val.target)
      authenticated := by
        rw [paid_responses request state protocol slot question session provider client budget answer found, if_pos affordable]
        exact Multiset.mem_singleton_self _
      readout := ComplementaryAssay.verdictOf_bit _ }

theorem incomplete_empty_no_elimination {Hypotheses : Type} (request : GeneralOccurrenceFrontier.Request)
    (state : State request) (protocol : Protocol) (slot question session provider client budget : Nat)
    (empty : state.answers = []) (prediction : Hypotheses → Nat → Bool) (candidates : Finset Hypotheses) :
    Mettapedia.OSLF.Framework.FiniteAssayLearner.revise prediction candidates question
      (paidRound request state protocol slot question session provider client budget).responses = candidates := by
  rw [empty_search_silent request state protocol slot question session provider client budget empty]
  exact Mettapedia.OSLF.Framework.FiniteAssayLearner.silence_preserves _ _ _

theorem underfunded_no_elimination {Hypotheses : Type} (request : GeneralOccurrenceFrontier.Request)
    (state : State request) (protocol : Protocol) (slot question session provider client budget : Nat)
    (answer : Answer request) (found : state.answers[slot]? = some answer)
    (underfunded : budget < protocol.deliveryCost question answer.val.target + protocol.inspectionCost question answer.val.target)
    (prediction : Hypotheses → Nat → Bool) (candidates : Finset Hypotheses) :
    Mettapedia.OSLF.Framework.FiniteAssayLearner.revise prediction candidates question
      (paidRound request state protocol slot question session provider client budget).responses = candidates := by
  rw [underfunded_silent request state protocol slot question session provider client budget answer found underfunded]
  exact Mettapedia.OSLF.Framework.FiniteAssayLearner.silence_preserves _ _ _

theorem genuine_refutation_removes {Hypotheses : Type} {request : GeneralOccurrenceFrontier.Request}
    {state : State request} {protocol : Protocol} {question session provider client : Nat} {bit : Bool}
    (receipt : PaidFiring request state protocol question session provider client bit)
    (prediction : Hypotheses → Nat → Bool) (candidates : Finset Hypotheses) (hypothesis : Hypotheses)
    (refuted : prediction hypothesis question ≠ bit) :
    hypothesis ∉ Mettapedia.OSLF.Framework.FiniteAssayLearner.revise prediction candidates question receipt.assay.round.responses := by
  apply Mettapedia.OSLF.Framework.FiniteAssayLearner.response_removes _ _ _ _ _ receipt.assay.response receipt.assay.authenticated
  simpa only [receipt.assay.readout] using refuted

theorem correct_hypothesis_survives {Hypotheses : Type} {request : GeneralOccurrenceFrontier.Request}
    {state : State request} {protocol : Protocol} {question session provider client : Nat} {bit : Bool}
    (receipt : PaidFiring request state protocol question session provider client bit)
    (prediction : Hypotheses → Nat → Bool) (candidates : Finset Hypotheses) (hypothesis : Hypotheses)
    (initial : hypothesis ∈ candidates) (predicts : prediction hypothesis question = bit) :
    hypothesis ∈ Mettapedia.OSLF.Framework.FiniteAssayLearner.revise prediction candidates question receipt.assay.round.responses := by
  apply (Mettapedia.OSLF.Framework.FiniteAssayLearner.revise_mem prediction candidates question
    receipt.assay.round.responses hypothesis).mpr
  refine ⟨initial, ?_⟩
  intro response present
  obtain ⟨_, _, _, singleton, _, _⟩ :=
    receipt.assay.round.response_sound receipt.assay.response receipt.assay.authenticated
  have same : response = receipt.assay.response := Multiset.mem_singleton.mp (singleton ▸ present)
  rw [same, receipt.assay.readout]
  exact predicts

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrencePaidReadouts
