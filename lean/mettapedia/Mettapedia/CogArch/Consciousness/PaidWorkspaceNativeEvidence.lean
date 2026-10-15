import Mettapedia.CogArch.Consciousness.PaidWorkspaceDescriptions
import Mettapedia.OSLF.Framework.PaidInterventionalEvidenceTransport

/-!
# Native comprehension and dependent sums for paid workspace receipts

The native index retains the concrete snapshot, question, initial purse,
session, provider, client and answer. Its witness is the complete paid
experiment and authenticated packet. The initial funding readout is earned
from its actual expenditure and remaining-purse ledger.

Architectural compression maps both real paths. Its public index forgets
the event counter, but the dependent-sum receipt retains the source index and
entire source witness. Universal elimination computes the supplied compressed
receipt without selecting an inverse snapshot.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.Consciousness.PaidWorkspaceNativeEvidence

open _root_.CategoryTheory
open Mettapedia.GSLT.Causality
open Mettapedia.GSLT.Causality.ProbeCampaign
open Mettapedia.CogArch.Consciousness.ArchitecturalIndicators
open Mettapedia.CogArch.Consciousness.PaidWorkspaceExperiments
open Mettapedia.CogArch.Consciousness.PaidWorkspaceDescriptions
open Mettapedia.OSLF.Framework.PaidInterventionalNativeEvidence
open Mettapedia.OSLF.Framework.PaidInterventionalEvidenceTransport
open Mettapedia.TypeTheory.DisplayedPresheafTransport

structure ReceiptIndex (Snapshot : Type) where
  snapshot : Snapshot
  question : Question
  budget : Nat
  session : Nat
  provider : Nat
  client : Nat
  answer : Bool

abbrev SourceIndex := ReceiptIndex State
abbrev CoreIndex := ReceiptIndex CoreState

abbrev SourceEvidence (key : SourceIndex) : Type :=
  AnsweredExperiment key.snapshot key.question key.budget key.session key.provider key.client key.answer

structure AnsweredCoreExperiment (state : CoreState) (question : Question)
    (budget session provider client : Nat) (value : Bool) where
  experiment : CoreExperiment state question budget session provider client
  response : Response Bool Nat
  authenticated : response ∈ experiment.assay.responses
  readout : response.2.1.bit = value

abbrev CoreEvidence (key : CoreIndex) : Type :=
  AnsweredCoreExperiment key.snapshot key.question key.budget key.session key.provider key.client key.answer

namespace AnsweredCoreExperiment

variable {state : CoreState} {question : Question} {budget session provider client : Nat} {value : Bool}

/-- Target agreement follows from the target's independently computed
endpoint and authenticated offer, without inspecting a realization mode. -/
theorem observation_agrees
    (receipt : AnsweredCoreExperiment state question budget session provider client value) :
    value = coreObservation state question := by
  obtain ⟨actual, arrives, responseEq, _, _, _⟩ :=
    receipt.experiment.assay.response_sound receipt.response receipt.authenticated
  have complete : question.commands.length ≤ budget := by
    by_contra incomplete
    simp only [coreRequest, if_neg incomplete] at arrives
    cases arrives
  have actualObservation : actual = coreObservation state question := by
    simp only [coreRequest, if_pos complete, coreProbeEndpoint] at arrives
    rw [List.take_of_length_le complete] at arrives
    exact (Option.some.inj arrives).symm
  have packet := receipt.readout
  rw [responseEq, ComplementaryAssay.verdictOf_bit] at packet
  change actual = value at packet
  exact packet.symm.trans actualObservation

end AnsweredCoreExperiment

def sourceInitial (key : SourceIndex) (receipt : SourceEvidence key) : Nat :=
  receipt.experiment.spent + receipt.experiment.remaining

def coreInitial (key : CoreIndex) (receipt : CoreEvidence key) : Nat :=
  coreExperimentSpent receipt.experiment + coreExperimentRemaining receipt.experiment

theorem sourceInitial_eq_budget (key : SourceIndex) (receipt : SourceEvidence key) :
    sourceInitial key receipt = key.budget := by
  have conserved := receipt.experiment.ledger
  dsimp [sourceInitial]
  omega

theorem coreInitial_eq_budget (key : CoreIndex) (receipt : CoreEvidence key) :
    coreInitial key receipt = key.budget := by
  have conserved := coreExperimentLedger receipt.experiment
  dsimp [coreInitial]
  omega

def coreIndex (key : SourceIndex) : CoreIndex where
  snapshot := coreView key.snapshot
  question := key.question
  budget := key.budget
  session := key.session
  provider := key.provider
  client := key.client
  answer := key.answer

def compressReceipt (key : SourceIndex) (receipt : SourceEvidence key) : CoreEvidence (coreIndex key) where
  experiment := compressExperiment receipt.experiment
  response := receipt.response
  authenticated := by
    change receipt.response ∈ (compressExperiment receipt.experiment).assay.responses
    rw [compressExperiment_responses]
    exact receipt.authenticated
  readout := receipt.readout

/-- This concrete witness map is nonidentity on states and transports
actual command and resource paths. Its charge law uses their earned ledgers. -/
def compressionWitness : WitnessMap SourceEvidence CoreEvidence sourceInitial coreInitial where
  index := coreIndex
  witness := compressReceipt
  charge := by
    intro key receipt
    exact (coreInitial_eq_budget (coreIndex key) (compressReceipt key receipt)).trans
      (sourceInitial_eq_budget key receipt).symm

def nativeFamily := fundedFamily SourceEvidence sourceInitial

def nativeComprehension := fundedComprehension SourceEvidence sourceInitial

def coreNativeFamily := fundedFamily CoreEvidence coreInitial

def comprehensionTranslation := compressionWitness.total

def originReceipts := compressionWitness.receipts

def insert (allowance : Nat) (key : SourceIndex) (receipt : SourceEvidence key)
    (affordable : sourceInitial key receipt ≤ allowance) :
    nativeFamily.obj ⟨Opposite.op allowance, key⟩ :=
  introduce SourceEvidence sourceInitial allowance key receipt affordable

/-- The ordinary comprehension mapping exposes the actual compressed
receipt. The dependent sum below additionally retains its source origin. -/
theorem comprehension_maps_actual_receipt (allowance : Nat) (key : SourceIndex)
    (receipt : SourceEvidence key) (affordable : sourceInitial key receipt ≤ allowance) :
    comprehensionTranslation.app (Opposite.op allowance)
      ⟨key, insert allowance key receipt affordable⟩ =
      ⟨coreIndex key, introduce CoreEvidence coreInitial allowance (coreIndex key)
        (compressReceipt key receipt) ((compressionWitness.charge key receipt).le.trans affordable)⟩ :=
  compressionWitness.total_readout allowance key receipt affordable

def retainOrigin (allowance : Nat) (key : SourceIndex) (receipt : SourceEvidence key)
    (affordable : sourceInitial key receipt ≤ allowance) :
    originReceipts.obj ⟨Opposite.op allowance, coreIndex key⟩ :=
  compressionWitness.retain allowance key receipt affordable

theorem retains_complete_origin (allowance : Nat) (key : SourceIndex)
    (receipt : SourceEvidence key) (affordable : sourceInitial key receipt ≤ allowance) :
    (retainOrigin allowance key receipt affordable).val.2.val.val =
      (⟨key, receipt⟩ : Sigma SourceEvidence) :=
  compressionWitness.retain_origin allowance key receipt affordable

theorem eliminate_computes_actual_compression (allowance : Nat) (key : SourceIndex)
    (receipt : SourceEvidence key) (affordable : sourceInitial key receipt ≤ allowance) :
    compressionWitness.eliminate.app ⟨Opposite.op allowance, coreIndex key⟩
      (retainOrigin allowance key receipt affordable) =
      introduce CoreEvidence coreInitial allowance (coreIndex key) (compressReceipt key receipt)
        ((compressionWitness.charge key receipt).le.trans affordable) :=
  compressionWitness.eliminate_retained allowance key receipt affordable

theorem budget_substitution_retains_witness (first second : Nat) (included : first ≤ second)
    (key : SourceIndex) (receipt : SourceEvidence key) (affordable : sourceInitial key receipt ≤ first) :
    nativeFamily.map
      (CategoryOfElements.homMk (F := (Functor.const BudgetWorldᵒᵖ).obj SourceIndex)
        ⟨Opposite.op first, key⟩ ⟨Opposite.op second, key⟩
        (homOfLE (X := BudgetWorld) included).op rfl)
      (insert first key receipt affordable) =
      insert second key receipt (affordable.trans included) :=
  introduced_substitution SourceEvidence sourceInitial first second included key receipt affordable

/-! ## Equal compressed answers keep distinct source receipts -/

def countedKey (count : Nat) : SourceIndex :=
  ⟨counted count, separatingQuestion, 7, 10, 20, 30, true⟩

def countedEvidence (count : Nat) : SourceEvidence (countedKey count) where
  experiment := execute (counted count) separatingQuestion 7 10 20 30
  response := (10, ComplementaryAssay.verdictOf true, 30, true)
  authenticated := by
    change (10, ComplementaryAssay.verdictOf true, 30, true) ∈
      (execute (counted count) separatingQuestion 7 10 20 30).responses
    rw [execute_responses, if_pos (by decide)]
    have observed : observation (counted count) separatingQuestion = true := by
      simp [observation, counted, separatingQuestion, broadcastWord, readField, run, step,
        reading, initial]
    rw [observed]
    exact Multiset.mem_singleton_self _
  readout := ComplementaryAssay.verdictOf_bit true

theorem countedEvidence_funded (count : Nat) :
    sourceInitial (countedKey count) (countedEvidence count) ≤ 7 := by
  rw [sourceInitial_eq_budget]
  exact le_rfl

theorem compressed_indices_collide : coreIndex (countedKey 0) = coreIndex (countedKey 7) := rfl

theorem retained_counted_origins_distinct :
    retainOrigin 7 (countedKey 0) (countedEvidence 0) (countedEvidence_funded 0) ≠
      retainOrigin 7 (countedKey 7) (countedEvidence 7) (countedEvidence_funded 7) := by
  intro same
  have snapshots := congrArg (fun receipt => receipt.val.2.val.val.1.snapshot.evidence) same
  change (0 : Nat) = 7 at snapshots
  omega

/-- Forgetting all public indices except the Boolean answer still retains
the entire actual paid experiment in the dependent answer fibre. -/
def answerSigma := answerReceipts SourceEvidence sourceInitial (fun key => key.answer)

def retainBooleanOrigin (allowance : Nat) (key : SourceIndex) (receipt : SourceEvidence key)
    (affordable : sourceInitial key receipt ≤ allowance) :
    answerSigma.obj ⟨Opposite.op allowance, key.answer⟩ :=
  retainAnswer SourceEvidence sourceInitial (fun key => key.answer)
    allowance key receipt affordable

theorem boolean_answer_retains_complete_origin (allowance : Nat) (key : SourceIndex)
    (receipt : SourceEvidence key) (affordable : sourceInitial key receipt ≤ allowance) :
    (retainBooleanOrigin allowance key receipt affordable).val.2.val.val =
      (⟨key, receipt⟩ : Sigma SourceEvidence) :=
  answer_retains_witness SourceEvidence sourceInitial (fun key => key.answer)
    allowance key receipt affordable

theorem same_boolean_answer_distinct_receipts :
    retainBooleanOrigin 7 (countedKey 0) (countedEvidence 0) (countedEvidence_funded 0) ≠
      retainBooleanOrigin 7 (countedKey 7) (countedEvidence 7) (countedEvidence_funded 7) := by
  intro same
  have snapshots := congrArg (fun receipt => receipt.val.2.val.val.1.snapshot.evidence) same
  change (0 : Nat) = 7 at snapshots
  omega

theorem source_receipt_not_available_at_six :
    ¬ Nonempty (nativeFamily.obj ⟨Opposite.op 6, countedKey 0⟩) := by
  rintro ⟨receipt⟩
  have original : receipt.val.val.1 = countedKey 0 := receipt.property
  have funded := receipt.val.property
  rw [sourceInitial_eq_budget, original] at funded
  change (7 : Nat) ≤ 6 at funded
  omega

end Mettapedia.CogArch.Consciousness.PaidWorkspaceNativeEvidence
