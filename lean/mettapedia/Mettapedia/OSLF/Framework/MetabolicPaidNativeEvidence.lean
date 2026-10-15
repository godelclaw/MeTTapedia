import Mettapedia.OSLF.Framework.MetabolicPaidControls
import Mettapedia.CogArch.Consciousness.PaidWorkspaceNativeEvidence

/-!
# Native families retain acquired resources and learning receipts

The native witness includes the complete source cost stack, supplied
occurrence configuration, actual acquisition and every synchronized debit.
Its public map exposes the independently authenticated workspace receipt.
The dependent sum retains the full resource origin even when public answers
and their compressed architectural descriptions agree.

The family allowance catalogs already witnessed resources. Increasing that
allowance preserves the same acquisition and execution; it does not create
a new stack or mint additional operational funding.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.MetabolicPaidNativeEvidence

open _root_.CategoryTheory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic
open Mettapedia.CogArch.Consciousness.ArchitecturalIndicators
open Mettapedia.CogArch.Consciousness.PaidWorkspaceExperiments
open Mettapedia.CogArch.Consciousness.PaidWorkspaceDescriptions
open Mettapedia.CogArch.Consciousness.PaidWorkspaceNativeEvidence
open Mettapedia.GSLT.Causality Mettapedia.GSLT.Causality.ProbeCampaign
open Mettapedia.OSLF.Framework.MetabolicPaidLearner
open Mettapedia.OSLF.Framework.MetabolicPaidControls
open Mettapedia.OSLF.Framework.PaidInterventionalNativeEvidence
open Mettapedia.OSLF.Framework.PaidInterventionalEvidenceTransport
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Cost

structure ResourceIndex where
  snapshot : State
  question : Question
  sourceStack : CostStack Nat
  unitCells : ∀ signature ∈ sourceStack.toList, signature.card = 1
  session : Nat
  provider : Nat
  client : Nat
  record : List (CostSig Nat)
  source : Configuration
  answer : Bool

def physicalStack (key : ResourceIndex) : Stack (CostSig Nat) :=
  Cost.Metabolic.StackInternalization.stack key.sourceStack

structure Evidence (key : ResourceIndex) where
  metabolic : AcquiredExperiment encoding key.snapshot key.question (physicalStack key)
    key.session key.provider key.client key.record key.source
  response : Response Bool Nat
  authenticated : response ∈ metabolic.answers
  readout : response.2.1.bit = key.answer

def paidKey (key : ResourceIndex) : SourceIndex where
  snapshot := key.snapshot
  question := key.question
  budget := (physicalStack key).size
  session := key.session
  provider := key.provider
  client := key.client
  answer := key.answer

def paidWitness (key : ResourceIndex) (evidence : Evidence key) : SourceEvidence (paidKey key) where
  experiment := evidence.metabolic.experiment
  response := evidence.response
  authenticated := evidence.authenticated
  readout := evidence.readout

/-- The initial readout is calculated from actual structural expenditure
and the remaining acquired resource, not supplied as an external grant. -/
def initialResource (key : ResourceIndex) (evidence : Evidence key) : Nat :=
  evidence.metabolic.experiment.spent + evidence.metabolic.coupling.finalStack.size

theorem initialResource_eq_stack (key : ResourceIndex) (evidence : Evidence key) :
    initialResource key evidence = (physicalStack key).size := by
  have conserved := evidence.metabolic.resource_ledger
  dsimp only [initialResource]
  omega

theorem initialResource_eq_source_cells (key : ResourceIndex) (evidence : Evidence key) :
    initialResource key evidence = key.sourceStack.cellCount :=
  (initialResource_eq_stack key evidence).trans
    (Cost.Metabolic.StackInternalization.exact_cells key.sourceStack)

private theorem unit_list_valuation (cells : List (CostSig Nat))
    (unitCells : ∀ signature ∈ cells, signature.card = 1) : cells.sum.card = cells.length := by
  induction cells with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      have headUnit := unitCells head List.mem_cons_self
      have tailUnit : ∀ signature ∈ rest, signature.card = 1 :=
        fun signature member => unitCells signature (List.mem_cons_of_mem head member)
      simp only [List.sum_cons, Multiset.card_add, List.length_cons]
      rw [headUnit, inductionHypothesis tailUnit, Nat.add_comm]

theorem initialResource_eq_source_signature_valuation (key : ResourceIndex) (evidence : Evidence key) :
    initialResource key evidence = key.sourceStack.storedSignatures.card := by
  rw [initialResource_eq_source_cells, CostStack.cellCount_eq_length,
    CostStack.storedSignatures_eq_sum]
  exact (unit_list_valuation key.sourceStack.toList key.unitCells).symm

theorem complete_signature_balance (key : ResourceIndex) (evidence : Evidence key) :
    key.sourceStack.storedSignatures = evidence.metabolic.coupling.consumedHeads.sum +
      evidence.metabolic.coupling.finalStack.heads.sum := by
  have ordered := congrArg (fun cells : List (CostSig Nat) => cells.sum)
    evidence.metabolic.coupling.ordered_heads
  have initial := Cost.Metabolic.StackInternalization.exact_signatures key.sourceStack
  exact initial.symm.trans (ordered.trans List.sum_append)

/-- In this admitted unit-cell profile, the exact consumed signature
valuation agrees with the actual paid learner's charge. -/
theorem consumed_signature_price (key : ResourceIndex) (evidence : Evidence key) :
    evidence.metabolic.coupling.consumedHeads.sum.card = evidence.metabolic.experiment.spent := by
  have units : ∀ signature ∈ evidence.metabolic.coupling.consumedHeads, signature.card = 1 := by
    intro signature member
    have inWhole : signature ∈ (physicalStack key).heads :=
      evidence.metabolic.coupling.ordered_heads ▸ List.mem_append_left _ member
    have sourceOrder := Cost.Metabolic.StackInternalization.ordered_heads key.sourceStack
    exact key.unitCells signature (sourceOrder ▸ inWhole)
  exact (unit_list_valuation _ units).trans
    (evidence.metabolic.coupling.consumed_count.trans (MetabolicPaidTrace.experimentPath_spent _))

/-- Forgetting the resource protocol is an actual witness map to the
already checked learner consumer. Its dependent sum preserves that origin. -/
def paidWitnessMap : WitnessMap Evidence SourceEvidence initialResource sourceInitial where
  index := paidKey
  witness := paidWitness
  charge := by
    intro key evidence
    exact (sourceInitial_eq_budget (paidKey key) (paidWitness key evidence)).trans
      (initialResource_eq_stack key evidence).symm

def coreWitnessMap := paidWitnessMap.comp compressionWitness

def nativeFamily := fundedFamily Evidence initialResource

def nativeComprehension := fundedComprehension Evidence initialResource

def paidComprehension := paidWitnessMap.total

def originReceipts := paidWitnessMap.receipts

def insert (allowance : Nat) (key : ResourceIndex) (evidence : Evidence key)
    (available : initialResource key evidence ≤ allowance) :
    nativeFamily.obj ⟨Opposite.op allowance, key⟩ :=
  introduce Evidence initialResource allowance key evidence available

def retainResource (allowance : Nat) (key : ResourceIndex) (evidence : Evidence key)
    (available : initialResource key evidence ≤ allowance) :
    originReceipts.obj ⟨Opposite.op allowance, paidKey key⟩ :=
  paidWitnessMap.retain allowance key evidence available

theorem retains_complete_resource (allowance : Nat) (key : ResourceIndex) (evidence : Evidence key)
    (available : initialResource key evidence ≤ allowance) :
    (retainResource allowance key evidence available).val.2.val.val =
      (⟨key, evidence⟩ : Sigma Evidence) :=
  paidWitnessMap.retain_origin allowance key evidence available

theorem eliminate_computes_actual_paid_receipt (allowance : Nat) (key : ResourceIndex)
    (evidence : Evidence key) (available : initialResource key evidence ≤ allowance) :
    paidWitnessMap.eliminate.app ⟨Opposite.op allowance, paidKey key⟩
      (retainResource allowance key evidence available) =
      introduce SourceEvidence sourceInitial allowance (paidKey key) (paidWitness key evidence)
        ((paidWitnessMap.charge key evidence).le.trans available) :=
  paidWitnessMap.eliminate_retained allowance key evidence available

theorem native_substitution_retains_actual_execution (first second : Nat) (included : first ≤ second)
    (key : ResourceIndex) (evidence : Evidence key) (available : initialResource key evidence ≤ first) :
    nativeFamily.map
      (CategoryOfElements.homMk (F := (Functor.const BudgetWorldᵒᵖ).obj ResourceIndex)
        ⟨Opposite.op first, key⟩ ⟨Opposite.op second, key⟩
        (homOfLE (X := BudgetWorld) included).op rfl)
      (insert first key evidence available) =
      insert second key evidence (available.trans included) :=
  introduced_substitution Evidence initialResource first second included key evidence available

theorem observation_agrees (key : ResourceIndex) (evidence : Evidence key) :
    key.answer = observation key.snapshot key.question :=
  (paidWitness key evidence).observation_agrees

theorem actual_partial_description (key : ResourceIndex) (evidence : Evidence key) :
    answer evidence.metabolic.experiment = some key.answer :=
  (paidWitness key evidence).actual_answer

theorem native_intervention_certificate (key : ResourceIndex) (evidence : Evidence key) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF theory).satisfies
      (S := ()) key.snapshot (probeNativeType key.question.commands (key.question.field, key.answer)).pred :=
  (paidWitness key evidence).native_certificate

theorem actual_learning_readout (key : ResourceIndex) (evidence : Evidence key) (hypotheses : Finset Mode) :
    evidence.metabolic.revision hypotheses =
      Mettapedia.OSLF.Framework.FiniteAssayLearner.revise prediction hypotheses key.question
        (paidWitness key evidence).experiment.responses := rfl

/-- The core map is the actual architectural compression of the supplied
paid experiment; the retained sum continues to store its metabolic origin. -/
theorem core_transport_executes (key : ResourceIndex) (evidence : Evidence key) :
    (coreWitnessMap.witness key evidence).experiment =
      compressExperiment evidence.metabolic.experiment := rfl

theorem credits_unit_cells (atom count : Nat) :
    ∀ signature ∈ (credits atom count).toList, signature.card = 1 := by
  induction count with
  | zero => simp [credits, CostStack.toList]
  | succ count inductionHypothesis =>
      intro signature member
      change signature ∈ {atom} :: (credits atom count).toList at member
      rcases List.mem_cons.mp member with same | later
      · subst signature; rfl
      · exact inductionHypothesis signature later

def connectedKey (atom count : Nat) : ResourceIndex where
  snapshot := initial .connected
  question := separatingQuestion
  sourceStack := credits atom count
  unitCells := credits_unit_cells atom count
  session := 10
  provider := 20
  client := 30
  record := []
  source := sourceFor encoding (initial .connected) separatingQuestion (units atom count)
    10 20 30 [] acquisitionOrigins 100
  answer := true

def connectedEvidence (atom : Nat) : Evidence (connectedKey atom 7) where
  metabolic := workspaceReceipt .connected atom 7
  response := (10, ComplementaryAssay.verdictOf
    (observation (initial .connected) separatingQuestion), 30,
    observation (initial .connected) separatingQuestion)
  authenticated := by
    change _ ∈ (workspaceReceipt .connected atom 7).answers
    rw [funded_actual_answer]
    exact Multiset.mem_singleton_self _
  readout := (ComplementaryAssay.verdictOf_bit _).trans separating_execution_answers.1

theorem connectedInitial (atom : Nat) :
    initialResource (connectedKey atom 7) (connectedEvidence atom) = 7 :=
  (initialResource_eq_stack _ _).trans (units_size atom 7)

def commonPaidKey : SourceIndex :=
  ⟨initial .connected, separatingQuestion, 7, 10, 20, 30, true⟩

theorem connected_paid_index (atom : Nat) : paidKey (connectedKey atom 7) = commonPaidKey := by
  exact congrArg (fun budget => (⟨initial .connected, separatingQuestion, budget, 10, 20, 30, true⟩ : SourceIndex))
    (units_size atom 7)

def retainedConnected (atom : Nat) : originReceipts.obj ⟨Opposite.op 7, commonPaidKey⟩ :=
  (connected_paid_index atom) ▸ retainResource 7 (connectedKey atom 7) (connectedEvidence atom)
    (connectedInitial atom).le

theorem retainedConnected_origin (atom : Nat) :
    (retainedConnected atom).val.2.val.val =
      (⟨connectedKey atom 7, connectedEvidence atom⟩ : Sigma Evidence) := by
  unfold retainedConnected
  cases connected_paid_index atom
  exact retains_complete_resource 7 (connectedKey atom 7) (connectedEvidence atom)
    (connectedInitial atom).le

theorem same_answer_distinct_resource_receipts : retainedConnected 0 ≠ retainedConnected 1 := by
  intro same
  have complete := congrArg (fun receipt => receipt.val.2.val.val) same
  rw [retainedConnected_origin, retainedConnected_origin] at complete
  have sourceStacks := congrArg (fun receipt : Sigma Evidence => receipt.1.sourceStack) complete
  change credits 0 7 = credits 1 7 at sourceStacks
  have distinct : credits 0 7 ≠ credits 1 7 := by decide +kernel
  exact distinct sourceStacks

theorem short_stack_has_no_completed_evidence (atom : Nat) :
    IsEmpty (Evidence (connectedKey atom 6)) := by
  refine ⟨fun evidence => ?_⟩
  have silent := evidence.metabolic.underfunded_silent (by
    change (units atom 6).size < separatingQuestion.commands.length + 2 + 3
    rw [units_size]
    decide)
  have present := evidence.authenticated
  rw [silent] at present
  simp at present

/-- A completed answer requires a real initial acquisition firing. -/
theorem unavailable_acquisition_has_no_evidence (key : ResourceIndex)
    (blocked : ∀ _ : ResourcePredation.Firing key.source, False) : IsEmpty (Evidence key) :=
  ⟨fun evidence => blocked evidence.metabolic.acquisition.claim⟩

/-- Declaring seven credits does not fund an experiment when no physical
offer is present in its actual configuration. -/
def unofferedKey (atom : Nat) : ResourceIndex :=
  { connectedKey atom 7 with source := Configuration.ofList [] }

theorem unoffered_source_has_no_acquisition (atom : Nat) :
    ∀ _ : ResourcePredation.Firing (unofferedKey atom).source, False := by
  intro firing
  have impossible : firing.inputIndex.val < 0 := firing.inputIndex.isLt
  omega

theorem unoffered_source_has_no_completed_evidence (atom : Nat) :
    IsEmpty (Evidence (unofferedKey atom)) :=
  unavailable_acquisition_has_no_evidence (unofferedKey atom) (unoffered_source_has_no_acquisition atom)

theorem connected_native_revision (atom : Nat) :
    (connectedEvidence atom).metabolic.revision candidates = {.connected} :=
  connected_intervention_learns atom

end Mettapedia.OSLF.Framework.MetabolicPaidNativeEvidence
