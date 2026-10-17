import Mettapedia.Algebra.SharedCoefficientLedger
import Mettapedia.Machines.Cursor.SharedOccurrenceOwnership
import Mettapedia.Machines.DemandBoundary
import Mettapedia.Machines.BranchLocalNeed.WeightedResumption
import Mettapedia.Machines.BranchLocalNeed.QualifiedReplay
import Mettapedia.Machines.BranchLocalNeed.InteractionAuthority
import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.Dynamics.EffectTraceInterleaving
import Mettapedia.GSLT.Dynamics.IndexedEventValuation
import Mettapedia.GSLT.Dynamics.IndependentEventValuationProduct
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec
import Mettapedia.Machines.OwnedPullDriver
import Mettapedia.Machines.Cursor.PermutationInvariantFold
import Mettapedia.GSLT.Core.InferenceRecording
import Mettapedia.Machines.NativeCostLedger

/-!
# Owned producer-account transport

The native scalar rendezvous publishes a grounded atom and fails every other
claim. This module keeps the producer account instead of that atom.

The resumption instance is the existing completed-receipt production
`NeedCacheLaws.CompletedReceiptControls`, run by
`NeedWeightedResumption.ProductionResumptionControls`. `Histories` is a
section in that file, not a namespace. The reused controls are
`completed_shared_production`, `suspension_retains_paid_production`,
`resumed_shared_production`, and `resetting_incoming_coefficient_refused`:
one shared production, two cached deliveries, ten transitions, and the
non-unit coefficient `2`.
Suspension is the fuel-1 cut. The ready account is that leaf, not the
pre-production occurrence paired with it. Resume sequences the cut for the
remaining ten steps. A production factor is earned only when that cut's
coefficient says so. Later deliveries contribute the coefficient monoid's
identity, so resume does not append a pending factor and a second resume does
not charge the production again. Restarting the suffix from the pending leaf
drops the incoming `2`.

Admission reads every leaf in the cut. A pending step requires `force` even
when the caller requests no rights. A returned cut requires `inspect` and does
not require `force`. Leaves whose worlds differ are not collapsed to the first
leaf. The scalar and proposal operations below refuse publication and do not
install an account.

Worlds are the Need machine's worlds. Rights are `DemandBoundary.Right`.
`restrict?` only attenuates the caller's request. The operation's own rights
are read from the cut and are required even when that request is empty.
Matching `heap.spine` does not determine `heap.current` unless both heaps are
`Heap.Recorded`. The receipt heap is one recorded allocation of the commit
cell followed by `setKnownCache` of that suspended record, and the receipt
run preserves `Recorded`. Checkpoint still compares spines. `Recorded` is the
agreement hypothesis, not another Boolean gate.
The three-node `Controls.sharedCycle` is a representation control carried
beside the cut. Its addresses are not cells of the Need heap. These facts do
not connect Need payload roots and do not qualify general ownership.
The production's demand cell is the commit cell retained in the occurrence
spine. Cancelling one consumer of that separate cycle drops only that
consumer's roots.

The live-root consumer below is a different source run. Its value is the
existing call-time-choice `Val`: one application holding two `need`
occurrences of one shared demand, whose origin captures a binding cell.
`ReferenceInventory` reads that value and the cell record. It is not a
numeric root assigned to the Nat receipt, and it is not `sharedCycle`.
Two consumers of the occurrence list share the reachable cells. Cancelling
one removes only that consumer's roots. A cell-free value on the same heap
does not preserve the demand. The two branch worlds stay separate.
Checkpoint still does not carry `Recorded`, a root inventory, force rights,
or a world join. The ordered account in `LiveRoots` is this run's receipt
graph in chronological order. Each factor identity is the receipt occurrence
the stepper wrote, and its coefficient is that receipt's world. Those words
are a noncommutative history readout. The source-order merge has eight
factors and is the receipt account of neither returned world; each returned
world has five. That merge is a representation comparison, not a
source-qualified producer, world, or claim join. An unchanged left account
beside the merged sidecar is not the joined source account.
The generic Need production ledger is another reading of the same
transitions. Its coefficient is the existing production-only assignment:
`2` on a real production receipt and `1` on every other instruction. The Nat
payment is that ledger's denotation, including an incoming payment kept
across a residual and dropped when the suffix is restarted. A complete
receipt list does not finish unfinished coefficient work. Same-world
admission and OR alternatives are separate dispositions. The numeric ledger
below is not either account. Agreement beyond this run remains open.
The general transport reads that same source. A contribution carries its
incoming coefficient, the generic production ledger, the recorded heap, and
the residual cut. Split paths refuse a join and keep both accounts. A paid
pending cut keeps the earned coefficient while the machine still needs
force. A rejected delivery keeps the full account and its proposals. An
accepted final return keeps the other consumer's live roots and does not
finish the unforced payload. Copies of one ledger are shared observation.
An independent AND join of two distinct productions in one recorded world
is not this run. `JointSource` below is a separate execution: two cells
allocated on one lineage before either force, then two singleton forces in
source order. Its combined account is that execution's production ledger.
Both runs instantiate one trace replay of `productionLedger`. A prefix keeps
the factors already earned, and the incoming ledger stays in front of the
suffix. This payload run stays the OR boundary and the shared-observation copy.

The coefficient-list ledger below is a representation control for prefix
refusal, noncommutative denotation, and supported claims. It is not a second
production receipt, resume does not extend it, and it is not the receipt
account in `LiveRoots`.

The native names are an obligation map checked against the current source.
They are not compiled-code verification. This file does not change C.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ProducerAccountTransport

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.Machines.Cursor.SharedOccurrenceOwnership
open Mettapedia.Machines.Cursor.SharedOccurrenceLog
open Mettapedia.Machines.ResourceOwnership
open Mettapedia.Machines.ResourceOwnership.Examples
open Mettapedia.Machines.DemandBoundary
open Mettapedia.Machines.BranchLocalNeed.NeedCacheLaws
open Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption
open Mettapedia.Machines.BranchLocalNeed.NeedQualifiedReplay
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Dynamics.WeightedBranchingResumption
open Mettapedia.GSLT.Dynamics.WeightedResumption

/-! ## Ordered coefficient words -/

structure Coeff where
  tokens : List Nat
  deriving DecidableEq, Repr

instance : Mul Coeff where
  mul a b := ⟨a.tokens ++ b.tokens⟩

instance : One Coeff where
  one := ⟨[]⟩

instance : Monoid Coeff where
  mul_assoc a b c := by
    cases a
    cases b
    cases c
    apply congrArg Coeff.mk
    exact List.append_assoc _ _ _
  one_mul a := by
    cases a
    apply congrArg Coeff.mk
    exact List.nil_append _
  mul_one a := by
    cases a
    apply congrArg Coeff.mk
    exact List.append_nil _

/-! ## The qualified Need production -/

abbrev NeedMachine := Machine Unit Nat Nat Unit Nat Unit Unit Unit

abbrev NeedOccurrence := WorkOccurrence NeedMachine

abbrev Cut := List ((NeedOccurrence ⊕ NeedOccurrence) × Nat)

/-- The production coefficient used by `ProductionResumptionControls`: `2` when
the source machine completes a production receipt, and the monoid identity
otherwise. -/
def productionSource : Coalgebra NeedOccurrence NeedOccurrence Nat :=
  source CompletedReceiptControls.spec
    (productionCoefficient (fun _ => (2 : Nat)))

def initialOccurrence : NeedOccurrence := ⟨CompletedReceiptControls.start, []⟩

def suspendedCut : Cut := contributions productionSource 1 initialOccurrence

def continueCut : NeedOccurrence ⊕ NeedOccurrence → Cut :=
  fun leaf =>
    match leaf with
    | .inl done => [(.inl done, (1 : Nat))]
    | .inr pending => contributions productionSource 10 pending

def sequenceCut (cut : Cut) : Cut :=
  Mettapedia.GSLT.Dynamics.WeightedResumption.sequence cut continueCut

/-- One suspended production followed by its ten-step continuation is the same
contribution list as the eleven-step run. This is `resume_exact` for the
completed-receipt spec, not a per-step ledger append. -/
theorem sequence_is_the_eleven_step_run :
    sequenceCut suspendedCut =
      contributions productionSource (1 + 10) initialOccurrence := by
  unfold sequenceCut continueCut suspendedCut productionSource initialOccurrence
  exact (resume_exact CompletedReceiptControls.spec
      (productionCoefficient (fun _ => (2 : Nat))) 1 10 initialOccurrence).symm

def project (cut : Cut) : List (Bool × Nat × Nat × Nat × List Nat) :=
  cut.map fun leaf =>
    (match leaf.1 with
      | .inl _ => true
      | .inr _ => false,
      (retained leaf.1).state.world.receipts.nextSerial,
      (retained leaf.1).state.work.transitions,
      leaf.2,
      (retained leaf.1).trace)

/-- Fuel 1 leaves the paid production pending: receipt serial 1, one
transition, coefficient 2, trace `[0]`. -/
theorem suspension_retains_paid_production :
    project suspendedCut = [(false, 1, 1, 2, [0])] :=
  ProductionResumptionControls.suspension_retains_paid_production

/-- The completed run returns one leaf: three receipts, ten transitions,
coefficient 2, and the ten successor indices. -/
theorem completed_shared_production :
    project (contributions productionSource 11 initialOccurrence) =
      [(true, 3, 10, 2, List.replicate 10 0)] :=
  ProductionResumptionControls.completed_shared_production

theorem resumed_shared_production :
    project (sequenceCut suspendedCut) = [(true, 3, 10, 2, List.replicate 10 0)] :=
  ProductionResumptionControls.resumed_shared_production

/-- Discarding the incoming coefficient and rerunning only the suffix keeps
the final occurrence but replaces the paid `2` with the identity `1`. -/
def restartedSuffix (cut : Cut) : Cut :=
  cut.flatMap fun leaf =>
    match leaf.1 with
    | .inl _ => []
    | .inr pending => contributions productionSource 10 pending

theorem restarting_the_suffix_drops_the_paid_coefficient :
    project (restartedSuffix suspendedCut) = [(true, 3, 10, 1, List.replicate 10 0)] ∧
      project (restartedSuffix suspendedCut) ≠ project (sequenceCut suspendedCut) :=
  ProductionResumptionControls.resetting_incoming_coefficient_refused

theorem project_singleton_returned (cut : Cut) (serial transitions weight : Nat)
    (trace : List Nat)
    (seen : project cut = [(true, serial, transitions, weight, trace)]) :
    ∃ occurrence paid,
      cut = [(.inl occurrence, paid)] ∧
      paid = weight ∧
      occurrence.trace = trace ∧
      occurrence.state.work.transitions = transitions ∧
      occurrence.state.world.receipts.nextSerial = serial := by
  cases cut with
  | nil => simp [project] at seen
  | cons head tail =>
      cases tail with
      | cons _ _ => simp [project] at seen
      | nil =>
          cases head with
          | mk leaf paid =>
              cases leaf with
              | inr _ => simp [project, retained] at seen
              | inl occurrence =>
                  simp [project, retained] at seen
                  obtain ⟨serialEq, rest⟩ := seen
                  obtain ⟨transitionsEq, rest⟩ := rest
                  obtain ⟨weightEq, traceEq⟩ := rest
                  exact ⟨occurrence, paid, rfl, weightEq, traceEq, transitionsEq, serialEq⟩

/-! ## Account -/

def supportedClaims (ledger : Ledger Nat Nat Coeff) (identity owner : Nat) : Nat → Option Nat :=
  fun candidate =>
    if decide (candidate = identity ∧ candidate ∈ identities ledger) then some owner else none

theorem supportedClaims_supported (ledger : Ledger Nat Nat Coeff) (identity owner : Nat) :
    Scoped.Supported ⟨ledger, supportedClaims ledger identity owner⟩ := by
  intro candidate claimant claimed
  cases held : decide (candidate = identity ∧ candidate ∈ identities ledger) with
  | false => simp [supportedClaims, held] at claimed
  | true =>
      simp [supportedClaims, held] at claimed
      exact (of_decide_eq_true held).2

def prefixFactor : Factor Nat Nat Coeff := ⟨1, 0, ⟨[1]⟩⟩
def sharedFactor : Factor Nat Nat Coeff := ⟨7, 3, ⟨[9]⟩⟩
def otherFactor : Factor Nat Nat Coeff := ⟨2, 0, ⟨[2]⟩⟩

def inheritedLedger : Ledger Nat Nat Coeff := [prefixFactor, sharedFactor]

def inherited : Scoped Nat Nat Coeff Nat :=
  ⟨inheritedLedger, supportedClaims inheritedLedger 7 0⟩

theorem inherited_supported : inherited.Supported :=
  supportedClaims_supported inheritedLedger 7 0

def rival : Scoped Nat Nat Coeff Nat :=
  ⟨inheritedLedger, supportedClaims inheritedLedger 7 1⟩

theorem rival_supported : rival.Supported :=
  supportedClaims_supported inheritedLedger 7 1

def demandCell (machine : NeedMachine) : Option CellId :=
  match machine.control with
  | .returned _ (.commit cell _ :: _) => some cell
  | .force cell _ => some cell
  | _ => none

def readyDemand : CellId :=
  match demandCell CompletedReceiptControls.start with
  | some cell => cell
  | none => ⟨0, [], 0, 0⟩

structure ProducerAccount where
  occurrence : NeedOccurrence
  rights : Rights
  demand : CellId
  paidProduction : Nat
  ledger : Scoped Nat Nat Coeff Nat
  delivery : Configuration (Fin 3) Nat 2
  cut : Cut

/-- A singleton leaf replaces the stored occurrence and payment. Every other
cut, including a multi-leaf residual, replaces only the cut: rights, demand,
ledger, and delivery stay the account's fields. -/
def adopt (account : ProducerAccount) (cut : Cut) : ProducerAccount :=
  { account with
      cut
      occurrence :=
        match cut with
        | [(.inl occurrence, _)] => occurrence
        | [(.inr occurrence, _)] => occurrence
        | _ => account.occurrence
      paidProduction :=
        match cut with
        | [(_, paid)] => paid
        | _ => account.paidProduction }

/-- Resume sequences the stored cut. The resulting payment is that sequence's
coefficient, which already contains the production receipt. -/
def resumeAccount (account : ProducerAccount) : ProducerAccount :=
  adopt account (sequenceCut account.cut)

/-- Built from the fuel-1 cut. `adopt` replaces the pre-production occurrence
and the zero payment with that pending leaf. -/
def ready : ProducerAccount :=
  adopt
    { occurrence := initialOccurrence
      rights := {Right.force, Right.inspect}
      demand := readyDemand
      paidProduction := 0
      ledger := inherited
      delivery := Controls.sharedCycle
      cut := suspendedCut }
    suspendedCut

theorem resume_keeps_ledger_rights_demand_and_delivery (account : ProducerAccount) :
    (resumeAccount account).ledger = account.ledger ∧
      (resumeAccount account).rights = account.rights ∧
      (resumeAccount account).demand = account.demand ∧
      (resumeAccount account).delivery = account.delivery := by
  unfold resumeAccount
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem returned_sequence_keeps_the_payment (occurrence : NeedOccurrence) (paid : Nat) :
    sequenceCut [(.inl occurrence, paid)] = [(.inl occurrence, paid * 1)] := by
  simp [sequenceCut, continueCut]

theorem second_resume_does_not_charge_again (account : ProducerAccount)
    (occurrence : NeedOccurrence) (paid : Nat)
    (shape : account.cut = [(.inl occurrence, paid)]) :
    (resumeAccount account).paidProduction = paid ∧
      (resumeAccount account).occurrence = occurrence ∧
      (resumeAccount account).ledger = account.ledger := by
  have cutEq : sequenceCut account.cut = [(.inl occurrence, paid * 1)] := by
    simpa [shape] using returned_sequence_keeps_the_payment occurrence paid
  unfold resumeAccount
  rw [cutEq]
  unfold adopt
  simp

theorem production_starts_without_receipts :
    CompletedReceiptControls.start.world.path = [] ∧
      CompletedReceiptControls.start.world.receipts.nextSerial = 0 ∧
      CompletedReceiptControls.start.work.transitions = 0 ∧
      initialOccurrence.trace = [] := by
  decide

theorem ready_demand_is_the_commit_cell :
    demandCell CompletedReceiptControls.start = some ready.demand := by
  rfl

theorem suspension_payment_is_ready :
    project ready.cut = [(false, 1, 1, ready.paidProduction, [0])] ∧
      ready.paidProduction = 2 ∧
      ready.occurrence.trace = [0] ∧
      ready.occurrence.trace ≠ initialOccurrence.trace := by
  have paid : ready.paidProduction = 2 := by
    unfold ready adopt
    rfl
  have trace : ready.occurrence.trace = [0] := by
    unfold ready adopt
    rfl
  refine ⟨?_, paid, trace, ?_⟩
  · rw [paid]
    unfold ready
    exact suspension_retains_paid_production
  · rw [trace]
    decide

theorem resume_adopts_the_completed_production :
    ∃ occurrence,
      (resumeAccount ready).cut = [(.inl occurrence, 2)] ∧
      (resumeAccount ready).occurrence = occurrence ∧
      (resumeAccount ready).paidProduction = ready.paidProduction ∧
      occurrence.trace = List.replicate 10 0 ∧
      occurrence.state.work.transitions = 10 ∧
      occurrence.state.world.receipts.nextSerial = 3 ∧
      (resumeAccount ready).ledger = ready.ledger ∧
      (resumeAccount ready).delivery = ready.delivery := by
  obtain ⟨occurrence, paid, same, paidEq, trace, transitions, serial⟩ :=
    project_singleton_returned (sequenceCut suspendedCut) 3 10 2
      (List.replicate 10 0) resumed_shared_production
  have step : sequenceCut ready.cut = [(.inl occurrence, paid)] := by
    unfold ready
    exact same
  unfold resumeAccount
  rw [step]
  unfold adopt
  refine ⟨occurrence, ?_, rfl, ?_, trace, transitions, serial, rfl, rfl⟩
  · rw [paidEq]
  · rw [paidEq, suspension_payment_is_ready.2.1]

/-! ## Admission -/

inductive Refusal where
  | staleWorld
  | changedDependency
  | missingRights
  | incompleteResidual
  | incoherentResidual
  | splitWorlds
  deriving DecidableEq, Repr

inductive Admit where
  | accept (account : ProducerAccount)
  | reject (reason : Refusal) (kept : ProducerAccount)

def Admit.kept : Admit → ProducerAccount
  | .accept account => account
  | .reject _ kept => kept

def leafPath (leaf : NeedOccurrence ⊕ NeedOccurrence) : WorldPath :=
  (retained leaf).state.world.path

def leafSpine (leaf : NeedOccurrence ⊕ NeedOccurrence) : List (HeapUpdate Unit Nat Unit) :=
  (retained leaf).state.world.heap.spine

/-- One pending non-halted step requires force. A returned leaf requires
inspect. The caller's requested subset is not this set. -/
def operationRights (cut : Cut) : Rights :=
  cut.foldl (fun acc leaf =>
    match leaf.1 with
    | .inl _ => acc ∪ {Right.inspect}
    | .inr pending =>
        match pending.state.control with
        | .halted _ => acc ∪ {Right.inspect}
        | _ => acc ∪ {Right.force}) ∅

def pathsUniform (cut : Cut) : Bool :=
  match cut with
  | [] => false
  | leaf :: rest => rest.all fun other => decide (leafPath other.1 = leafPath leaf.1)

def spinesUniform (cut : Cut) : Bool :=
  match cut with
  | [] => false
  | leaf :: rest => rest.all fun other => decide (leafSpine other.1 = leafSpine leaf.1)

def allPaths (cut : Cut) (expected : WorldPath) : Bool :=
  cut.all fun leaf => decide (leafPath leaf.1 = expected)

def allSpines (cut : Cut) (expected : List (HeapUpdate Unit Nat Unit)) : Bool :=
  cut.all fun leaf => decide (leafSpine leaf.1 = expected)

/-- A singleton residual agrees with the stored occurrence in the decidable
world, trace, control, and payment fields. Several leaves must share one path
and spine; their traces are not replaced by the first leaf. -/
def cutAgrees (account : ProducerAccount) : Bool :=
  match account.cut with
  | [(leaf, paid)] =>
      decide (leafPath leaf = account.occurrence.state.world.path) &&
        decide (leafSpine leaf = account.occurrence.state.world.heap.spine) &&
        decide ((retained leaf).trace = account.occurrence.trace) &&
        decide ((retained leaf).state.world.receipts.nextSerial =
          account.occurrence.state.world.receipts.nextSerial) &&
        decide ((retained leaf).state.work.transitions =
          account.occurrence.state.work.transitions) &&
        decide ((retained leaf).state.control = account.occurrence.state.control) &&
        decide (paid = account.paidProduction)
  | leaf :: rest =>
      pathsUniform account.cut && spinesUniform account.cut &&
        decide (leafPath leaf.1 = account.occurrence.state.world.path) &&
        decide (leafSpine leaf.1 = account.occurrence.state.world.heap.spine) &&
        rest.all fun other =>
          decide (leafPath other.1 = account.occurrence.state.world.path)
  | [] => false

def checkpoint (expectedPath : WorldPath)
    (expectedSpine : List (HeapUpdate Unit Nat Unit)) (requested : Rights)
    (account : ProducerAccount) : Admit :=
  if account.cut.isEmpty then
    .reject .incompleteResidual account
  else if !pathsUniform account.cut || !spinesUniform account.cut then
    .reject .splitWorlds account
  else if !cutAgrees account then
    .reject .incoherentResidual account
  else if !allPaths account.cut expectedPath then
    .reject .staleWorld account
  else if !allSpines account.cut expectedSpine then
    .reject .changedDependency account
  else if !(decide (operationRights account.cut ⊆ account.rights)) then
    .reject .missingRights account
  else if (restrict? account.rights requested).isNone then
    .reject .missingRights account
  else
    .accept account

def resume (expectedPath : WorldPath) (expectedSpine : List (HeapUpdate Unit Nat Unit))
    (requested : Rights) (account : ProducerAccount) : Admit :=
  match checkpoint expectedPath expectedSpine requested account with
  | .reject reason kept => .reject reason kept
  | .accept _ => .accept (resumeAccount account)

theorem operationRights_of_returned (occurrence : NeedOccurrence) (paid : Nat) :
    operationRights [(.inl occurrence, paid)] = {Right.inspect} := by
  unfold operationRights
  rfl

/-- Acceptance is the conjunction of the cut checks. It is not a separate
soundness field: an empty request still has to hold the operation's rights. -/
theorem checkpoint_accepts_only_a_coherent_cut
    (expectedPath : WorldPath)
    (expectedSpine : List (HeapUpdate Unit Nat Unit))
    (requested : Rights) (account : ProducerAccount)
    (admitted : checkpoint expectedPath expectedSpine requested account = .accept account) :
    account.cut.isEmpty = false ∧
      pathsUniform account.cut = true ∧
      spinesUniform account.cut = true ∧
      cutAgrees account = true ∧
      allPaths account.cut expectedPath = true ∧
      allSpines account.cut expectedSpine = true ∧
      operationRights account.cut ⊆ account.rights ∧
      ∃ granted, restrict? account.rights requested = some granted := by
  unfold checkpoint at admitted
  cases hEmpty : account.cut.isEmpty with
  | true => simp [hEmpty] at admitted
  | false =>
      cases hWorlds : (!pathsUniform account.cut || !spinesUniform account.cut) with
      | true => simp [hEmpty, hWorlds] at admitted
      | false =>
          cases hAgrees : (!cutAgrees account) with
          | true => simp [hEmpty, hWorlds, hAgrees] at admitted
          | false =>
              cases hPaths : (!allPaths account.cut expectedPath) with
              | true => simp [hEmpty, hWorlds, hAgrees, hPaths] at admitted
              | false =>
                  cases hSpines : (!allSpines account.cut expectedSpine) with
                  | true => simp [hEmpty, hWorlds, hAgrees, hPaths, hSpines] at admitted
                  | false =>
                      cases hRights : (!(decide (operationRights account.cut ⊆ account.rights))) with
                      | true =>
                          simp [hEmpty, hWorlds, hAgrees, hPaths, hSpines, hRights] at admitted
                      | false =>
                          cases hRestrict : (restrict? account.rights requested).isNone with
                          | true =>
                              simp [hEmpty, hWorlds, hAgrees, hPaths, hSpines, hRights, hRestrict]
                                at admitted
                          | false =>
                              have pathsHeld : pathsUniform account.cut = true := by
                                cases hp : pathsUniform account.cut with
                                | false =>
                                    exfalso
                                    have contra : true = false := by
                                      have uniform :
                                          (!pathsUniform account.cut ||
                                            !spinesUniform account.cut) = true := by simp [hp]
                                      exact uniform.symm.trans hWorlds
                                    cases contra
                                | true => rfl
                              have spinesHeld : spinesUniform account.cut = true := by
                                cases hs : spinesUniform account.cut with
                                | false =>
                                    exfalso
                                    have contra : true = false := by
                                      have uniform :
                                          (!pathsUniform account.cut ||
                                            !spinesUniform account.cut) = true := by
                                        simp [pathsHeld, hs]
                                      exact uniform.symm.trans hWorlds
                                    cases contra
                                | true => rfl
                              have agreesHeld : cutAgrees account = true := by
                                cases hc : cutAgrees account with
                                | false =>
                                    exfalso
                                    have contra : true = false := by
                                      have negated : (!cutAgrees account) = true := by simp [hc]
                                      exact negated.symm.trans hAgrees
                                    cases contra
                                | true => rfl
                              have pathsExpected : allPaths account.cut expectedPath = true := by
                                cases hc : allPaths account.cut expectedPath with
                                | false =>
                                    exfalso
                                    have contra : true = false := by
                                      have negated : (!allPaths account.cut expectedPath) = true := by
                                        simp [hc]
                                      exact negated.symm.trans hPaths
                                    cases contra
                                | true => rfl
                              have spinesExpected : allSpines account.cut expectedSpine = true := by
                                cases hc : allSpines account.cut expectedSpine with
                                | false =>
                                    exfalso
                                    have contra : true = false := by
                                      have negated :
                                          (!allSpines account.cut expectedSpine) = true := by simp [hc]
                                      exact negated.symm.trans hSpines
                                    cases contra
                                | true => rfl
                              have rightsHeld : operationRights account.cut ⊆ account.rights := by
                                cases hc : decide (operationRights account.cut ⊆ account.rights) with
                                | false =>
                                    exfalso
                                    have contra : true = false := by
                                      have negated :
                                          (!(decide (operationRights account.cut ⊆ account.rights))) =
                                            true := by simp [hc]
                                      exact negated.symm.trans hRights
                                    cases contra
                                | true => exact of_decide_eq_true hc
                              have attenuatedSome :
                                  ∃ granted, restrict? account.rights requested = some granted := by
                                cases hr : restrict? account.rights requested with
                                | none =>
                                    exfalso
                                    have contra : true = false := by
                                      have negated :
                                          (restrict? account.rights requested).isNone = true := by
                                        simp [hr]
                                      exact negated.symm.trans hRestrict
                                    cases contra
                                | some granted => exact ⟨granted, rfl⟩
                              exact ⟨rfl, pathsHeld, spinesHeld, agreesHeld, pathsExpected,
                                spinesExpected, rightsHeld, attenuatedSome⟩

theorem accepted_resume_sequences_the_account
    (expectedPath : WorldPath)
    (expectedSpine : List (HeapUpdate Unit Nat Unit))
    (requested : Rights) (account next : ProducerAccount)
    (admitted : resume expectedPath expectedSpine requested account = .accept next) :
    next = resumeAccount account ∧
      next.ledger = account.ledger ∧
      next.rights = account.rights ∧
      next.demand = account.demand ∧
      next.delivery = account.delivery := by
  unfold resume at admitted
  split at admitted
  · simp at admitted
  · simp only [Admit.accept.injEq] at admitted
    obtain rfl := admitted.symm
    exact ⟨rfl, resume_keeps_ledger_rights_demand_and_delivery account⟩

theorem suspended_cut_is_present :
    ready.cut.isEmpty = false := by
  unfold ready
  have seen := suspension_retains_paid_production
  cases h : suspendedCut.isEmpty with
  | true =>
      rw [List.isEmpty_iff.mp h] at seen
      simp [project] at seen
  | false =>
      exact h

theorem production_spine_is_present :
    decide (CompletedReceiptControls.start.world.heap.spine = []) = false := by
  decide

theorem resume_accepts_the_live_production :
    resume ready.occurrence.state.world.path ready.occurrence.state.world.heap.spine
      {Right.force} ready = .accept (resumeAccount ready) := by
  unfold resume checkpoint
  rfl

theorem stale_world_is_not_refreshed :
    resume [9] ready.occurrence.state.world.heap.spine {Right.force} ready =
      .reject .staleWorld ready := by
  unfold resume checkpoint
  rfl

theorem changed_dependency_is_not_refreshed :
    resume ready.occurrence.state.world.path [] {Right.force} ready =
      .reject .changedDependency ready := by
  unfold resume checkpoint
  rfl

def inspectOnly : ProducerAccount := { ready with rights := {Right.inspect} }

theorem missing_force_is_not_granted :
    resume ready.occurrence.state.world.path ready.occurrence.state.world.heap.spine
      {Right.force} inspectOnly = .reject .missingRights inspectOnly := by
  unfold resume checkpoint inspectOnly
  rfl

/-- The operation needs force because the cut is pending. An empty request
does not supply that right, and attenuation of the empty set does not either. -/
theorem empty_request_does_not_resume_without_force :
    Right.force ∉ inspectOnly.rights ∧
      resume ready.occurrence.state.world.path ready.occurrence.state.world.heap.spine
        ∅ inspectOnly = .reject .missingRights inspectOnly := by
  constructor
  · simp [inspectOnly]
  · unfold resume checkpoint inspectOnly
    rfl

def noResidual : ProducerAccount := { ready with cut := [] }

theorem missing_continuation_is_not_invented :
    resume ready.occurrence.state.world.path ready.occurrence.state.world.heap.spine
      {Right.force} noResidual = .reject .incompleteResidual noResidual := by
  unfold resume checkpoint noResidual
  rfl

theorem refusal_keeps_the_paid_production :
    (resume [9] ready.occurrence.state.world.heap.spine {Right.force} ready).kept.paidProduction =
      ready.paidProduction ∧
    (resume [9] ready.occurrence.state.world.heap.spine {Right.force} ready).kept.cut =
      ready.cut := by
  rw [stale_world_is_not_refreshed]
  exact ⟨rfl, rfl⟩

def foreignOccurrence : NeedOccurrence :=
  { initialOccurrence with
    state := { initialOccurrence.state with
      world := { initialOccurrence.state.world with path := [9] } } }

/-- The stored occurrence keeps the fuel-1 world. The cut leaf does not. -/
def forgedCut : ProducerAccount :=
  { ready with cut := [(.inr foreignOccurrence, 2)] }

theorem pending_cut_world_must_match_the_occurrence :
    foreignOccurrence.state.world.path ≠ forgedCut.occurrence.state.world.path ∧
      checkpoint ready.occurrence.state.world.path ready.occurrence.state.world.heap.spine
        {Right.force} forgedCut = .reject .incoherentResidual forgedCut := by
  constructor
  · unfold forgedCut foreignOccurrence
    decide
  · unfold checkpoint forgedCut
    rfl

def splitWorldCut : ProducerAccount :=
  { ready with
    cut := [(.inr initialOccurrence, 1), (.inr foreignOccurrence, 2)] }

theorem distinct_cut_worlds_are_not_collapsed :
    checkpoint ready.occurrence.state.world.path ready.occurrence.state.world.heap.spine
      {Right.force} splitWorldCut = .reject .splitWorlds splitWorldCut := by
  unfold checkpoint splitWorldCut pathsUniform foreignOccurrence initialOccurrence
  rfl

def returnedInspection : ProducerAccount :=
  { resumeAccount ready with rights := {Right.inspect} }

theorem returned_inspection_does_not_require_force :
    Right.force ∉ returnedInspection.rights ∧
      operationRights returnedInspection.cut = {Right.inspect} ∧
      resume returnedInspection.occurrence.state.world.path
        returnedInspection.occurrence.state.world.heap.spine {Right.inspect}
        returnedInspection = .accept (resumeAccount returnedInspection) := by
  obtain ⟨occurrence, cutEq, _⟩ := resume_adopts_the_completed_production
  refine ⟨?_, ?_, ?_⟩
  · simp [returnedInspection]
  · unfold returnedInspection
    rw [cutEq]
    exact operationRights_of_returned occurrence 2
  · unfold resume checkpoint returnedInspection
    rfl

theorem empty_request_can_inspect_a_returned_cut :
    resume returnedInspection.occurrence.state.world.path
      returnedInspection.occurrence.state.world.heap.spine ∅ returnedInspection =
      .accept (resumeAccount returnedInspection) := by
  unfold resume checkpoint returnedInspection
  rfl

/-! ## Scalar projection -/

inductive GroundKind where
  | int
  | float
  | bool
  | string
  | bigint
  | rational
  deriving DecidableEq, Repr

/-- The native scalar rendezvous can carry a grounded kind and a token.
It has no production coefficient, Need world, rights, dependency spine, or
ownership graph. -/
structure ScalarPacket where
  kind : GroundKind
  token : Nat
  demandSlot : Nat
  deriving DecidableEq, Repr

def forgottenScalar (account : ProducerAccount) : ScalarPacket :=
  ⟨.int, 21, account.demand.slot⟩

def scalarBlocked (account : ProducerAccount) : Bool :=
  !account.delivery.log.rows.isEmpty ||
    (account.delivery.published != ∅) ||
    (account.paidProduction != 0) ||
    !account.occurrence.trace.isEmpty ||
    (account.rights != ∅) ||
    (account.occurrence.state.world.receipts.nextSerial != 0) ||
    !account.occurrence.state.world.path.isEmpty ||
    !account.occurrence.state.world.heap.spine.isEmpty

/-- Refusal control. This module does not encode or decode a scalar packet. -/
def scalarPacket? (_account : ProducerAccount) : Option ScalarPacket :=
  none

theorem scalar_publication_is_refused (account : ProducerAccount) :
    scalarPacket? account = none := rfl

/-- Retention tag. It does not publish, decode, or install the account. -/
def retainAccount (account : ProducerAccount) : ProducerAccount :=
  account

theorem retention_is_not_a_scalar_publication (account : ProducerAccount) :
    retainAccount account = account ∧ scalarPacket? account = none := by
  constructor <;> rfl

def unpaid : ProducerAccount := { ready with paidProduction := 0 }

theorem forgotten_scalar_identifies_different_payments :
    forgottenScalar unpaid = forgottenScalar ready ∧
      unpaid.paidProduction = 0 ∧ ready.paidProduction = 2 := by
  exact ⟨rfl, rfl, suspension_payment_is_ready.2.1⟩

theorem paid_production_blocks_the_scalar :
    scalarBlocked ready = true ∧ scalarPacket? ready = none := by
  constructor
  · decide
  · rfl

theorem ownership_rows_block_an_unpaid_scalar :
    scalarBlocked unpaid = true ∧ scalarPacket? unpaid = none := by
  constructor
  · decide
  · rfl

/-! ## Source order -/

inductive Proposal where
  | admitted (order : List Nat)
  | unqualified (proposed : List Nat)
  deriving DecidableEq, Repr

/-- A singleton cut admits its trace only when that trace is the stored
occurrence trace. Several leaves do not yield one trace. -/
def admittedTrace? (account : ProducerAccount) : Option (List Nat) :=
  match account.cut with
  | [(leaf, _)] =>
      if decide ((retained leaf).trace = account.occurrence.trace) then
        some account.occurrence.trace
      else none
  | _ => none

/-- A list is an admitted demand order only when it is that singleton trace.
Any other list is an unqualified proposal. -/
def award (account : ProducerAccount) (proposed : List Nat) : Proposal :=
  match admittedTrace? account with
  | some trace => if proposed = trace then .admitted trace else .unqualified proposed
  | none => .unqualified proposed

/-- No installer is defined. Classification retains the account. -/
def retainProposal (account : ProducerAccount) (_proposal : Proposal) : ProducerAccount :=
  account

theorem proposal_retention_does_not_install (account : ProducerAccount) (proposal : Proposal) :
    retainProposal account proposal = account := rfl

theorem supplied_finish_order_is_unqualified :
    award ready [9, 1] = .unqualified [9, 1] := by
  unfold award admittedTrace?
  decide

theorem fuel1_trace_is_retained :
    award ready [0] = .admitted [0] ∧ retainProposal ready (.admitted [0]) = ready := by
  constructor
  · unfold award admittedTrace?
    decide
  · rfl

theorem resumed_trace_rejects_a_supplied_finish_order :
    award (resumeAccount ready) [9, 1] = .unqualified [9, 1] ∧
      retainProposal (resumeAccount ready) (.unqualified [9, 1]) = resumeAccount ready := by
  obtain ⟨occurrence, _, occEq, _, trace, _, _, _, _⟩ := resume_adopts_the_completed_production
  refine ⟨?_, ?_⟩
  · unfold award admittedTrace?
    rw [occEq, trace]
    decide
  · rfl

/-! ## Realization of this production

The ledger and the three-node delivery cycle are carried beside the Need cut.
The cycle's addresses are not cells of the Need heap. After the commit step
the pending control no longer exposes that cell, so the demand is the commit
cell retained by the occurrence spine. This is one instance. It is not a
`ResourceOwnership` census of an arbitrary returned payload.
-/

/-- The commit cell still occurs in the retained heap spine. -/
def spineMentionsDemand (account : ProducerAccount) : Bool :=
  account.occurrence.state.world.heap.spine.any fun update =>
    decide (HeapUpdate.cell update = account.demand)

theorem ready_realization :
    ready.paidProduction = 2 ∧
      ready.occurrence.trace = [0] ∧
      ready.demand = readyDemand ∧
      operationRights ready.cut = {Right.force} ∧
      operationRights ready.cut ⊆ ready.rights ∧
      spineMentionsDemand ready = true ∧
      ready.ledger.Supported := by
  refine ⟨suspension_payment_is_ready.2.1, suspension_payment_is_ready.2.2.1, rfl, ?_, ?_, ?_,
    inherited_supported⟩
  · unfold operationRights ready
    rfl
  · unfold operationRights ready
    decide
  · unfold spineMentionsDemand ready
    decide

theorem resumed_realization :
    (resumeAccount ready).paidProduction = 2 ∧
      (resumeAccount ready).occurrence.trace = List.replicate 10 0 ∧
      operationRights (resumeAccount ready).cut = {Right.inspect} ∧
      operationRights (resumeAccount ready).cut ⊆ (resumeAccount ready).rights ∧
      (resumeAccount ready).ledger = ready.ledger ∧
      (resumeAccount ready).demand = ready.demand ∧
      spineMentionsDemand (resumeAccount ready) = true := by
  obtain ⟨occurrence, cutEq, occEq, paidEq, trace, _, _, _, _⟩ :=
    resume_adopts_the_completed_production
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [paidEq]
    exact suspension_payment_is_ready.2.1
  · rw [occEq]
    exact trace
  · rw [cutEq]
    exact operationRights_of_returned occurrence 2
  · have rights : (resumeAccount ready).rights = {Right.force, Right.inspect} := by
      unfold resumeAccount
      rfl
    rw [cutEq, operationRights_of_returned occurrence 2, rights]
    decide
  · exact (resume_keeps_ledger_rights_demand_and_delivery ready).1
  · exact (resume_keeps_ledger_rights_demand_and_delivery ready).2.2.1
  · unfold spineMentionsDemand
    decide

/-! ## Recorded heap agreement

`cutAgrees` and `spinesUniform` compare `heap.spine` only. `Heap.current` is
a function, so two heaps can share that history and still differ. Checkpoint
has no `Recorded` proof field: erasing every current lookup of the paid
singleton keeps the spine and is still accepted, and `Recorded` fails at cell
`(1, [], 0, 0)`. That is the regression. `Heap.eq_of_spine_eq` gives heap
agreement only for recorded heaps. The receipt heap is rebuilt with
`Heap.empty`, `Heap.allocate?`, and `Heap.setKnownCache`, and the real
contribution run preserves `Recorded`. Callers do not assert that invariant.
-/

section RecordedHeaps

open Mettapedia.Machines.BranchLocalNeed.NeedReference.Heap

abbrev NeedHeap :=
  Mettapedia.Machines.BranchLocalNeed.NeedReference.Heap Unit Nat Unit

abbrev NeedCache :=
  Mettapedia.Machines.BranchLocalNeed.NeedReference.Cache Nat Unit

/-- The suspended record written by allocating the commit cell in an empty heap. -/
def allocatedProductionHeap : NeedHeap :=
  { current := Function.update (fun _ => none) readyDemand (some ⟨(), .suspended⟩)
    spine := [.allocate readyDemand ()] }

/-- Allocation, then the known cache replacement of that same suspended record. -/
def recordedProductionHeap (cache : NeedCache) : NeedHeap :=
  allocatedProductionHeap.setKnownCache readyDemand ⟨(), .suspended⟩ cache

theorem production_heap_allocates :
    (empty : NeedHeap).allocate? readyDemand () = some allocatedProductionHeap := by
  unfold allocate? lookup allocatedProductionHeap empty
  rfl

theorem allocated_production_is_recorded : allocatedProductionHeap.Recorded :=
  allocate?_recorded empty allocatedProductionHeap empty_recorded readyDemand ()
    production_heap_allocates

theorem recorded_production_heap_is_recorded (cache : NeedCache) :
    (recordedProductionHeap cache).Recorded :=
  setKnownCache_recorded allocatedProductionHeap allocated_production_is_recorded
    readyDemand ⟨(), .suspended⟩ (allocate?_lookup_same production_heap_allocates) cache

theorem recorded_production_lookup (cache : NeedCache) (queried : CellId) :
    (recordedProductionHeap cache).lookup queried =
      if queried = readyDemand then some ⟨(), cache⟩ else none := by
  simp only [recordedProductionHeap, allocatedProductionHeap, setKnownCache, lookup,
    Function.update_apply]
  by_cases same : queried = readyDemand
  · simp [same]
  · simp [same]

theorem production_start_spine :
    CompletedReceiptControls.start.world.heap.spine =
      (recordedProductionHeap (.evaluating 3)).spine := by
  rfl

theorem production_start_lookup (queried : CellId) :
    CompletedReceiptControls.start.world.heap.lookup queried =
      if queried = readyDemand then some ⟨(), .evaluating 3⟩ else none := by
  rfl

theorem production_start_is_recorded :
    CompletedReceiptControls.start.world.heap.Recorded := by
  intro queried
  rw [production_start_lookup queried]
  have recorded := recorded_production_heap_is_recorded (.evaluating 3) queried
  rw [recorded_production_lookup (.evaluating 3) queried] at recorded
  rw [← production_start_spine] at recorded
  exact recorded

theorem production_start_heap_is_the_recorded_heap :
    CompletedReceiptControls.start.world.heap = recordedProductionHeap (.evaluating 3) :=
  eq_of_spine_eq _ _ production_start_is_recorded
    (recorded_production_heap_is_recorded _) production_start_spine

/-- The finite spine comparison accepts a heap whose current map was erased.
Equality needs `Recorded` on both sides, which this erasure lacks. -/
def wipedProductionCurrent : NeedHeap :=
  { recordedProductionHeap (.evaluating 3) with current := fun _ => none }

theorem matching_spine_does_not_determine_the_current :
    sameRecordedSpine wipedProductionCurrent (recordedProductionHeap (.evaluating 3)) = true ∧
      wipedProductionCurrent.spine = (recordedProductionHeap (.evaluating 3)).spine ∧
      wipedProductionCurrent ≠ recordedProductionHeap (.evaluating 3) ∧
      ¬ wipedProductionCurrent.Recorded ∧
      CompletedReceiptControls.start.world.heap = recordedProductionHeap (.evaluating 3) ∧
      CompletedReceiptControls.start.world.heap.Recorded := by
  refine ⟨?_, rfl, ?_, ?_, production_start_heap_is_the_recorded_heap,
    production_start_is_recorded⟩
  · unfold sameRecordedSpine
    exact decide_eq_true rfl
  · intro same
    have lookupEq :=
      congrArg (fun heap : NeedHeap => heap.lookup readyDemand) same
    have wipedNone : wipedProductionCurrent.lookup readyDemand = none := rfl
    have kept : (recordedProductionHeap (.evaluating 3)).lookup readyDemand =
        some ⟨(), .evaluating 3⟩ := by
      simpa using recorded_production_lookup (.evaluating 3) readyDemand
    rw [wipedNone, kept] at lookupEq
    cases lookupEq
  · intro recorded
    have observed := recorded readyDemand
    have wipedNone : wipedProductionCurrent.lookup readyDemand = none := rfl
    rw [wipedNone] at observed
    have spineEq : wipedProductionCurrent.spine =
        (recordedProductionHeap (.evaluating 3)).spine := rfl
    rw [spineEq] at observed
    have someLookup : lookupSpine (recordedProductionHeap (.evaluating 3)).spine readyDemand =
        some ⟨(), .evaluating 3⟩ := by
      have valid := recorded_production_heap_is_recorded (.evaluating 3) readyDemand
      have lookupEq := recorded_production_lookup (.evaluating 3) readyDemand
      simp at lookupEq
      rw [← valid, lookupEq]
    rw [someLookup] at observed
    cases observed

/-- Regression: the paid singleton stays accepted after every `heap.current`
lookup is erased. The expected path and spine are the real receipt's.
Checkpoint does not carry a `Recorded` obligation. -/
def eraseCurrent (occurrence : NeedOccurrence) : NeedOccurrence :=
  { occurrence with
      state := { occurrence.state with
        world := { occurrence.state.world with
          heap := { occurrence.state.world.heap with current := fun _ => none } } } }

def erasedCurrentAccount : ProducerAccount :=
  { ready with
      occurrence := eraseCurrent ready.occurrence
      cut := ready.cut.map fun leaf => (Sum.map eraseCurrent eraseCurrent leaf.1, leaf.2) }

theorem erased_current_singleton_is_admitted :
    (match checkpoint ready.occurrence.state.world.path
        ready.occurrence.state.world.heap.spine {Right.force} erasedCurrentAccount with
      | .accept _ => true
      | .reject _ _ => false) = true := by
  rfl

theorem erased_current_fails_recorded_at_the_commit_cell :
    ¬ erasedCurrentAccount.occurrence.state.world.heap.Recorded := by
  intro recorded
  have mismatch := congrArg Option.isSome (recorded ⟨1, [], 0, 0⟩)
  change false = true at mismatch
  cases mismatch

theorem initial_occurrence_is_recorded :
    initialOccurrence.state.world.heap.Recorded := by
  simpa [initialOccurrence] using production_start_is_recorded

/-- Returned and suspended leaves of this source keep a recorded heap.
The successor step is `step_heap_recorded`, whose cache case is
`setKnownCache_recorded` and whose allocation case is `allocate?_recorded`. -/
theorem production_contributions_stay_recorded (fuel : Nat) (occurrence : NeedOccurrence)
    (valid : occurrence.state.world.heap.Recorded) :
    ∀ leaf ∈ contributions productionSource fuel occurrence,
      (retained leaf.1).state.world.heap.Recorded := by
  intro leaf member
  have preserved :=
    contributions_invariant productionSource
      (fun state => state.state.world.heap.Recorded)
      (fun state => state.state.world.heap.Recorded)
      (fun state answer valid returned => by
        have returnedSource :
            source CompletedReceiptControls.spec
              (productionCoefficient (fun _ => (2 : Nat))) state = .inl answer := by
          simpa [productionSource] using returned
        obtain ⟨same, _⟩ :=
          (source_return_iff CompletedReceiptControls.spec
            (productionCoefficient (fun _ => (2 : Nat))) state answer).mp returnedSource
        cases same
        exact valid)
      (fun state alternatives valid branched next nextMember => by
        have branchedSource :
            source CompletedReceiptControls.spec
              (productionCoefficient (fun _ => (2 : Nat))) state = .inr alternatives := by
          simpa [productionSource] using branched
        have notHalted : isHalted state.state = false := by
          cases control : state.state.control with
          | halted _ =>
              simp only [source, control] at branchedSource
              exact False.elim (Sum.inl_ne_inr branchedSource)
          | force _ _ =>
              unfold isHalted
              rw [control]
          | run _ _ =>
              unfold isHalted
              rw [control]
          | returned _ _ =>
              unfold isHalted
              rw [control]
        have running :=
          source_branches CompletedReceiptControls.spec
            (productionCoefficient (fun _ => (2 : Nat))) state notHalted
        have successorsEq :
            successors CompletedReceiptControls.spec
              (productionCoefficient (fun _ => (2 : Nat))) state = alternatives := by
          have joined := running.symm.trans branchedSource
          injection joined
        rw [← successorsEq] at nextMember
        obtain ⟨index, found, _trace, _value⟩ :=
          (successor_iff CompletedReceiptControls.spec
            (productionCoefficient (fun _ => (2 : Nat))) state next.1 next.2).mp nextMember
        exact step_heap_recorded CompletedReceiptControls.spec state.state next.1.state valid
          (List.mem_of_getElem? found))
      fuel occurrence valid leaf member
  cases leaf with
  | mk which _coeff =>
      cases which with
      | inl answer => exact preserved
      | inr pending => exact preserved

theorem ready_cut_is_suspended : ready.cut = suspendedCut := by
  unfold ready
  rfl

theorem ready_is_the_suspended_leaf :
    ready.cut = [(.inr ready.occurrence, ready.paidProduction)] := by
  unfold ready adopt
  rfl

theorem resumed_cut_is_the_receipt_run :
    (resumeAccount ready).cut =
      contributions productionSource (1 + 10) initialOccurrence := by
  have cutEq : (resumeAccount ready).cut = sequenceCut suspendedCut := by
    unfold resumeAccount ready
    rfl
  exact cutEq.trans sequence_is_the_eleven_step_run

theorem ready_heap_is_recorded : ready.occurrence.state.world.heap.Recorded := by
  have member : (.inr ready.occurrence, ready.paidProduction) ∈
      contributions productionSource 1 initialOccurrence := by
    rw [← suspendedCut, ← ready_cut_is_suspended, ready_is_the_suspended_leaf]
    exact List.mem_singleton_self _
  have recorded :=
    production_contributions_stay_recorded 1 initialOccurrence initial_occurrence_is_recorded
      _ member
  simpa [retained] using recorded

theorem erased_current_is_not_the_receipt_occurrence :
    erasedCurrentAccount.occurrence.state.world.heap ≠ ready.occurrence.state.world.heap := by
  intro same
  exact erased_current_fails_recorded_at_the_commit_cell <| by
    rw [same]
    exact ready_heap_is_recorded

theorem resumed_heap_is_recorded :
    (resumeAccount ready).occurrence.state.world.heap.Recorded := by
  obtain ⟨occurrence, cutEq, occEq, _paid, _trace, _transitions, _serial, _ledger, _delivery⟩ :=
    resume_adopts_the_completed_production
  have member : (.inl occurrence, 2) ∈ contributions productionSource (1 + 10) initialOccurrence := by
    rw [← resumed_cut_is_the_receipt_run, cutEq]
    exact List.mem_singleton_self _
  have recorded :=
    production_contributions_stay_recorded (1 + 10) initialOccurrence initial_occurrence_is_recorded
      _ member
  simpa [retained, occEq] using recorded

theorem receipt_run_preserves_recorded_heaps :
    CompletedReceiptControls.start.world.heap.Recorded ∧
      initialOccurrence.state.world.heap.Recorded ∧
      ready.occurrence.state.world.heap.Recorded ∧
      (∀ leaf ∈ ready.cut, (retained leaf.1).state.world.heap.Recorded) ∧
      (resumeAccount ready).occurrence.state.world.heap.Recorded ∧
      (∀ leaf ∈ (resumeAccount ready).cut,
        (retained leaf.1).state.world.heap.Recorded) := by
  refine ⟨production_start_is_recorded, initial_occurrence_is_recorded, ready_heap_is_recorded, ?_,
    resumed_heap_is_recorded, ?_⟩
  · intro leaf member
    exact production_contributions_stay_recorded 1 initialOccurrence initial_occurrence_is_recorded
      leaf (by simpa [suspendedCut, ready_cut_is_suspended] using member)
  · intro leaf member
    exact production_contributions_stay_recorded (1 + 10) initialOccurrence
      initial_occurrence_is_recorded leaf (by simpa [resumed_cut_is_the_receipt_run] using member)

/-- Spine uniformity in an accepted cut is heap equality once every retained
heap and the stored heap are recorded. The checkpoint Boolean does not decide
`heap.current`. -/
theorem cut_leaf_spines_match_the_stored_spine (account : ProducerAccount)
    (uniform : spinesUniform account.cut = true) (agrees : cutAgrees account = true) :
    ∀ leaf ∈ account.cut, leafSpine leaf.1 = account.occurrence.state.world.heap.spine := by
  cases hcut : account.cut with
  | nil =>
      exfalso
      have contra : true = false := by
        simpa [spinesUniform, hcut] using uniform.symm
      cases contra
  | cons first rest =>
      cases first with
      | mk sum paid =>
          cases rest with
          | nil =>
              have chain := agrees
              simp only [cutAgrees, hcut] at chain
              have dropPaid := (Bool.and_eq_true_iff.mp chain).1
              have dropControl := (Bool.and_eq_true_iff.mp dropPaid).1
              have dropTransitions := (Bool.and_eq_true_iff.mp dropControl).1
              have dropSerial := (Bool.and_eq_true_iff.mp dropTransitions).1
              have dropTrace := (Bool.and_eq_true_iff.mp dropSerial).1
              have firstSpine :=
                decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp dropTrace).2
              intro leaf leafMember
              have leafEq : leaf = (sum, paid) := by
                simpa [hcut] using List.mem_singleton.mp leafMember
              cases leafEq
              exact firstSpine
          | cons second more =>
              have chain := agrees
              simp only [cutAgrees, hcut] at chain
              have dropAll := (Bool.and_eq_true_iff.mp chain).1
              have firstSpine :=
                decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp dropAll).2
              have others : ∀ other ∈ second :: more,
                  leafSpine other.1 = leafSpine sum := by
                intro other otherMember
                have uniformAll :
                    (second :: more).all
                      (fun other => decide (leafSpine other.1 = leafSpine sum)) = true := by
                  simpa [spinesUniform, hcut] using uniform
                exact decide_eq_true_eq.mp
                  ((List.all_eq_true.mp uniformAll) other otherMember)
              intro leaf leafMember
              have memberEq : leaf = (sum, paid) ∨ leaf ∈ second :: more := by
                simpa [hcut] using List.mem_cons.mp leafMember
              cases memberEq with
              | inl headEq =>
                  cases headEq
                  exact firstSpine
              | inr tailMember =>
                  exact (others leaf tailMember).trans firstSpine

theorem admitted_recorded_leaves_share_the_stored_heap
    (expectedPath : WorldPath)
    (expectedSpine : List (HeapUpdate Unit Nat Unit))
    (requested : Rights) (account : ProducerAccount)
    (admitted : checkpoint expectedPath expectedSpine requested account = .accept account)
    (stored : account.occurrence.state.world.heap.Recorded)
    (leaves : ∀ leaf ∈ account.cut, (retained leaf.1).state.world.heap.Recorded) :
    ∀ leaf ∈ account.cut,
      (retained leaf.1).state.world.heap = account.occurrence.state.world.heap := by
  obtain ⟨_nonempty, _paths, spinesHeld, agreesHeld, _expectedPaths, _expectedSpines, _rights,
      _attenuated⟩ :=
    checkpoint_accepts_only_a_coherent_cut expectedPath expectedSpine requested account admitted
  intro leaf member
  exact eq_of_spine_eq _ _ (leaves leaf member) stored
    (cut_leaf_spines_match_the_stored_spine account spinesHeld agreesHeld leaf member)

theorem ready_recorded_leaves_share_the_stored_heap :
    ∀ leaf ∈ ready.cut,
      (retained leaf.1).state.world.heap = ready.occurrence.state.world.heap := by
  exact admitted_recorded_leaves_share_the_stored_heap
    ready.occurrence.state.world.path ready.occurrence.state.world.heap.spine
    {Right.force} ready (by unfold checkpoint; rfl) ready_heap_is_recorded
    (fun leaf member =>
      production_contributions_stay_recorded 1 initialOccurrence initial_occurrence_is_recorded
        leaf (by simpa [suspendedCut, ready_cut_is_suspended] using member))

theorem resumed_recorded_leaves_share_the_stored_heap :
    ∀ leaf ∈ (resumeAccount ready).cut,
      (retained leaf.1).state.world.heap =
        (resumeAccount ready).occurrence.state.world.heap := by
  exact admitted_recorded_leaves_share_the_stored_heap
    (resumeAccount ready).occurrence.state.world.path
    (resumeAccount ready).occurrence.state.world.heap.spine
    {Right.inspect} (resumeAccount ready) (by unfold checkpoint; rfl) resumed_heap_is_recorded
    (fun leaf member =>
      production_contributions_stay_recorded (1 + 10) initialOccurrence
        initial_occurrence_is_recorded leaf
        (by simpa [resumed_cut_is_the_receipt_run] using member))

end RecordedHeaps

/-! ## Separate ownership representation

These facts are about `Controls.sharedCycle`. That cycle is a representation
control. It is not a census of Need payload roots, and it does not qualify
general ownership.
-/

theorem compound_delivery_is_well_formed : WellFormed cyclicHeap ready.delivery := by
  have delivery : ready.delivery = Controls.sharedCycle := rfl
  refine ⟨?_, ?_⟩
  · simpa [delivery] using Controls.sharedCycle_valid
  · intro _ _
    exact Finset.mem_univ _

theorem compound_row_is_not_the_reachable_graph :
    unread ready.delivery.log 0 = [0, 0] ∧
      unread ready.delivery.log 1 = [0, 0] ∧
      rootAddresses (logRoots Nat ready.delivery.log) = {0} ∧
      (1 : Fin 3) ∈ census cyclicHeap (logRoots Nat ready.delivery.log) ∧
      (2 : Fin 3) ∈ census cyclicHeap (logRoots Nat ready.delivery.log) := by
  decide

theorem cancel_drops_only_that_consumers_rows :
    unread (cancelConsumer ready.delivery 0).log 0 = [] ∧
      unread (cancelConsumer ready.delivery 0).log 1 = [0, 0] := by
  decide

theorem cancel_keeps_the_other_reachable_cycle (location : Fin 3) :
    (collect cyclicHeap (roots (trimLog (cancelConsumer ready.delivery 0)))).lookup location =
      cyclicHeap.lookup location := by
  have delivery : ready.delivery = Controls.sharedCycle := rfl
  simpa [delivery] using Controls.cancellation_keeps_the_other_consumers_cycle location

theorem resume_keeps_the_other_consumers_graph (location : Fin 3) :
    (collect cyclicHeap
      (roots (trimLog (cancelConsumer (resumeAccount ready).delivery 0)))).lookup location =
      cyclicHeap.lookup location := by
  have same := (resume_keeps_ledger_rights_demand_and_delivery ready).2.2.2
  simpa [same] using cancel_keeps_the_other_reachable_cycle location

/-! ## Ledger representation controls

These equalities concern the ordered coefficient ledger carried beside the
Need cut. They do not earn the production coefficient `2`.
-/

theorem nonprefix_shared_factor_is_refused :
    merge? inheritedLedger [otherFactor, sharedFactor] = none := by
  decide

theorem source_order_is_not_finish_order :
    denote inheritedLedger = ⟨[1, 9]⟩ ∧
      denote [sharedFactor, prefixFactor] = ⟨[9, 1]⟩ := by
  decide

theorem inherited_claim_is_supported :
    inherited.claims 7 = some 0 ∧ inherited.Supported :=
  ⟨by decide, inherited_supported⟩

theorem second_observation_selects_nothing :
    Scoped.selectedSince [] (Scoped.handleSince [] 1 inherited) = [] :=
  Scoped.selectedSince_after_handle [] 1 inherited

theorem inherited_claim_survives_the_second_read :
    (Scoped.handleSince [] 1 inherited).claims 7 = some 0 :=
  Scoped.handleSince_prior_claim_preserved [] 1 inherited (by decide)

theorem conflicting_owners_are_refused :
    Scoped.merge? inherited rival = none :=
  Scoped.conflicting_claims_refused inherited rival rival_supported
    (identity := 7) (first := 0) (second := 1)
    (by decide) (by decide) (by decide)

/-! ## Worlds -/

def forked (branch : Nat) : NeedMachine :=
  { CompletedReceiptControls.start with
    world := CompletedReceiptControls.start.world.fork branch }

def accountAt (machine : NeedMachine) : ProducerAccount :=
  { ready with occurrence := ⟨machine, []⟩, paidProduction := 0, cut := [] }

/-- Path comparison only. An empty cut is not an admitted production. -/
def joinWorld? (left right : ProducerAccount) : Option WorldPath :=
  let leftPath := left.occurrence.state.world.path
  let rightPath := right.occurrence.state.world.path
  if leftPath = rightPath then some leftPath else none

theorem forked_worlds_stay_separate :
    (forked 0).world.path = [0] ∧ (forked 1).world.path = [1] ∧
      joinWorld? (accountAt (forked 0)) (accountAt (forked 1)) = none ∧
      (accountAt (forked 1)).paidProduction = 0 ∧
      (accountAt (forked 1)).cut = [] ∧
      ready.paidProduction = 2 := by
  refine ⟨?_, ?_, ?_, rfl, rfl, suspension_payment_is_ready.2.1⟩
  · unfold forked World.fork
    rw [production_starts_without_receipts.1]
    rfl
  · unfold forked World.fork
    rw [production_starts_without_receipts.1]
    rfl
  · unfold joinWorld? accountAt forked World.fork
    rw [production_starts_without_receipts.1]
    rfl

theorem empty_cut_is_not_admitted (machine : NeedMachine) :
    checkpoint (accountAt machine).occurrence.state.world.path
      (accountAt machine).occurrence.state.world.heap.spine
      {Right.force} (accountAt machine) =
      .reject .incompleteResidual (accountAt machine) := by
  unfold checkpoint accountAt
  rfl

def sameWorldSibling : ProducerAccount :=
  { ready with
    occurrence := ⟨{ CompletedReceiptControls.start with control := .force readyDemand [] }, []⟩ }

theorem fuel1_path_is_the_source_world :
    ready.occurrence.state.world.path = [] := by
  unfold ready adopt
  rfl

theorem same_world_join_does_not_merge_controls :
    joinWorld? ready sameWorldSibling = some [] ∧
      ready.occurrence.state.world.path = sameWorldSibling.occurrence.state.world.path ∧
      ready.occurrence.state.control ≠ sameWorldSibling.occurrence.state.control ∧
      ready.paidProduction = sameWorldSibling.paidProduction ∧
      checkpoint ready.occurrence.state.world.path ready.occurrence.state.world.heap.spine
        {Right.force, Right.inspect} sameWorldSibling =
        .reject .incoherentResidual sameWorldSibling := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · unfold joinWorld? sameWorldSibling
    rw [fuel1_path_is_the_source_world, production_starts_without_receipts.1]
    rfl
  · rw [fuel1_path_is_the_source_world]
    unfold sameWorldSibling
    rw [production_starts_without_receipts.1]
  · unfold sameWorldSibling
    decide
  · unfold checkpoint sameWorldSibling
    rfl

/-! ## Live payload roots

The Nat receipt value does not carry two occurrences of a demand. This
source returns `Val.app (Val.need shared) (Val.need shared)`. The shared
cell's origin is the binding cell. Both facts are read back from the run.
`ReferenceInventory` builds the resource heap only for a recorded, closed
machine. The consumer log's rows are the value's occurrence list, so the
two positions share one address. `sharedCycle` is not an input.
-/

section LiveRoots

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
open Mettapedia.Machines.BranchLocalNeed.NeedReference.Heap
open Mettapedia.Machines.Cursor.OwnedLifecycle (answerRoots)

inductive PayloadOrigin where
  | symbol (name : Nat)
  | capture (binding : CellId) (name : Nat)
  deriving DecidableEq, Repr

inductive PayloadRule where
  | left
  | right
  deriving DecidableEq, Repr

inductive PayloadResume where
  | afterBinding
  | afterShared (binding : CellId)
  | afterDemand (shared : CellId)
  deriving DecidableEq, Repr

inductive PayloadLocal where
  | start
  | gotBinding (binding : CellId)
  | gotShared (shared : CellId)
  | finish (shared : CellId)
  | emit (name : Nat)
  deriving DecidableEq, Repr

abbrev PayloadMachine :=
  Machine PayloadOrigin PayloadLocal PayloadResume PayloadRule (Val CellId) Unit Unit Unit

abbrev PayloadOccurrence := WorkOccurrence PayloadMachine

abbrev PayloadCut := List ((PayloadOccurrence ⊕ PayloadOccurrence) × Nat)

abbrev PayloadCache :=
  Mettapedia.Machines.BranchLocalNeed.NeedReference.Cache (Val CellId) Unit

abbrev PayloadCell :=
  Mettapedia.Machines.BranchLocalNeed.NeedReference.CellRecord
    PayloadOrigin (Val CellId) Unit

/-- The payload account carries the occurrence, rights, demand, payment, and
cut. It has no `Recorded` field, no root inventory, and no world-join field.
`delivery` on the Nat account stays the separate cycle. -/
structure PayloadAccount where
  occurrence : PayloadOccurrence
  rights : Rights
  demand : CellId
  paidProduction : Nat
  cut : PayloadCut

def payloadSpec :
    Spec PayloadOrigin PayloadLocal PayloadResume PayloadRule (Val CellId) Unit Unit Unit where
  alternatives
    | .symbol name => [(.left, .emit name)]
    | .capture _ name => [(.left, .emit name), (.right, .emit (name + 1))]
  action
    | .start => .allocate (.symbol 8) .afterBinding
    | .gotBinding binding => .allocate (.capture binding 5) (.afterShared binding)
    | .gotShared shared => .demand shared (.afterDemand shared)
    | .finish shared => .done (.value (.app (.need shared) (.need shared)))
    | .emit name => .done (.value (.sym name))
  afterDemand
    | .afterDemand shared, _ => .finish shared
    | .afterBinding, _ => .start
    | .afterShared _, _ => .start
  afterAllocation
    | .afterBinding, cell => .gotBinding cell
    | .afterShared _, cell => .gotShared cell
    | .afterDemand _, cell => .gotShared cell

def originRefs : PayloadOrigin → Finset CellId
  | .symbol _ => ∅
  | .capture cell _ => {cell}

def localRefs : PayloadLocal → Finset CellId
  | .start | .emit _ => ∅
  | .gotBinding cell | .gotShared cell | .finish cell => {cell}

def resumeRefs : PayloadResume → Finset CellId
  | .afterBinding => ∅
  | .afterShared cell | .afterDemand cell => {cell}

def originHolds (p : CellId → Prop) (origin : PayloadOrigin) : Prop :=
  ∀ cell ∈ originRefs origin, p cell

def localHolds (p : CellId → Prop) (state : PayloadLocal) : Prop :=
  ∀ cell ∈ localRefs state, p cell

def resumeHolds (p : CellId → Prop) (token : PayloadResume) : Prop :=
  ∀ cell ∈ resumeRefs token, p cell

def valueHolds (p : CellId → Prop) (value : Val CellId) : Prop :=
  ∀ cell ∈ value.referenceSet, p cell

def payloadDiscipline : ReferenceDiscipline payloadSpec where
  origin := originHolds
  localState := localHolds
  resume := resumeHolds
  value := valueHolds
  origin_mono := by
    intro p q grows origin held cell member
    exact grows cell (held cell member)
  local_mono := by
    intro p q grows state held cell member
    exact grows cell (held cell member)
  resume_mono := by
    intro p q grows token held cell member
    exact grows cell (held cell member)
  value_mono := by
    intro p q grows value held cell member
    exact grows cell (held cell member)
  alternatives := by
    intro p origin rule state _held member
    cases origin with
    | symbol name =>
        simp [payloadSpec] at member
        obtain ⟨rfl, rfl⟩ := member
        simp [localHolds, localRefs]
    | capture _binding name =>
        simp [payloadSpec] at member
        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        all_goals simp [localHolds, localRefs]
  action := by
    intro p state held
    cases state with
    | start =>
        simp [payloadSpec, originHolds, originRefs, resumeHolds, resumeRefs]
    | gotBinding binding =>
        have bindingHeld : p binding := by
          simpa [localHolds, localRefs, Finset.mem_singleton] using held
        suffices originHolds p (.capture binding 5) ∧
            resumeHolds p (.afterShared binding) by
          simpa [payloadSpec] using this
        exact ⟨by simpa [originHolds, originRefs, Finset.mem_singleton] using bindingHeld,
          by simpa [resumeHolds, resumeRefs, Finset.mem_singleton] using bindingHeld⟩
    | gotShared shared =>
        have sharedHeld : p shared := by
          simpa [localHolds, localRefs, Finset.mem_singleton] using held
        suffices p shared ∧ resumeHolds p (.afterDemand shared) by
          simpa [payloadSpec] using this
        exact ⟨sharedHeld,
          by simpa [resumeHolds, resumeRefs, Finset.mem_singleton] using sharedHeld⟩
    | finish shared =>
        have sharedHeld : p shared := by
          simpa [localHolds, localRefs, Finset.mem_singleton] using held
        suffices valueHolds p (.app (.need shared) (.need shared)) by
          simpa [payloadSpec] using this
        intro cell member
        simp only [Val.referenceSet, Finset.mem_union, Finset.mem_singleton] at member
        rcases member with rfl | rfl <;> exact sharedHeld
    | emit _name =>
        simp [payloadSpec, valueHolds, Val.referenceSet]
  afterDemand := by
    intro p token outcome held _outcomeHeld
    cases token with
    | afterBinding =>
        cases outcome <;> simp [payloadSpec, localHolds, localRefs]
    | afterShared _ =>
        cases outcome <;> simp [payloadSpec, localHolds, localRefs]
    | afterDemand _shared =>
        cases outcome <;>
          simpa [payloadSpec, localHolds, localRefs, resumeHolds, resumeRefs] using held
  afterAllocation := by
    intro p token cell _held cellHeld
    cases token <;>
      simpa [payloadSpec, localHolds, localRefs, Finset.mem_singleton] using cellHeld

def payloadInventory : ReferenceInventory payloadDiscipline where
  origin := originRefs
  localState := localRefs
  resume := resumeRefs
  value := Val.referenceSet
  origin_exact := by intro _ _; rfl
  local_exact := by intro _ _; rfl
  resume_exact := by intro _ _; rfl
  value_exact := by intro _ _; rfl

def bindingCell : CellId := ⟨1, [], 0, 0⟩

def sharedCell : CellId := ⟨1, [], 1, 0⟩

def compoundValue : Val CellId := .app (.need sharedCell) (.need sharedCell)

/-- Positions stay in the value. The reference set keeps one address. -/
def occurrencesOf : Val CellId → List CellId
  | .sym _ => []
  | .app head arg => occurrencesOf head ++ occurrencesOf arg
  | .need cell | .thunk cell | .code cell => [cell]

def consumersOf (value : Val CellId) : Configuration CellId Nat 2 :=
  let rows := occurrencesOf value
  ⟨⟨0, rows, fun _ => some 0, false, rows.length⟩, ∅⟩

def payloadWeight : PayloadCell → Nat := fun _ => 1

theorem compound_value_retains_two_occurrences :
    occurrencesOf compoundValue = [sharedCell, sharedCell] ∧
      compoundValue.referenceSet = {sharedCell} ∧
      compoundValue.matchApp = some (.need sharedCell, .need sharedCell) ∧
      bindingCell ∉ compoundValue.referenceSet := by
  decide

theorem compound_consumers_share_one_demand :
    unread (consumersOf compoundValue).log 0 = [sharedCell, sharedCell] ∧
      unread (consumersOf compoundValue).log 1 = [sharedCell, sharedCell] ∧
      SharedOccurrenceLog.Valid (consumersOf compoundValue).log := by
  refine And.intro (by decide) (And.intro (by decide) ?_)
  unfold SharedOccurrenceLog.Valid consumersOf compoundValue occurrencesOf
    SharedOccurrenceLog.pastEnd
  refine And.intro (by simp) ?_
  intro _client position positionEq
  simp at positionEq
  subst positionEq
  simp

theorem cancellation_drops_only_the_one_consumer :
    let consumers := consumersOf compoundValue
    unread (cancelConsumer consumers 0).log 0 = [] ∧
      unread (cancelConsumer consumers 0).log 1 = [sharedCell, sharedCell] := by
  decide

theorem cell_free_payload_has_no_demand :
    occurrencesOf (.sym (Cell := CellId) 0) = [] ∧
      (Val.sym (Cell := CellId) 0).referenceSet = ∅ ∧
      (consumersOf (.sym (Cell := CellId) 0)).log.rows = [] := by
  exact ⟨rfl, by simp [Val.referenceSet], rfl⟩

def payloadCoefficient : PayloadMachine → PayloadMachine → Nat :=
  productionCoefficient (fun _ => (2 : Nat))

def payloadSource : Coalgebra PayloadOccurrence PayloadOccurrence Nat :=
  source payloadSpec payloadCoefficient

def payloadStart : PayloadMachine :=
  { world :=
      { lineage := 1
        path := []
        heap := empty
        receipts := ReceiptGraph.empty
        nextCell := 0
        nextEvaluator := 0 }
    control := .run .start [] }

def payloadInitial : PayloadOccurrence := ⟨payloadStart, []⟩

def payloadSuspendedCut : PayloadCut := contributions payloadSource 3 payloadInitial

def payloadRun : PayloadCut := contributions payloadSource (3 + 7) payloadInitial

def advanceCut (cut : PayloadCut) : PayloadCut :=
  Mettapedia.GSLT.Dynamics.WeightedResumption.sequence cut fun leaf =>
    match leaf with
    | .inl done => [(.inl done, (1 : Nat))]
    | .inr pending => contributions payloadSource 7 pending

theorem payload_sequence_is_the_source_run :
    advanceCut payloadSuspendedCut = payloadRun := by
  unfold advanceCut payloadSuspendedCut payloadRun payloadSource payloadInitial
  exact (resume_exact payloadSpec payloadCoefficient 3 7 payloadInitial).symm

def payloadShell : PayloadAccount :=
  { occurrence := payloadInitial
    rights := {Right.force, Right.inspect}
    demand := sharedCell
    paidProduction := 0
    cut := [] }

/-- A singleton leaf replaces the occurrence and payment. A branching cut
replaces only the cut, so the two worlds are not written into one occurrence. -/
def adoptPayload (account : PayloadAccount) (cut : PayloadCut) : PayloadAccount :=
  { account with
      cut
      occurrence :=
        match cut with
        | [(.inl occurrence, _)] => occurrence
        | [(.inr occurrence, _)] => occurrence
        | _ => account.occurrence
      paidProduction :=
        match cut with
        | [(_, paid)] => paid
        | _ => account.paidProduction }

def payloadReady : PayloadAccount := adoptPayload payloadShell payloadSuspendedCut

def advancePayload (account : PayloadAccount) : PayloadAccount :=
  adoptPayload account (advanceCut account.cut)

def branchAccount (leaf : (PayloadOccurrence ⊕ PayloadOccurrence) × Nat) : PayloadAccount :=
  { occurrence := retained leaf.1
    rights :=
      match leaf.1 with
      | .inl _ => {Right.inspect}
      | .inr _ => {Right.force, Right.inspect}
    demand := sharedCell
    paidProduction := leaf.2
    cut := [leaf] }

def leftAccount : PayloadAccount :=
  match payloadRun with
  | left :: _ => branchAccount left
  | [] => payloadShell

def rightAccount : PayloadAccount :=
  match payloadRun with
  | _ :: right :: _ => branchAccount right
  | _ => payloadShell

def payloadLeafPath (leaf : PayloadOccurrence ⊕ PayloadOccurrence) : WorldPath :=
  (retained leaf).state.world.path

def payloadLeafSpine (leaf : PayloadOccurrence ⊕ PayloadOccurrence) :
    List (HeapUpdate PayloadOrigin (Val CellId) Unit) :=
  (retained leaf).state.world.heap.spine

def payloadOperationRights (cut : PayloadCut) : Rights :=
  cut.foldl (fun acc leaf =>
    match leaf.1 with
    | .inl _ => acc ∪ {Right.inspect}
    | .inr pending =>
        match pending.state.control with
        | .halted _ => acc ∪ {Right.inspect}
        | _ => acc ∪ {Right.force}) ∅

def payloadPathsUniform (cut : PayloadCut) : Bool :=
  match cut with
  | [] => false
  | leaf :: rest => rest.all fun other => decide (payloadLeafPath other.1 = payloadLeafPath leaf.1)

def payloadSpinesUniform (cut : PayloadCut) : Bool :=
  match cut with
  | [] => false
  | leaf :: rest => rest.all fun other => decide (payloadLeafSpine other.1 = payloadLeafSpine leaf.1)

def payloadAllPaths (cut : PayloadCut) (expected : WorldPath) : Bool :=
  cut.all fun leaf => decide (payloadLeafPath leaf.1 = expected)

def payloadAllSpines (cut : PayloadCut)
    (expected : List (HeapUpdate PayloadOrigin (Val CellId) Unit)) : Bool :=
  cut.all fun leaf => decide (payloadLeafSpine leaf.1 = expected)

/-- Decidable cut agreement. It does not read `heap.current`, `Recorded`, or
any root inventory. -/
def payloadCutAgrees (account : PayloadAccount) : Bool :=
  match account.cut with
  | [(leaf, paid)] =>
      decide (payloadLeafPath leaf = account.occurrence.state.world.path) &&
        decide (payloadLeafSpine leaf = account.occurrence.state.world.heap.spine) &&
        decide ((retained leaf).trace = account.occurrence.trace) &&
        decide ((retained leaf).state.world.receipts.nextSerial =
          account.occurrence.state.world.receipts.nextSerial) &&
        decide ((retained leaf).state.work.transitions =
          account.occurrence.state.work.transitions) &&
        decide ((retained leaf).state.control = account.occurrence.state.control) &&
        decide (paid = account.paidProduction)
  | leaf :: rest =>
      payloadPathsUniform account.cut && payloadSpinesUniform account.cut &&
        decide (payloadLeafPath leaf.1 = account.occurrence.state.world.path) &&
        decide (payloadLeafSpine leaf.1 = account.occurrence.state.world.heap.spine) &&
        rest.all fun other =>
          decide (payloadLeafPath other.1 = account.occurrence.state.world.path)
  | [] => false

inductive PayloadAdmit where
  | accept (account : PayloadAccount)
  | reject (reason : Refusal) (kept : PayloadAccount)

/-- Path, spine, cut, and rights. No `Recorded` field, no root set, and no
world join. -/
def payloadCheckpoint (expectedPath : WorldPath)
    (expectedSpine : List (HeapUpdate PayloadOrigin (Val CellId) Unit))
    (requested : Rights) (account : PayloadAccount) : PayloadAdmit :=
  if account.cut.isEmpty then
    .reject .incompleteResidual account
  else if !payloadPathsUniform account.cut || !payloadSpinesUniform account.cut then
    .reject .splitWorlds account
  else if !payloadCutAgrees account then
    .reject .incoherentResidual account
  else if !payloadAllPaths account.cut expectedPath then
    .reject .staleWorld account
  else if !payloadAllSpines account.cut expectedSpine then
    .reject .changedDependency account
  else if !(decide (payloadOperationRights account.cut ⊆ account.rights)) then
    .reject .missingRights account
  else if (restrict? account.rights requested).isNone then
    .reject .missingRights account
  else
    .accept account

def resumeBranch (index : Nat) (expectedPath : WorldPath)
    (expectedSpine : List (HeapUpdate PayloadOrigin (Val CellId) Unit))
    (requested : Rights) (account : PayloadAccount) : PayloadAdmit :=
  match payloadCheckpoint account.occurrence.state.world.path
      account.occurrence.state.world.heap.spine {Right.force} account with
  | .reject reason kept => .reject reason kept
  | .accept current =>
      match (advancePayload current).cut[index]? with
      | none => .reject .incompleteResidual current
      | some leaf =>
          payloadCheckpoint expectedPath expectedSpine requested (branchAccount leaf)

def erasePayloadCurrent (occurrence : PayloadOccurrence) : PayloadOccurrence :=
  { occurrence with
      state := { occurrence.state with
        world := { occurrence.state.world with
          heap := { occurrence.state.world.heap with current := fun _ => none } } } }

def erasedPayloadAccount : PayloadAccount :=
  { leftAccount with
      occurrence := erasePayloadCurrent leftAccount.occurrence
      cut := leftAccount.cut.map fun leaf =>
        (Sum.map erasePayloadCurrent erasePayloadCurrent leaf.1, leaf.2) }

def payloadAdmitted (result : PayloadAdmit) : Bool :=
  match result with
  | .accept _ => true
  | .reject _ _ => false

def payloadRefused (reason : Refusal) (result : PayloadAdmit) : Bool :=
  match result with
  | .reject found _ => decide (found = reason)
  | .accept _ => false

theorem payload_ready_is_admitted :
    payloadAdmitted (payloadCheckpoint payloadReady.occurrence.state.world.path
      payloadReady.occurrence.state.world.heap.spine {Right.force} payloadReady) = true ∧
      payloadAdmitted (payloadCheckpoint payloadReady.occurrence.state.world.path
        payloadReady.occurrence.state.world.heap.spine ∅ payloadReady) = true := by
  decide

theorem payload_pending_empty_request_needs_force :
    payloadRefused .missingRights (payloadCheckpoint
      payloadReady.occurrence.state.world.path
      payloadReady.occurrence.state.world.heap.spine ∅
      { payloadReady with rights := {Right.inspect} }) = true := by
  decide

theorem payload_suspension_preserves_the_prefix :
    payloadSuspendedCut.map (fun leaf =>
      ((retained leaf.1).state.world.path, (retained leaf.1).trace, leaf.2,
        (retained leaf.1).state.world.nextCell)) = [([], [0, 0, 0], 1, 2)] ∧
      payloadSuspendedCut.all (fun leaf =>
        decide ((retained leaf.1).state.control =
          .force sharedCell [.resume (.afterDemand sharedCell)])) = true := by
  decide

theorem payload_run_keeps_both_worlds :
    payloadRun.map (fun leaf =>
      ((retained leaf.1).state.world.path, leaf.2,
        (retained leaf.1).state.world.nextCell)) = [([0], 2, 2), ([1], 2, 2)] ∧
      payloadRun.all (fun leaf =>
        decide ((retained leaf.1).trace.take 3 = [0, 0, 0]) &&
          decide ((retained leaf.1).state.control =
            .halted (.value compoundValue))) = true := by
  decide

theorem payload_branches_do_not_join :
    payloadReady.occurrence.state.world.path = [] ∧
      leftAccount.occurrence.state.world.path = [0] ∧
      rightAccount.occurrence.state.world.path = [1] ∧
      leftAccount.occurrence.state.world.path ≠
        rightAccount.occurrence.state.world.path := by
  decide

theorem payload_joined_resume_is_split_worlds :
    payloadRefused .splitWorlds (payloadCheckpoint [] [] {Right.inspect}
      (advancePayload payloadReady)) = true := by
  decide

theorem payload_branch_resume_is_admitted :
    payloadAdmitted (resumeBranch 0 leftAccount.occurrence.state.world.path
      leftAccount.occurrence.state.world.heap.spine {Right.inspect} payloadReady) = true ∧
      payloadAdmitted (resumeBranch 1 rightAccount.occurrence.state.world.path
        rightAccount.occurrence.state.world.heap.spine ∅ payloadReady) = true ∧
      payloadRefused .staleWorld (resumeBranch 0 []
        leftAccount.occurrence.state.world.heap.spine {Right.inspect} payloadReady) = true := by
  decide

theorem payload_returned_inspection_accepts_an_empty_request :
    payloadAdmitted (payloadCheckpoint leftAccount.occurrence.state.world.path
      leftAccount.occurrence.state.world.heap.spine ∅ leftAccount) = true ∧
      payloadOperationRights leftAccount.cut = {Right.inspect} := by
  decide

theorem payload_second_resume_does_not_charge_again :
    (advancePayload leftAccount).paidProduction = leftAccount.paidProduction ∧
      leftAccount.paidProduction = 2 ∧
      (advancePayload leftAccount).cut.map Prod.snd = [2] := by
  decide

def sharedSuspended (machine : PayloadMachine) : Bool :=
  decide (machine.world.heap.lookup sharedCell =
    some ({ origin := .capture bindingCell 5
            cache := .suspended } : PayloadCell))

def sharedValued (machine : PayloadMachine) (symbol : Nat) : Bool :=
  decide (machine.world.heap.lookup sharedCell =
    some ({ origin := .capture bindingCell 5
            cache := .value (.sym symbol) } : PayloadCell))

def bindingHeld (machine : PayloadMachine) : Bool :=
  decide (machine.world.heap.lookup bindingCell =
    some ({ origin := .symbol 8, cache := .suspended } : PayloadCell))

def bothAllocated (machine : PayloadMachine) : Bool :=
  decide (machine.world.heap.allocated = {bindingCell, sharedCell})

theorem payload_cells_come_from_the_run :
    payloadSuspendedCut.all (fun leaf =>
      sharedSuspended (retained leaf.1).state &&
        bindingHeld (retained leaf.1).state &&
        bothAllocated (retained leaf.1).state) = true ∧
      sharedValued leftAccount.occurrence.state 5 = true ∧
      sharedValued rightAccount.occurrence.state 6 = true ∧
      bindingHeld leftAccount.occurrence.state = true ∧
      bindingHeld rightAccount.occurrence.state = true ∧
      bothAllocated leftAccount.occurrence.state = true ∧
      bothAllocated rightAccount.occurrence.state = true := by
  decide

theorem payload_initial_is_anchored :
    payloadInitial.state.world.heap.Recorded ∧
      payloadDiscipline.machineClosed payloadInitial.state := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [payloadInitial, payloadStart] using
      (empty_recorded : Recorded (empty : Heap PayloadOrigin (Val CellId) Unit))
  · intro cell record found
    simp [payloadInitial, payloadStart, lookup, empty] at found
  · simp [ReferenceDiscipline.control, payloadDiscipline, payloadInitial, payloadStart,
      localHolds, localRefs, ReferenceDiscipline.stack]

theorem payload_contributions_stay_anchored (fuel : Nat) (occurrence : PayloadOccurrence)
    (valid : occurrence.state.world.heap.Recorded ∧
      payloadDiscipline.machineClosed occurrence.state) :
    ∀ leaf ∈ contributions payloadSource fuel occurrence,
      (retained leaf.1).state.world.heap.Recorded ∧
        payloadDiscipline.machineClosed (retained leaf.1).state := by
  intro leaf member
  have preserved :=
    contributions_invariant payloadSource
      (fun state => state.state.world.heap.Recorded ∧
        payloadDiscipline.machineClosed state.state)
      (fun state => state.state.world.heap.Recorded ∧
        payloadDiscipline.machineClosed state.state)
      (fun state answer anchored returned => by
        have returnedSource : payloadSource state = .inl answer := returned
        obtain ⟨same, _⟩ :=
          (source_return_iff payloadSpec payloadCoefficient state answer).mp returnedSource
        cases same
        exact anchored)
      (fun state alternatives anchored branched next nextMember => by
        have branchedSource : payloadSource state = .inr alternatives := branched
        have notHalted : isHalted state.state = false := by
          cases control : state.state.control with
          | halted _ =>
              simp only [payloadSource, source, control] at branchedSource
              exact False.elim (Sum.inl_ne_inr branchedSource)
          | force _ _ =>
              unfold isHalted
              rw [control]
          | run _ _ =>
              unfold isHalted
              rw [control]
          | returned _ _ =>
              unfold isHalted
              rw [control]
        have running := source_branches payloadSpec payloadCoefficient state notHalted
        have successorsEq :
            successors payloadSpec payloadCoefficient state = alternatives := by
          have joined := running.symm.trans branchedSource
          injection joined
        rw [← successorsEq] at nextMember
        obtain ⟨index, found, _trace, _value⟩ :=
          (successor_iff payloadSpec payloadCoefficient state next.1 next.2).mp nextMember
        exact ⟨step_heap_recorded payloadSpec state.state next.1.state anchored.1
            (List.mem_of_getElem? found),
          payloadDiscipline.step_closed anchored.2 (List.mem_of_getElem? found)⟩)
      fuel occurrence valid leaf member
  cases leaf with
  | mk which _coeff =>
      cases which with
      | inl answer => exact preserved
      | inr pending => exact preserved

/-- Semantic anchoring is derived. It is not a checkpoint conjunct. -/
def SemanticallyAnchored (account : PayloadAccount) : Prop :=
  account.occurrence.state.world.heap.Recorded ∧
    payloadDiscipline.machineClosed account.occurrence.state ∧
    ∀ leaf ∈ account.cut,
      (retained leaf.1).state.world.heap.Recorded ∧
        payloadDiscipline.machineClosed (retained leaf.1).state ∧
        (retained leaf.1).state.world.heap = account.occurrence.state.world.heap

theorem payload_ready_is_anchored : SemanticallyAnchored payloadReady := by
  have length : payloadSuspendedCut.length = 1 := by decide
  have pendingShape : payloadSuspendedCut.all (fun item =>
      match item.1 with | .inl _ => false | .inr _ => true) = true := by
    decide
  match hcut : payloadSuspendedCut with
  | [] => simp [hcut] at length
  | leaf :: rest =>
      cases rest with
      | cons _ _ => simp [hcut] at length
      | nil =>
          cases leaf with
          | mk which paid =>
              cases which with
              | inl _ =>
                  simp [hcut] at pendingShape
              | inr pending =>
                  have member : (.inr pending, paid) ∈ payloadSuspendedCut := by
                    simp [hcut]
                  have anchored :=
                    payload_contributions_stay_anchored 3 payloadInitial
                      payload_initial_is_anchored (.inr pending, paid) member
                  have occurrenceEq : payloadReady.occurrence = pending := by
                    simp [payloadReady, adoptPayload, hcut]
                  have cutEq : payloadReady.cut = [(.inr pending, paid)] := by
                    simp [payloadReady, adoptPayload, hcut]
                  refine And.intro ?_ (And.intro ?_ ?_)
                  · simpa [occurrenceEq, retained] using anchored.1
                  · simpa [occurrenceEq, retained] using anchored.2
                  · intro other otherMember
                    have otherEq : other = (.inr pending, paid) := by
                      simpa [cutEq] using otherMember
                    cases otherEq
                    exact And.intro anchored.1 (And.intro anchored.2 (by
                      simp [payloadReady, adoptPayload, hcut, retained]))

theorem left_branch_is_anchored : SemanticallyAnchored leftAccount := by
  have length : payloadRun.length = 2 := by decide
  match hrun : payloadRun with
  | [] => simp [hrun] at length
  | left :: rest =>
      cases rest with
      | nil => simp [hrun] at length
      | cons right more =>
          cases more with
          | cons _ _ => simp [hrun] at length
          | nil =>
              have account : leftAccount = branchAccount left := by
                simp [leftAccount, hrun]
              have runMember : left ∈ contributions payloadSource (3 + 7) payloadInitial := by
                have listed : left ∈ payloadRun := by
                  rw [hrun]
                  exact .head _
                simpa [payloadRun] using listed
              have anchored :=
                payload_contributions_stay_anchored (3 + 7) payloadInitial
                  payload_initial_is_anchored left runMember
              refine And.intro ?_ (And.intro ?_ ?_)
              · simpa [account, branchAccount, retained] using anchored.1
              · simpa [account, branchAccount, retained] using anchored.2
              · intro leaf member
                have leafEq : leaf = left := by
                  simpa [account, branchAccount] using member
                cases leafEq
                exact And.intro anchored.1 (And.intro anchored.2 (by
                  simp [account, branchAccount, retained]))

theorem right_branch_is_anchored : SemanticallyAnchored rightAccount := by
  have length : payloadRun.length = 2 := by decide
  match hrun : payloadRun with
  | [] => simp [hrun] at length
  | left :: rest =>
      cases rest with
      | nil => simp [hrun] at length
      | cons right more =>
          cases more with
          | cons _ _ => simp [hrun] at length
          | nil =>
              have account : rightAccount = branchAccount right := by
                simp [rightAccount, hrun]
              have runMember : right ∈ contributions payloadSource (3 + 7) payloadInitial := by
                have listed : right ∈ payloadRun := by
                  rw [hrun]
                  exact .tail _ (.head _)
                simpa [payloadRun] using listed
              have anchored :=
                payload_contributions_stay_anchored (3 + 7) payloadInitial
                  payload_initial_is_anchored right runMember
              refine And.intro ?_ (And.intro ?_ ?_)
              · simpa [account, branchAccount, retained] using anchored.1
              · simpa [account, branchAccount, retained] using anchored.2
              · intro leaf member
                have leafEq : leaf = right := by
                  simpa [account, branchAccount] using member
                cases leafEq
                exact And.intro anchored.1 (And.intro anchored.2 (by
                  simp [account, branchAccount, retained]))

theorem payload_branch_heaps_stay_separate :
    leftAccount.occurrence.state.world.heap ≠ rightAccount.occurrence.state.world.heap := by
  intro same
  have cells := payload_cells_come_from_the_run
  have leftLookup := of_decide_eq_true (by simpa [sharedValued] using cells.2.1)
  have rightLookup := of_decide_eq_true (by simpa [sharedValued] using cells.2.2.1)
  have joined := congrArg
      (fun heap : Heap PayloadOrigin (Val CellId) Unit => heap.lookup sharedCell) same
  rw [leftLookup, rightLookup] at joined
  injection joined with records
  have caches := congrArg (fun record : PayloadCell => record.cache) records
  injection caches with values
  injection values with numbers
  exact absurd numbers (by decide)

theorem compound_root_addresses :
    rootAddresses (roots (consumersOf compoundValue)) = {sharedCell} ∧
      rootAddresses (payloadInventory.controlRoots (0 : Nat)
        (.halted (.value compoundValue))) = {sharedCell} ∧
      rootAddresses (payloadInventory.controlRoots (0 : Nat)
        (.force sharedCell [.resume (.afterDemand sharedCell)])) = {sharedCell} ∧
      payloadInventory.controlRoots (0 : Nat) (.halted (.value (.sym (Cell := CellId) 0))) = ∅ ∧
      roots (consumersOf (.sym (Cell := CellId) 0)) = ∅ := by
  decide

theorem shared_cycle_is_not_the_payload_root_census :
    ready.delivery = Controls.sharedCycle ∧
      rootAddresses (logRoots Nat ready.delivery.log) = {(0 : Fin 3)} ∧
      compoundValue.referenceSet = {sharedCell} ∧
      bindingCell ∉ compoundValue.referenceSet := by
  refine And.intro rfl (And.intro ?_ (And.intro ?_ ?_))
  · exact Controls.duplicate_occurrences_share_one_resource_graph.1
  · decide
  · simp [compoundValue, Val.referenceSet]
    decide

private theorem payload_checkpoint_agrees
    (expectedPath : WorldPath)
    (expectedSpine : List (HeapUpdate PayloadOrigin (Val CellId) Unit))
    (requested : Rights) (account : PayloadAccount)
    (admitted : payloadCheckpoint expectedPath expectedSpine requested account = .accept account) :
    payloadPathsUniform account.cut = true ∧
      payloadSpinesUniform account.cut = true ∧
      payloadCutAgrees account = true := by
  unfold payloadCheckpoint at admitted
  cases hEmpty : account.cut.isEmpty with
  | true => simp [hEmpty] at admitted
  | false =>
      cases hWorlds : (!payloadPathsUniform account.cut || !payloadSpinesUniform account.cut) with
      | true => simp [hEmpty, hWorlds] at admitted
      | false =>
          cases hAgrees : (!payloadCutAgrees account) with
          | true => simp [hEmpty, hWorlds, hAgrees] at admitted
          | false =>
              cases hPaths : (!payloadAllPaths account.cut expectedPath) with
              | true => simp [hEmpty, hWorlds, hAgrees, hPaths] at admitted
              | false =>
                  cases hSpines : (!payloadAllSpines account.cut expectedSpine) with
                  | true => simp [hEmpty, hWorlds, hAgrees, hPaths, hSpines] at admitted
                  | false =>
                      cases hRights :
                          (!(decide (payloadOperationRights account.cut ⊆ account.rights))) with
                      | true =>
                          simp [hEmpty, hWorlds, hAgrees, hPaths, hSpines, hRights] at admitted
                      | false =>
                          cases hRestrict : (restrict? account.rights requested).isNone with
                          | true =>
                              simp [hEmpty, hWorlds, hAgrees, hPaths, hSpines, hRights, hRestrict]
                                at admitted
                          | false =>
                              have pathsHeld : payloadPathsUniform account.cut = true := by
                                cases hp : payloadPathsUniform account.cut with
                                | false =>
                                    have contra : true = false := by
                                      have uniform :
                                          (!payloadPathsUniform account.cut ||
                                            !payloadSpinesUniform account.cut) = true := by
                                        simp [hp]
                                      exact uniform.symm.trans hWorlds
                                    cases contra
                                | true => rfl
                              have spinesHeld : payloadSpinesUniform account.cut = true := by
                                cases hs : payloadSpinesUniform account.cut with
                                | false =>
                                    have contra : true = false := by
                                      have uniform :
                                          (!payloadPathsUniform account.cut ||
                                            !payloadSpinesUniform account.cut) = true := by
                                        simp [pathsHeld, hs]
                                      exact uniform.symm.trans hWorlds
                                    cases contra
                                | true => rfl
                              have agreesHeld : payloadCutAgrees account = true := by
                                cases hc : payloadCutAgrees account with
                                | false =>
                                    have contra : true = false := by
                                      have negated : (!payloadCutAgrees account) = true := by
                                        simp [hc]
                                      exact negated.symm.trans hAgrees
                                    cases contra
                                | true => rfl
                              exact ⟨pathsHeld, spinesHeld, agreesHeld⟩

theorem payload_singleton_spine_needs_recorded
    (expectedPath : WorldPath)
    (expectedSpine : List (HeapUpdate PayloadOrigin (Val CellId) Unit))
    (requested : Rights) (account : PayloadAccount)
    (admitted : payloadCheckpoint expectedPath expectedSpine requested account = .accept account)
    (stored : account.occurrence.state.world.heap.Recorded)
    (leaves : ∀ leaf ∈ account.cut, (retained leaf.1).state.world.heap.Recorded) :
    ∀ leaf ∈ account.cut,
      (retained leaf.1).state.world.heap = account.occurrence.state.world.heap := by
  obtain ⟨_paths, spinesHeld, agreesHeld⟩ :=
    payload_checkpoint_agrees expectedPath expectedSpine requested account admitted
  intro leaf member
  have spineEq : payloadLeafSpine leaf.1 = account.occurrence.state.world.heap.spine := by
    cases hcut : account.cut with
    | nil =>
        have contra : true = false := by
          simpa [payloadSpinesUniform, hcut] using spinesHeld.symm
        cases contra
    | cons first rest =>
        cases first with
        | mk sum paid =>
            cases rest with
            | nil =>
                have chain := agreesHeld
                simp only [payloadCutAgrees, hcut] at chain
                have dropPaid := (Bool.and_eq_true_iff.mp chain).1
                have dropControl := (Bool.and_eq_true_iff.mp dropPaid).1
                have dropTransitions := (Bool.and_eq_true_iff.mp dropControl).1
                have dropSerial := (Bool.and_eq_true_iff.mp dropTransitions).1
                have dropTrace := (Bool.and_eq_true_iff.mp dropSerial).1
                have firstSpine := decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp dropTrace).2
                have leafEq : leaf = (sum, paid) := by
                  rw [hcut] at member
                  simpa using List.mem_singleton.mp member
                cases leafEq
                exact firstSpine
            | cons second more =>
                have chain := agreesHeld
                simp only [payloadCutAgrees, hcut] at chain
                have dropAll := (Bool.and_eq_true_iff.mp chain).1
                have firstSpine := decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp dropAll).2
                have others : ∀ other ∈ second :: more,
                    payloadLeafSpine other.1 = payloadLeafSpine sum := by
                  intro other otherMember
                  have uniformAll :
                      (second :: more).all
                        (fun other => decide (payloadLeafSpine other.1 = payloadLeafSpine sum)) =
                        true := by
                    simpa [payloadSpinesUniform, hcut] using spinesHeld
                  exact decide_eq_true_eq.mp ((List.all_eq_true.mp uniformAll) other otherMember)
                have memberEq : leaf = (sum, paid) ∨ leaf ∈ second :: more := by
                  rw [hcut] at member
                  simpa using List.mem_cons.mp member
                cases memberEq with
                | inl headEq =>
                    cases headEq
                    exact firstSpine
                | inr tailMember =>
                    exact (others leaf tailMember).trans firstSpine
  exact eq_of_spine_eq _ _ (leaves leaf member) stored spineEq

private def payloadResources (machine : PayloadMachine)
    (recorded : machine.world.heap.Recorded)
    (closed : payloadDiscipline.heapClosed machine.world.heap) :=
  payloadInventory.resourceHeap machine.world.heap recorded closed payloadWeight

private theorem record_mentions_only_the_binding
    (record : PayloadCell)
    (originEq : record.origin = .capture bindingCell 5)
    (cacheEq : record.cache = .suspended ∨
      ∃ symbol, record.cache = .value (.sym symbol)) :
    payloadInventory.record record = {bindingCell} := by
  cases cacheEq with
  | inl suspended =>
      rw [ReferenceInventory.record, originEq, suspended]
      simp [payloadInventory, ReferenceInventory.cache, originRefs]
  | inr valued =>
      obtain ⟨symbol, valued⟩ := valued
      rw [ReferenceInventory.record, originEq, valued]
      simp [payloadInventory, ReferenceInventory.cache, originRefs, Val.referenceSet]

theorem shared_demand_footprint {Owner : Type} [DecidableEq Owner]
    (machine : PayloadMachine)
    (recorded : machine.world.heap.Recorded)
    (closed : payloadDiscipline.heapClosed machine.world.heap)
    (sharedLookup : machine.world.heap.lookup sharedCell =
      some ({ origin := .capture bindingCell 5, cache := .suspended } : PayloadCell) ∨
      ∃ symbol, machine.world.heap.lookup sharedCell =
        some ({ origin := .capture bindingCell 5, cache := .value (.sym symbol) } : PayloadCell))
    (_bindingLookup : machine.world.heap.lookup bindingCell =
      some ({ origin := .symbol 8, cache := .suspended } : PayloadCell))
    (allocated : machine.world.heap.allocated = {bindingCell, sharedCell})
    (roots : Roots Owner CellId)
    (sameRoots : rootAddresses roots = {sharedCell}) :
    let resources := payloadResources machine recorded closed
    ValidRoots resources roots ∧
      census resources roots = {bindingCell, sharedCell} := by
  intro resources
  have sharedRecord :
      ∃ record, machine.world.heap.lookup sharedCell = some record ∧
        record.origin = .capture bindingCell 5 ∧
        (record.cache = .suspended ∨
          ∃ symbol, record.cache = .value (.sym symbol)) := by
    cases sharedLookup with
    | inl suspended =>
        exact ⟨_, suspended, rfl, Or.inl rfl⟩
    | inr valued =>
        obtain ⟨symbol, valued⟩ := valued
        exact ⟨_, valued, rfl, Or.inr ⟨symbol, rfl⟩⟩
  obtain ⟨record, found, origin, cache⟩ := sharedRecord
  have edge : payloadInventory.record record = {bindingCell} :=
    record_mentions_only_the_binding record origin cache
  have resourcesLookup :
      resources.lookup sharedCell =
        some ⟨record, payloadInventory.record record, payloadWeight record⟩ := by
    simp only [resources]
    unfold payloadResources ReferenceInventory.resourceHeap resourceHeap
    simp [found, payloadWeight]
  have allocatedResources : resources.allocated = {bindingCell, sharedCell} := by
    simp only [resources]
    unfold payloadResources ReferenceInventory.resourceHeap resourceHeap
    exact allocated
  have valid : ValidRoots resources roots := by
    apply (rootAddresses_subset_iff_validRoots resources roots).mp
    rw [sameRoots]
    intro cell member
    have cellEq : cell = sharedCell := by simpa using member
    rw [cellEq, allocatedResources]
    simp
  refine ⟨valid, ?_⟩
  have pair : ∃ owner, (owner, sharedCell) ∈ roots := by
    have address : sharedCell ∈ rootAddresses roots := by simp [sameRoots]
    obtain ⟨pair, member, snd⟩ := Finset.mem_image.mp address
    cases pair with
    | mk owner cell =>
        cases snd
        exact ⟨owner, member⟩
  obtain ⟨owner, member⟩ := pair
  have sharedAllocated : sharedCell ∈ resources.allocated := by
    rw [allocatedResources]
    simp
  have liveShared : Live resources roots sharedCell :=
    live_of_root resources roots member sharedAllocated
  have liveBinding : Live resources roots bindingCell := by
    have reference : bindingCell ∈ payloadInventory.record record := by
      rw [edge]
      simp
    exact live_step resources roots liveShared resourcesLookup reference
  ext cell
  constructor
  · intro memberCensus
    have live := (mem_census_iff_live resources roots valid cell).mp memberCensus
    have kept : cell ∈ resources.allocated := live_allocated resources roots live
    rw [allocatedResources] at kept
    simpa using kept
  · intro memberCell
    apply (mem_census_iff_live resources roots valid cell).mpr
    have cellEq : cell = bindingCell ∨ cell = sharedCell := by simpa using memberCell
    cases cellEq with
    | inl binding =>
        cases binding
        exact liveBinding
    | inr shared =>
        cases shared
        exact liveShared

theorem payload_cancellation_preserves_the_other_live_payload
    (machine : PayloadMachine)
    (recorded : machine.world.heap.Recorded)
    (closed : payloadDiscipline.machineClosed machine)
    (symbol : Nat)
    (sharedLookup : sharedValued machine symbol = true)
    (bindingLookup : bindingHeld machine = true)
    (allocated : bothAllocated machine = true)
    (halted : machine.control = .halted (.value compoundValue)) :
    let resources := payloadResources machine recorded closed.1
    let consumers := consumersOf compoundValue
    census resources (roots consumers) = {bindingCell, sharedCell} ∧
      census resources (payloadInventory.controlRoots (0 : Nat) machine.control) =
        {bindingCell, sharedCell} ∧
      (collect resources (roots (trimLog (cancelConsumer consumers 0)))).lookup sharedCell =
        resources.lookup sharedCell ∧
      (collect resources (roots (trimLog (cancelConsumer consumers 0)))).lookup bindingCell =
        resources.lookup bindingCell ∧
      (collect resources (roots (consumersOf (.sym (Cell := CellId) 0)))).lookup sharedCell =
        none ∧
      (collect resources (payloadInventory.controlRoots (0 : Nat)
        (.halted (.value (.sym (Cell := CellId) 0))))).lookup bindingCell = none ∧
      resources.lookup sharedCell ≠ none := by
  intro resources consumers
  have sharedEq := of_decide_eq_true (by simpa [sharedValued] using sharedLookup)
  have bindingEq := of_decide_eq_true (by simpa [bindingHeld] using bindingLookup)
  have allocatedEq := of_decide_eq_true (by simpa [bothAllocated] using allocated)
  have consumerRoots : rootAddresses (roots consumers) = {sharedCell} :=
    compound_root_addresses.1
  have controlAddresses :
      rootAddresses (payloadInventory.controlRoots (0 : Nat) machine.control) = {sharedCell} := by
    simpa [halted] using compound_root_addresses.2.1
  have consumerFootprint :=
    shared_demand_footprint machine recorded closed.1 (Or.inr ⟨symbol, sharedEq⟩) bindingEq
      allocatedEq (roots consumers) consumerRoots
  have controlFootprint :=
    shared_demand_footprint machine recorded closed.1 (Or.inr ⟨symbol, sharedEq⟩) bindingEq
      allocatedEq (payloadInventory.controlRoots (0 : Nat) machine.control) controlAddresses
  have unreadOther : unread consumers.log 1 = [sharedCell, sharedCell] :=
    compound_consumers_share_one_demand.2.1
  let otherOwner : Sum (Fin 2) Nat := Sum.inl 1
  have otherRoots : answerRoots otherOwner (unread consumers.log 1) =
      {(otherOwner, sharedCell)} := by
    simp [unreadOther, answerRoots]
  have liveShared : Live resources (answerRoots otherOwner (unread consumers.log 1))
      sharedCell := by
    apply live_of_root (owner := otherOwner)
    · rw [otherRoots]
      exact Finset.mem_singleton_self _
    · have sharedAllocated : sharedCell ∈ resources.allocated := by
        have footprint := consumerFootprint.2
        have member : sharedCell ∈ census resources (roots consumers) := by
          rw [footprint]
          simp
        exact live_allocated resources (roots consumers)
          ((mem_census_iff_live resources (roots consumers) consumerFootprint.1 sharedCell).mp
            member)
      exact sharedAllocated
  let sharedRecord : PayloadCell :=
    { origin := .capture bindingCell 5, cache := .value (.sym symbol) }
  have sourceRecord : machine.world.heap.lookup sharedCell = some sharedRecord := by
    simpa [sharedRecord] using sharedEq
  have edge := record_mentions_only_the_binding sharedRecord rfl (Or.inr ⟨symbol, rfl⟩)
  have resourcesLookup : resources.lookup sharedCell =
      some ⟨sharedRecord, {bindingCell}, payloadWeight sharedRecord⟩ := by
    have mapped :
        resources.lookup sharedCell =
          (machine.world.heap.lookup sharedCell).map
            (fun record => ⟨record, payloadInventory.record record, payloadWeight record⟩) := by
      simp only [resources, payloadResources, ReferenceInventory.resourceHeap, resourceHeap]
    rw [mapped, sourceRecord]
    simp [Option.map_some, edge]
  have liveBinding : Live resources (answerRoots otherOwner (unread consumers.log 1))
      bindingCell :=
    live_step resources _ liveShared resourcesLookup (by simp)
  have keptShared :=
    cancel_trim_retains_other_unread_graph resources consumers 0 1
      compound_consumers_share_one_demand.2.2 (by decide) sharedCell liveShared
  have keptBinding :=
    cancel_trim_retains_other_unread_graph resources consumers 0 1
      compound_consumers_share_one_demand.2.2 (by decide) bindingCell liveBinding
  have omittedLog : roots (consumersOf (.sym (Cell := CellId) 0)) = ∅ :=
    compound_root_addresses.2.2.2.2
  have omittedControl :
      payloadInventory.controlRoots (0 : Nat) (.halted (.value (.sym (Cell := CellId) 0))) = ∅ :=
    compound_root_addresses.2.2.2.1
  have droppedShared :=
    lookup_collect_of_not_live resources (roots (consumersOf (.sym (Cell := CellId) 0)))
      (by
        rw [omittedLog]
        exact not_live_empty resources sharedCell)
  have droppedBinding :=
    lookup_collect_of_not_live resources
      (payloadInventory.controlRoots (0 : Nat) (.halted (.value (.sym (Cell := CellId) 0))))
      (by
        rw [omittedControl]
        exact not_live_empty resources bindingCell)
  refine ⟨consumerFootprint.2, controlFootprint.2, keptShared, keptBinding, droppedShared,
    droppedBinding, ?_⟩
  rw [resourcesLookup]
  simp

theorem left_payload_cancellation_preserves_the_other_consumer :
    let machine := leftAccount.occurrence.state
    let resources := payloadResources machine left_branch_is_anchored.1
      left_branch_is_anchored.2.1.1
    (collect resources (roots (trimLog (cancelConsumer (consumersOf compoundValue) 0)))).lookup
        sharedCell = resources.lookup sharedCell ∧
      (collect resources (roots (trimLog (cancelConsumer (consumersOf compoundValue) 0)))).lookup
        bindingCell = resources.lookup bindingCell ∧
      (collect resources (roots (consumersOf (.sym (Cell := CellId) 0)))).lookup sharedCell = none ∧
      census resources (payloadInventory.controlRoots (0 : Nat) machine.control) =
        {bindingCell, sharedCell} := by
  have cells := payload_cells_come_from_the_run
  have halted : leftAccount.occurrence.state.control = .halted (.value compoundValue) := by
    have all := payload_run_keeps_both_worlds.2
    have length : payloadRun.length = 2 := by decide
    match hrun : payloadRun with
    | [] => simp [hrun] at length
    | left :: rest =>
        cases rest with
        | nil => simp [hrun] at length
        | cons _ more =>
            cases more with
            | cons _ _ => simp [hrun] at length
            | nil =>
                have account : leftAccount = branchAccount left := by simp [leftAccount, hrun]
                have flag := (List.all_eq_true.mp all) left (by simp [hrun])
                have controlFlag := (Bool.and_eq_true_iff.mp flag).2
                have controlEq := decide_eq_true_eq.mp controlFlag
                simpa [account, branchAccount, retained] using controlEq
  have preserved := payload_cancellation_preserves_the_other_live_payload
    leftAccount.occurrence.state left_branch_is_anchored.1 left_branch_is_anchored.2.1 5
    cells.2.1 cells.2.2.2.1 cells.2.2.2.2.2.1 halted
  exact ⟨preserved.2.2.1, preserved.2.2.2.1, preserved.2.2.2.2.1, preserved.2.1⟩

theorem payload_suspension_footprint :
    census
        (payloadResources payloadReady.occurrence.state payload_ready_is_anchored.1
          payload_ready_is_anchored.2.1.1)
        (payloadInventory.controlRoots (0 : Nat) payloadReady.occurrence.state.control) =
      {bindingCell, sharedCell} := by
  have cells := payload_cells_come_from_the_run.1
  have length : payloadSuspendedCut.length = 1 := by decide
  match hcut : payloadSuspendedCut with
  | [] => simp [hcut] at length
  | leaf :: rest =>
      cases rest with
      | cons _ _ => simp [hcut] at length
      | nil =>
          have accountOccurrence : payloadReady.occurrence = retained leaf.1 := by
            cases leaf with
            | mk which _paid =>
                cases which with
                | inl _ =>
                    have pending : payloadSuspendedCut.all (fun item =>
                        match item.1 with | .inl _ => false | .inr _ => true) = true := by
                      decide
                    simp [hcut] at pending
                | inr _pending =>
                    simp [payloadReady, adoptPayload, hcut, retained]
          have flag := (List.all_eq_true.mp cells) leaf (by simp [hcut])
          have dropAllocated := (Bool.and_eq_true_iff.mp flag).1
          have suspendedFlag := (Bool.and_eq_true_iff.mp dropAllocated).1
          have bindingFlag := (Bool.and_eq_true_iff.mp dropAllocated).2
          have allocatedFlag := (Bool.and_eq_true_iff.mp flag).2
          have control : payloadReady.occurrence.state.control =
              .force sharedCell [.resume (.afterDemand sharedCell)] := by
            have controls := payload_suspension_preserves_the_prefix.2
            have controlFlag := (List.all_eq_true.mp controls) leaf (by simp [hcut])
            simpa [accountOccurrence] using decide_eq_true_eq.mp controlFlag
          have addresses :
              rootAddresses (payloadInventory.controlRoots (0 : Nat)
                payloadReady.occurrence.state.control) = {sharedCell} := by
            simpa [control] using compound_root_addresses.2.2.1
          have sharedEq := of_decide_eq_true
            (by simpa [sharedSuspended, accountOccurrence.symm] using suspendedFlag)
          have bindingEq := of_decide_eq_true
            (by simpa [bindingHeld, accountOccurrence.symm] using bindingFlag)
          have allocatedEq := of_decide_eq_true
            (by simpa [bothAllocated, accountOccurrence.symm] using allocatedFlag)
          simpa using (shared_demand_footprint payloadReady.occurrence.state
            payload_ready_is_anchored.1 payload_ready_is_anchored.2.1.1
            (Or.inl sharedEq) bindingEq allocatedEq
            (payloadInventory.controlRoots (0 : Nat) payloadReady.occurrence.state.control)
            addresses).2

theorem payload_erased_singleton_is_admitted :
    payloadAdmitted (payloadCheckpoint leftAccount.occurrence.state.world.path
      leftAccount.occurrence.state.world.heap.spine {Right.inspect} erasedPayloadAccount) = true ∧
      erasedPayloadAccount.occurrence.state.world.heap.spine =
        leftAccount.occurrence.state.world.heap.spine := by
  decide

theorem payload_erased_current_is_not_recorded :
    ¬ erasedPayloadAccount.occurrence.state.world.heap.Recorded := by
  intro recorded
  have cells := payload_cells_come_from_the_run
  have bindingEq := of_decide_eq_true (by simpa [bindingHeld] using cells.2.2.2.1)
  have spineEq : erasedPayloadAccount.occurrence.state.world.heap.spine =
      leftAccount.occurrence.state.world.heap.spine :=
    payload_erased_singleton_is_admitted.2
  have leftRecorded := left_branch_is_anchored.1
  have spineLookup := leftRecorded bindingCell
  rw [bindingEq, ← spineEq] at spineLookup
  have currentNone : erasedPayloadAccount.occurrence.state.world.heap.lookup bindingCell = none := by
    unfold erasedPayloadAccount erasePayloadCurrent lookup
    rfl
  have erasedLookup := recorded bindingCell
  rw [currentNone, ← spineLookup] at erasedLookup
  cases erasedLookup

theorem payload_checkpoint_acceptance_is_not_anchoring :
    payloadAdmitted (payloadCheckpoint leftAccount.occurrence.state.world.path
      leftAccount.occurrence.state.world.heap.spine {Right.inspect} erasedPayloadAccount) = true ∧
      ¬ SemanticallyAnchored erasedPayloadAccount := by
  refine ⟨payload_erased_singleton_is_admitted.1, ?_⟩
  intro anchored
  exact payload_erased_current_is_not_recorded anchored.1

theorem payload_erased_spine_is_not_the_recorded_heap :
    erasedPayloadAccount.occurrence.state.world.heap.spine =
      leftAccount.occurrence.state.world.heap.spine ∧
      erasedPayloadAccount.occurrence.state.world.heap ≠
        leftAccount.occurrence.state.world.heap := by
  refine ⟨payload_erased_singleton_is_admitted.2, ?_⟩
  intro same
  exact payload_erased_current_is_not_recorded <| by
    rw [same]
    exact left_branch_is_anchored.1

/-! ## Source-derived ordered account

`ReceiptGraph.append` conses, so `nodes` are newest-first. Reversing them is
the order this run wrote. A factor's identity is that receipt occurrence.
Its coefficient is the receipt's world path, so branch alternatives stay on
the source path that wrote them. Finish order is not an input.

The numeric ledger above, with identities `1`, `7`, and `2`, is not this
account. `Controls.sharedCycle` is not this account. The projection is not a
checkpoint field, and a matching receipt list is not `Heap.Recorded`.

The source-order merge of the two branch ledgers compares those
receipt-world words. It is not the receipt account of either returned world,
and it is not a source-qualified join. `disposeAdmitted` is the separate
world-qualified disposition.
-/

abbrev PayloadReceiptNode :=
  ReceiptNode PayloadOrigin PayloadRule (Val CellId) Unit Unit Unit

abbrev PayloadReceipt :=
  ReceiptPayload PayloadOrigin PayloadRule (Val CellId) Unit Unit Unit

abbrev PayloadReceiptLedger := Ledger ReceiptId PayloadReceipt Coeff

abbrev PayloadProductionLedger :=
  Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Coeff

abbrev PayloadClaim := Scoped ReceiptId PayloadReceipt Coeff Nat

def occurrenceCoefficient (id : ReceiptId) : Coeff := ⟨id.world⟩

/-- Chronological receipt nodes. This reads the graph on the machine. -/
def chronologicalReceipts (machine : PayloadMachine) : List PayloadReceiptNode :=
  machine.world.receipts.nodes.reverse

def receiptFactor (node : PayloadReceiptNode) : Factor ReceiptId PayloadReceipt Coeff :=
  ⟨node.id, node.payload, occurrenceCoefficient node.id⟩

def receiptLedger (machine : PayloadMachine) : PayloadReceiptLedger :=
  (chronologicalReceipts machine).map receiptFactor

/-- Observe receipts only. On this run those observes are the shared-cell
commits. The payload does not store a separate completion kind. -/
def productionFactor? (node : PayloadReceiptNode) :
    Option (Factor (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Coeff) :=
  match node.payload with
  | .observe cell outcome =>
      some ⟨(cell, node.id), outcome, occurrenceCoefficient node.id⟩
  | _ => none

def productionLedgerOf (machine : PayloadMachine) : PayloadProductionLedger :=
  (chronologicalReceipts machine).filterMap productionFactor?

def sharedAllocationId : ReceiptId := ⟨[], 0⟩
def sharedDemandId : ReceiptId := ⟨[], 1⟩
def leftEvaluateId : ReceiptId := ⟨[0], 2⟩
def leftChoiceId : ReceiptId := ⟨[0], 3⟩
def leftProductionId : ReceiptId := ⟨[0], 4⟩
def rightEvaluateId : ReceiptId := ⟨[1], 2⟩
def rightChoiceId : ReceiptId := ⟨[1], 3⟩
def rightProductionId : ReceiptId := ⟨[1], 4⟩

def bindingAllocationFactor : Factor ReceiptId PayloadReceipt Coeff :=
  ⟨sharedAllocationId, .allocate bindingCell (.symbol 8), ⟨[]⟩⟩

def sharedDemandFactor : Factor ReceiptId PayloadReceipt Coeff :=
  ⟨sharedDemandId, .allocate sharedCell (.capture bindingCell 5), ⟨[]⟩⟩

def leftEvaluateFactor : Factor ReceiptId PayloadReceipt Coeff :=
  ⟨leftEvaluateId, .evaluate sharedCell 0, ⟨[0]⟩⟩

def leftChoiceFactor : Factor ReceiptId PayloadReceipt Coeff :=
  ⟨leftChoiceId, .chooseRule sharedCell PayloadRule.left, ⟨[0]⟩⟩

def leftProductionFactor : Factor ReceiptId PayloadReceipt Coeff :=
  ⟨leftProductionId, .observe sharedCell (.value (.sym 5)), ⟨[0]⟩⟩

def rightEvaluateFactor : Factor ReceiptId PayloadReceipt Coeff :=
  ⟨rightEvaluateId, .evaluate sharedCell 0, ⟨[1]⟩⟩

def rightChoiceFactor : Factor ReceiptId PayloadReceipt Coeff :=
  ⟨rightChoiceId, .chooseRule sharedCell PayloadRule.right, ⟨[1]⟩⟩

def rightProductionFactor : Factor ReceiptId PayloadReceipt Coeff :=
  ⟨rightProductionId, .observe sharedCell (.value (.sym 6)), ⟨[1]⟩⟩

def suspensionReceiptLedger : PayloadReceiptLedger :=
  [bindingAllocationFactor, sharedDemandFactor]

def leftFreshReceipts : PayloadReceiptLedger :=
  [leftEvaluateFactor, leftChoiceFactor, leftProductionFactor]

def rightFreshReceipts : PayloadReceiptLedger :=
  [rightEvaluateFactor, rightChoiceFactor, rightProductionFactor]

def leftReceiptLedger : PayloadReceiptLedger :=
  suspensionReceiptLedger ++ leftFreshReceipts

def rightReceiptLedger : PayloadReceiptLedger :=
  suspensionReceiptLedger ++ rightFreshReceipts

def leftProductionEntry :
    Factor (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Coeff :=
  ⟨(sharedCell, leftProductionId), .value (.sym 5), ⟨[0]⟩⟩

def rightProductionEntry :
    Factor (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Coeff :=
  ⟨(sharedCell, rightProductionId), .value (.sym 6), ⟨[1]⟩⟩

def suspensionClaims (candidate : ReceiptId) : Option Nat :=
  if candidate = sharedDemandId then some 0 else none

def leftClaims (candidate : ReceiptId) : Option Nat :=
  if candidate = sharedDemandId then some 0
  else if candidate = leftProductionId then some 0
  else none

def rightClaims (candidate : ReceiptId) : Option Nat :=
  if candidate = sharedDemandId then some 0
  else if candidate = rightProductionId then some 1
  else none

/-- Same receipt list as the left branch. The production occurrence is claimed
by the other owner. -/
def rivalClaims (candidate : ReceiptId) : Option Nat :=
  if candidate = sharedDemandId then some 0
  else if candidate = leftProductionId then some 1
  else none

def suspensionClaim : PayloadClaim := ⟨suspensionReceiptLedger, suspensionClaims⟩
def leftClaim : PayloadClaim := ⟨leftReceiptLedger, leftClaims⟩
def rightClaim : PayloadClaim := ⟨rightReceiptLedger, rightClaims⟩
def rivalClaim : PayloadClaim := ⟨leftReceiptLedger, rivalClaims⟩

/-- Algebraic claim merge. A successful result is a representation sidecar
beside the unchanged account. It does not join the two source worlds, install
a field, clear a receipt graph, or park a proposal. -/
def disposeClaims (account : PayloadAccount) (left right : PayloadClaim) :
    PayloadAccount × Option PayloadClaim :=
  match Scoped.merge? left right with
  | none => (account, none)
  | some merged => (account, some merged)

def payloadKept : PayloadAdmit → PayloadAccount
  | .accept account => account
  | .reject _ account => account

theorem dispose_keeps_the_payload_account (account : PayloadAccount)
    (left right : PayloadClaim) :
    (disposeClaims account left right).1 = account := by
  unfold disposeClaims
  cases Scoped.merge? left right <;> rfl

theorem suspension_claim_is_supported : suspensionClaim.Supported := by
  intro candidate owner claimed
  have claimedFun : suspensionClaims candidate = some owner := by
    simpa [suspensionClaim] using claimed
  unfold suspensionClaims at claimedFun
  split at claimedFun
  · next same =>
      cases claimedFun
      rw [same]
      decide
  · next _ =>
      cases claimedFun

theorem left_receipt_claim_is_supported : leftClaim.Supported := by
  intro candidate owner claimed
  have claimedFun : leftClaims candidate = some owner := by
    simpa [leftClaim] using claimed
  unfold leftClaims at claimedFun
  split at claimedFun
  · next same =>
      cases claimedFun
      rw [same]
      decide
  · next _ =>
      split at claimedFun
      · next same =>
          cases claimedFun
          rw [same]
          decide
      · next _ =>
          cases claimedFun

theorem right_receipt_claim_is_supported : rightClaim.Supported := by
  intro candidate owner claimed
  have claimedFun : rightClaims candidate = some owner := by
    simpa [rightClaim] using claimed
  unfold rightClaims at claimedFun
  split at claimedFun
  · next same =>
      cases claimedFun
      rw [same]
      decide
  · next _ =>
      split at claimedFun
      · next same =>
          cases claimedFun
          rw [same]
          decide
      · next _ =>
          cases claimedFun

theorem rival_receipt_claim_is_supported : rivalClaim.Supported := by
  intro candidate owner claimed
  have claimedFun : rivalClaims candidate = some owner := by
    simpa [rivalClaim] using claimed
  unfold rivalClaims at claimedFun
  split at claimedFun
  · next same =>
      cases claimedFun
      rw [same]
      decide
  · next _ =>
      split at claimedFun
      · next same =>
          cases claimedFun
          rw [same]
          decide
      · next _ =>
          cases claimedFun

theorem receipt_suspension_is_the_unfinished_prefix :
    receiptLedger payloadReady.occurrence.state = suspensionReceiptLedger ∧
      productionLedgerOf payloadReady.occurrence.state = [] ∧
      denote suspensionReceiptLedger = ⟨[]⟩ ∧
      payloadReady.paidProduction = 1 ∧
      payloadReady.occurrence.state.control =
        .force sharedCell [.resume (.afterDemand sharedCell)] := by
  decide

theorem receipt_left_branch_earns_one_production :
    receiptLedger leftAccount.occurrence.state = leftReceiptLedger ∧
      productionLedgerOf leftAccount.occurrence.state = [leftProductionEntry] ∧
      leftAccount.paidProduction = 2 ∧
      denote leftReceiptLedger = ⟨[0, 0, 0]⟩ ∧
      leftProductionId.world = leftAccount.occurrence.state.world.path := by
  decide

theorem receipt_right_branch_earns_the_other_production :
    receiptLedger rightAccount.occurrence.state = rightReceiptLedger ∧
      productionLedgerOf rightAccount.occurrence.state = [rightProductionEntry] ∧
      rightAccount.paidProduction = 2 ∧
      denote rightReceiptLedger = ⟨[1, 1, 1]⟩ ∧
      rightProductionId.world = rightAccount.occurrence.state.world.path ∧
      leftProductionId ≠ rightProductionId := by
  decide

/-- Representation comparison of receipt-world words. Source order and finish
order denote different words. This equality is not a world join. -/
theorem receipt_source_order_is_not_finish_order :
    Mettapedia.Algebra.SharedCoefficientLedger.merge? leftReceiptLedger rightReceiptLedger =
        some (leftReceiptLedger ++ rightFreshReceipts) ∧
      denote (leftReceiptLedger ++ rightFreshReceipts) = ⟨[0, 0, 0, 1, 1, 1]⟩ ∧
      denote (suspensionReceiptLedger ++ rightFreshReceipts ++ leftFreshReceipts) =
        ⟨[1, 1, 1, 0, 0, 0]⟩ ∧
      Mettapedia.Algebra.SharedCoefficientLedger.merge? leftReceiptLedger rightReceiptLedger ≠
        some (suspensionReceiptLedger ++ rightFreshReceipts ++ leftFreshReceipts) ∧
      Valid (leftReceiptLedger ++ rightFreshReceipts) := by
  have mergeEq :
      Mettapedia.Algebra.SharedCoefficientLedger.merge? leftReceiptLedger rightReceiptLedger =
        some (leftReceiptLedger ++ rightFreshReceipts) := by
    decide
  have sourceDenote :
      denote (leftReceiptLedger ++ rightFreshReceipts) = ⟨[0, 0, 0, 1, 1, 1]⟩ := by
    decide
  have finishDenote :
      denote (suspensionReceiptLedger ++ rightFreshReceipts ++ leftFreshReceipts) =
        ⟨[1, 1, 1, 0, 0, 0]⟩ := by
    decide
  have validMerge : Valid (leftReceiptLedger ++ rightFreshReceipts) := by
    decide
  refine ⟨mergeEq, sourceDenote, finishDenote, ?_, validMerge⟩
  intro same
  rw [mergeEq] at same
  injection same with lists
  have denotations := congrArg denote lists
  rw [sourceDenote, finishDenote] at denotations
  injection denotations with tokens
  have tokensDiff : ([0, 0, 0, 1, 1, 1] : List Nat) ≠ [1, 1, 1, 0, 0, 0] := by
    decide
  exact tokensDiff tokens

theorem receipt_nonprefix_shared_factor_is_refused :
    Mettapedia.Algebra.SharedCoefficientLedger.merge? leftReceiptLedger
        [leftProductionFactor, sharedDemandFactor] = none ∧
      Mettapedia.Algebra.SharedCoefficientLedger.merge? [leftProductionFactor, sharedDemandFactor]
        rightReceiptLedger = none := by
  decide

theorem receipt_repeated_observation_is_refused :
    append? leftReceiptLedger leftProductionFactor = none ∧
      append? [leftProductionEntry] leftProductionEntry = none ∧
      (Scoped.handleSince leftReceiptLedger 0 leftClaim).productions =
        leftClaim.productions ∧
      Scoped.selectedSince leftReceiptLedger
        (Scoped.handleSince leftReceiptLedger 0 leftClaim) = [] ∧
      receiptLedger (advancePayload leftAccount).occurrence.state = leftReceiptLedger ∧
      productionLedgerOf (advancePayload leftAccount).occurrence.state =
        [leftProductionEntry] ∧
      (advancePayload leftAccount).paidProduction = 2 := by
  have capture : Scoped.extendsOccurrenceCapture leftClaim leftClaim = true := by
    decide
  have accepted :
      Scoped.handleSince? leftClaim leftClaim 0 =
        some (Scoped.handleSince leftClaim.productions 0 leftClaim,
          Scoped.selectedSince leftClaim.productions leftClaim) := by
    unfold Scoped.handleSince?
    rw [capture]
    rfl
  refine ⟨by decide, by decide, ?_, ?_, by decide, by decide, by decide⟩
  · exact (Scoped.handleSince_spec accepted).1
  · exact Scoped.selectedSince_after_handle leftReceiptLedger 0 leftClaim

theorem receipt_inherited_claim_survives_the_resume :
    Scoped.extendsCapture suspensionClaim leftClaim = true ∧
      leftClaim.claims sharedDemandId = some 0 ∧
      (Scoped.handleSince suspensionReceiptLedger 1 leftClaim).productions =
        leftClaim.productions ∧
      Scoped.selectedSince suspensionReceiptLedger
        (Scoped.handleSince suspensionReceiptLedger 1 leftClaim) = [] ∧
      (Scoped.handleSince suspensionReceiptLedger 1 leftClaim).claims sharedDemandId =
        some 0 := by
  have capture : Scoped.extendsOccurrenceCapture suspensionClaim leftClaim = true := by
    decide
  have accepted :
      Scoped.handleSince? suspensionClaim leftClaim 1 =
        some (Scoped.handleSince suspensionClaim.productions 1 leftClaim,
          Scoped.selectedSince suspensionClaim.productions leftClaim) := by
    unfold Scoped.handleSince?
    rw [capture]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact Scoped.extendsCapture_preserves_claim suspension_claim_is_supported
      (by decide : Scoped.extendsCapture suspensionClaim leftClaim = true)
      (by decide : suspensionClaim.claims sharedDemandId = some 0)
  · exact (Scoped.handleSince_spec accepted).1
  · exact Scoped.selectedSince_after_handle suspensionReceiptLedger 1 leftClaim
  · exact Scoped.handleSince_prior_claim_preserved suspensionReceiptLedger 1 leftClaim
      (by decide : leftClaim.claims sharedDemandId = some 0)

/-- The algebraic sidecar in source order. Its production list is neither
returned world's receipt account. `disposeClaims` leaves the left account
unchanged beside that sidecar. -/
theorem receipt_agreed_claims_merge_in_source_order :
    ∃ merged : PayloadClaim,
      Scoped.merge? leftClaim rightClaim = some merged ∧
        merged.productions = leftReceiptLedger ++ rightFreshReceipts ∧
        denote merged.productions = ⟨[0, 0, 0, 1, 1, 1]⟩ ∧
        merged.claims sharedDemandId = some 0 ∧
        merged.claims leftProductionId = some 0 ∧
        merged.claims rightProductionId = some 1 ∧
        (disposeClaims leftAccount leftClaim rightClaim).2 = some merged := by
  have production :
      Mettapedia.Algebra.SharedCoefficientLedger.merge? leftReceiptLedger rightReceiptLedger =
        some (leftReceiptLedger ++ rightFreshReceipts) := by
    decide
  have compatible :
      (leftReceiptLedger ++ rightFreshReceipts).all
          (fun factor => Scoped.compatibleAt leftClaim rightClaim factor.identity) =
        true := by
    decide
  let merged : PayloadClaim :=
    ⟨leftReceiptLedger ++ rightFreshReceipts,
      fun identity => (leftClaim.claims identity).or (rightClaim.claims identity)⟩
  have productionClaims :
      Mettapedia.Algebra.SharedCoefficientLedger.merge? leftClaim.productions
          rightClaim.productions =
        some (leftReceiptLedger ++ rightFreshReceipts) := by
    simpa [leftClaim, rightClaim] using production
  have mergedEq : Scoped.merge? leftClaim rightClaim = some merged := by
    unfold Scoped.merge? merged
    rw [productionClaims]
    dsimp
    rw [compatible]
    rfl
  refine ⟨merged, mergedEq, rfl, by decide, by decide, by decide, by decide, ?_⟩
  unfold disposeClaims
  rw [mergedEq]

theorem receipt_rival_disposition_keeps_the_complete_account :
    Scoped.merge? leftClaim rivalClaim = none ∧
      (disposeClaims leftAccount leftClaim rivalClaim).1 = leftAccount ∧
      (disposeClaims leftAccount leftClaim rivalClaim).2 = none ∧
      (disposeClaims leftAccount leftClaim rivalClaim).1.paidProduction = 2 ∧
      (disposeClaims leftAccount leftClaim rivalClaim).1.cut.length = 1 ∧
      (disposeClaims leftAccount leftClaim rivalClaim).1.demand = sharedCell ∧
      receiptLedger (disposeClaims leftAccount leftClaim rivalClaim).1.occurrence.state =
        leftReceiptLedger ∧
      retainProposal ready (.unqualified [9, 1]) = ready ∧
      ready.ledger.productions = inheritedLedger := by
  have refused : Scoped.merge? leftClaim rivalClaim = none :=
    Scoped.conflicting_claims_refused leftClaim rivalClaim rival_receipt_claim_is_supported
      (identity := leftProductionId) (first := 0) (second := 1)
      (by decide) (by decide) (by decide)
  have kept := dispose_keeps_the_payload_account leftAccount leftClaim rivalClaim
  refine ⟨refused, kept, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · unfold disposeClaims
    rw [refused]
  · rw [kept]
    exact receipt_left_branch_earns_one_production.2.2.1
  · rw [kept]
    decide
  · rw [kept]
    rfl
  · rw [kept]
    exact receipt_left_branch_earns_one_production.1

private theorem adopt_two_keeps_the_occurrence (account : PayloadAccount)
    (first second : (PayloadOccurrence ⊕ PayloadOccurrence) × Nat) :
    (adoptPayload account [first, second]).occurrence = account.occurrence := by
  unfold adoptPayload
  split <;> simp_all

theorem receipt_residual_keeps_both_branch_ledgers :
    (advancePayload payloadReady).cut.length = 2 ∧
      (advancePayload payloadReady).occurrence = payloadReady.occurrence ∧
      (advancePayload payloadReady).paidProduction = 1 ∧
      (advancePayload payloadReady).cut.map
          (fun leaf => receiptLedger (retained leaf.1).state) =
        [leftReceiptLedger, rightReceiptLedger] ∧
      receiptLedger payloadReady.occurrence.state = suspensionReceiptLedger := by
  have length : payloadRun.length = 2 := by decide
  have readyCut : payloadReady.cut = payloadSuspendedCut := by
    unfold payloadReady adoptPayload
    rfl
  have advanced : advanceCut payloadReady.cut = payloadRun := by
    rw [readyCut]
    exact payload_sequence_is_the_source_run
  refine ⟨by decide, ?_, by decide, by decide, receipt_suspension_is_the_unfinished_prefix.1⟩
  unfold advancePayload
  rw [advanced]
  match hrun : payloadRun with
  | [] => simp [hrun] at length
  | head :: rest =>
      cases rest with
      | nil => simp [hrun] at length
      | cons next more =>
          cases more with
          | cons _ _ => simp [hrun] at length
          | nil =>
              exact adopt_two_keeps_the_occurrence payloadReady head next

theorem receipt_stale_world_keeps_the_left_ledger :
    let result := resumeBranch 0 [] leftAccount.occurrence.state.world.heap.spine
      {Right.inspect} payloadReady
    payloadRefused .staleWorld result = true ∧
      (payloadKept result).paidProduction = 2 ∧
      (payloadKept result).cut.length = 1 ∧
      receiptLedger (payloadKept result).occurrence.state = leftReceiptLedger ∧
      productionLedgerOf (payloadKept result).occurrence.state = [leftProductionEntry] := by
  decide

theorem receipt_missing_right_keeps_the_suspension_ledger :
    let refusedAccount := { payloadReady with rights := {Right.inspect} }
    let result := payloadCheckpoint payloadReady.occurrence.state.world.path
      payloadReady.occurrence.state.world.heap.spine ∅ refusedAccount
    payloadRefused .missingRights result = true ∧
      (payloadKept result).paidProduction = 1 ∧
      receiptLedger (payloadKept result).occurrence.state = suspensionReceiptLedger ∧
      productionLedgerOf (payloadKept result).occurrence.state = [] ∧
      (payloadKept result).occurrence.state.control =
        .force sharedCell [.resume (.afterDemand sharedCell)] := by
  decide

theorem receipt_cancellation_keeps_the_right_production_cell :
    productionLedgerOf rightAccount.occurrence.state = [rightProductionEntry] ∧
      rightProductionEntry.identity.1 = sharedCell ∧
      bindingCell ∉ compoundValue.referenceSet ∧
      (collect
          (payloadResources rightAccount.occurrence.state right_branch_is_anchored.1
            right_branch_is_anchored.2.1.1)
          (roots (trimLog (cancelConsumer (consumersOf compoundValue) 0)))).lookup
        sharedCell =
        (payloadResources rightAccount.occurrence.state right_branch_is_anchored.1
          right_branch_is_anchored.2.1.1).lookup sharedCell := by
  refine ⟨receipt_right_branch_earns_the_other_production.2.1, rfl,
    compound_value_retains_two_occurrences.2.2.2, ?_⟩
  have cells := payload_cells_come_from_the_run
  have halted : rightAccount.occurrence.state.control =
      .halted (.value compoundValue) := by
    have all := payload_run_keeps_both_worlds.2
    have length : payloadRun.length = 2 := by decide
    match hrun : payloadRun with
    | [] => simp [hrun] at length
    | _left :: rest =>
        cases rest with
        | nil => simp [hrun] at length
        | cons right more =>
            cases more with
            | cons _ _ => simp [hrun] at length
            | nil =>
                have account : rightAccount = branchAccount right := by
                  simp [rightAccount, hrun]
                have flag := (List.all_eq_true.mp all) right (by simp [hrun])
                have controlFlag := (Bool.and_eq_true_iff.mp flag).2
                have controlEq := decide_eq_true_eq.mp controlFlag
                simpa [account, branchAccount, retained] using controlEq
  have preserved := payload_cancellation_preserves_the_other_live_payload
    rightAccount.occurrence.state right_branch_is_anchored.1 right_branch_is_anchored.2.1 6
    cells.2.2.1 cells.2.2.2.2.1 cells.2.2.2.2.2.2 halted
  exact preserved.2.2.1

theorem receipt_production_cell_is_in_the_suspension_census :
    leftProductionEntry.identity.1 = sharedCell ∧
      bindingAllocationFactor.dependency = .allocate bindingCell (.symbol 8) ∧
      bindingCell ∉ compoundValue.referenceSet ∧
      sharedCell ∈ compoundValue.referenceSet ∧
      census
          (payloadResources payloadReady.occurrence.state payload_ready_is_anchored.1
            payload_ready_is_anchored.2.1.1)
          (payloadInventory.controlRoots (0 : Nat) payloadReady.occurrence.state.control) =
        {bindingCell, sharedCell} := by
  exact ⟨rfl, rfl, compound_value_retains_two_occurrences.2.2.2, by decide,
    payload_suspension_footprint⟩

theorem receipt_erased_current_keeps_the_receipt_ledger :
    receiptLedger erasedPayloadAccount.occurrence.state =
      receiptLedger leftAccount.occurrence.state ∧
      payloadAdmitted (payloadCheckpoint leftAccount.occurrence.state.world.path
        leftAccount.occurrence.state.world.heap.spine {Right.inspect}
        erasedPayloadAccount) = true ∧
      ¬ erasedPayloadAccount.occurrence.state.world.heap.Recorded := by
  exact ⟨by unfold erasedPayloadAccount erasePayloadCurrent receiptLedger chronologicalReceipts; rfl,
    payload_erased_singleton_is_admitted.1, payload_erased_current_is_not_recorded⟩

theorem receipt_account_is_not_the_supplied_ledger :
    denote leftReceiptLedger = ⟨[0, 0, 0]⟩ ∧
      denote inheritedLedger = ⟨[1, 9]⟩ ∧
      inheritedLedger.map Factor.identity = [1, 7] ∧
      denote leftReceiptLedger ≠ denote inheritedLedger ∧
      ready.delivery = Controls.sharedCycle ∧
      rootAddresses (logRoots Nat ready.delivery.log) = {(0 : Fin 3)} ∧
      retainProposal ready (.unqualified [9, 1]) = ready := by
  exact ⟨by decide, by decide, by decide, by decide, rfl,
    shared_cycle_is_not_the_payload_root_census.2.1, rfl⟩

/-! ## World admission and the semantic production ledger

The eight-entry source-order word compares receipt-world coefficients. It is
not either returned world's receipt account. `disposeAdmitted` refuses that
cross-world use and also refuses a same-world proposal whose productions are
not the receipt ledger the source machine wrote. Both accounts and both
proposals stay in either case.

The shared `NeedQualifiedReplay.traceReplay` reads a successor trace through
`productionReceipt?` and a coefficient assignment in any coefficient monoid. It
is specialized below for the natural-number payload and joint runs. The factor reader takes that assignment and the
machine about to step; it does not take the spec. The trace reader takes
the spec because it calls `step`. Its ledger is `productionLedger` of that
history, including a proper prefix and an incoming ledger kept in front.
The history induction is shared. The payload run and the later same-world
execution only instantiate it. Neither stores a second account beside the
source ledger, and neither proof repeats the induction. Factor order is
the source order. Commutativity is not assumed. The helper is stated at
`Type` because `pathMachine` and `historyEventPath` are. Generalizing it
to `Type*` remains open.
-/

open Mettapedia.Machines.BranchLocalNeed.NeedInteractionValuation
open Mettapedia.Machines.BranchLocalNeed.NeedCacheLaws
open Mettapedia.Machines.BranchLocalNeed.NeedInteractionAuthority
open Mettapedia.Machines.BranchLocalNeed.NeedInferenceControl.Reference
open Mettapedia.GSLT.Causality.OccurrenceMachineHistory
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.OSLF.Binding
open _root_.CategoryTheory

/-- One coefficient grade for every production receipt of this source family.
Grade `2` is the assignment used by the payload run and the joint execution.
Grades `0` and `1` use the same replay and do not drop a receipt. -/
def sourceCoefficient (grade : Nat) :
    CompletedReceipt (Val CellId) Unit Unit → Nat :=
  fun _receipt => grade

def payloadSemanticAssignment :
    CompletedReceipt (Val CellId) Unit Unit → Nat :=
  sourceCoefficient 2

theorem payload_coefficient_uses_the_semantic_assignment :
    payloadCoefficient = productionCoefficient payloadSemanticAssignment := rfl

abbrev PayloadSemanticLedger :=
  Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat


def semanticProductionFactor? (before : PayloadMachine) :
    Option (Factor (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat) :=
  traceProductionFactor? payloadSemanticAssignment before

/-- The payload instance of `traceReplay`. -/
def semanticReplay (before : PayloadMachine) :
    List Nat → Option (PayloadMachine × PayloadSemanticLedger) :=
  traceReplay payloadSpec payloadSemanticAssignment before

def replayLedger (trace : List Nat) : Option PayloadSemanticLedger :=
  (semanticReplay payloadStart trace).map Prod.snd

def leftSemanticLedger : PayloadSemanticLedger :=
  [⟨(sharedCell, leftProductionId), .value (.sym 5), 2⟩]

def rightSemanticLedger : PayloadSemanticLedger :=
  [⟨(sharedCell, rightProductionId), .value (.sym 6), 2⟩]

def leftWorldTrace : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0]

def rightWorldTrace : List Nat := [0, 0, 0, 1, 0, 0, 0, 0, 0]

def leftPaidTrace : List Nat := [0, 0, 0, 0, 0, 0]

def rightPaidTrace : List Nat := [0, 0, 0, 1, 0, 0]

def suspensionTrace : List Nat := [0, 0, 0]

private theorem semanticReplay_append (before : PayloadMachine)
    (first second : List Nat) :
    semanticReplay before (first ++ second) =
      (semanticReplay before first).bind fun earlier =>
        (semanticReplay earlier.1 second).map fun later =>
          (later.1, earlier.2 ++ later.2) := by
  simpa [semanticReplay] using
    trace_replay_append payloadSpec payloadSemanticAssignment before first second

private theorem one_step_production_ledger (before after : PayloadMachine)
    (index : Nat) (stepped : (step payloadSpec before)[index]? = some after) :
    productionLedger payloadSpec payloadSemanticAssignment
        (EventPath.cons (presentation := machinePresentation payloadSpec)
          (source := before) (middle := after) (target := after) (site := index)
          (⟨stepped⟩ : OccurrenceEvidence payloadSpec index before after)
          (.nil (presentation := machinePresentation payloadSpec) after)) =
      (semanticProductionFactor? before).toList := by
  simpa [semanticProductionFactor?] using
    one_step_trace_ledger payloadSpec payloadSemanticAssignment before after index stepped

/-- Every real history's production ledger is the replay of its successor
indices. The history keeps the administrative steps; the ledger keeps only
production receipts and the semantic coefficient. -/
theorem semanticReplay_of_history
    {source target : RewriteEventHistory.State
      (system (pathMachine payloadSpec payloadStart))}
    (history : Quiver.Path source target) :
    semanticReplay source.term (indices (pathMachine payloadSpec payloadStart) history) =
      some (target.term,
        productionLedger payloadSpec payloadSemanticAssignment
          (historyEventPath payloadSpec payloadStart history)) := by
  simpa [semanticReplay] using
    trace_replay_of_history payloadSpec payloadSemanticAssignment payloadStart history

private theorem semantic_ledger_of_member (fuel : Nat)
    {leaf : (PayloadOccurrence ⊕ PayloadOccurrence) × Nat}
    (member : leaf ∈ contributions payloadSource fuel payloadInitial)
    {trace : List Nat} {expected : PayloadSemanticLedger}
    (traceEq : (retained leaf.1).trace = trace)
    (replayed : replayLedger trace = some expected) :
    ∃ history : History (pathMachine payloadSpec payloadStart) payloadStart
        (retained leaf.1).state,
      indices (pathMachine payloadSpec payloadStart) history = trace ∧
        productionLedger payloadSpec payloadSemanticAssignment
            (historyEventPath payloadSpec payloadStart history) = expected ∧
          Valid expected ∧
          denote expected = leaf.2 := by
  exact trace_account_of_contribution payloadSpec payloadSemanticAssignment payloadStart
    fuel member traceEq (by simpa [replayLedger, semanticReplay] using replayed)

/-- A real contribution transports its incoming coefficient, generic
production ledger, and recorded current heap together. The ledger is
`productionLedger`, not a second calculus. -/
theorem source_contribution_transport (fuel : Nat)
    {leaf : (PayloadOccurrence ⊕ PayloadOccurrence) × Nat}
    (member : leaf ∈ contributions payloadSource fuel payloadInitial)
    {trace : List Nat} {expected : PayloadSemanticLedger}
    (traceEq : (retained leaf.1).trace = trace)
    (replayed : replayLedger trace = some expected) :
    ∃ history : History (pathMachine payloadSpec payloadStart) payloadStart
        (retained leaf.1).state,
      indices (pathMachine payloadSpec payloadStart) history = trace ∧
        productionLedger payloadSpec payloadSemanticAssignment
            (historyEventPath payloadSpec payloadStart history) = expected ∧
          Valid expected ∧
          denote expected = leaf.2 ∧
          (retained leaf.1).state.world.heap.Recorded ∧
          payloadDiscipline.machineClosed (retained leaf.1).state := by
  obtain ⟨history, indicesEq, productionEq, validLedger, denoted⟩ :=
    semantic_ledger_of_member fuel member traceEq replayed
  obtain ⟨recorded, closed⟩ :=
    payload_contributions_stay_anchored fuel payloadInitial payload_initial_is_anchored
      leaf member
  exact ⟨history, indicesEq, productionEq, validLedger, denoted, recorded, closed⟩

structure PayloadDisposition where
  leftAccount : PayloadAccount
  rightAccount : PayloadAccount
  leftProposal : PayloadClaim
  rightProposal : PayloadClaim
  joined : Option PayloadReceiptLedger

def sourceLedgerAdmitted (account : PayloadAccount) (claim : PayloadClaim) : Bool :=
  decide (claim.productions = receiptLedger account.occurrence.state)

/-- OR worlds are refused before any algebraic merge. Same-world proposals
join only when claim merge succeeds and the merged productions are the
receipt ledger that world's source machine wrote. Printed identifiers that
fail that test are refused. Both accounts and both proposals are retained. -/
def disposeAdmitted (left right : PayloadAccount)
    (leftProposal rightProposal : PayloadClaim) : PayloadDisposition :=
  let joined :=
    if decide (left.occurrence.state.world.path = right.occurrence.state.world.path) then
      match Scoped.merge? leftProposal rightProposal with
      | some merged =>
          if sourceLedgerAdmitted left leftProposal &&
              sourceLedgerAdmitted right rightProposal &&
              decide (merged.productions = receiptLedger left.occurrence.state) then
            some merged.productions
          else
            none
      | none => none
    else
      none
  ⟨left, right, leftProposal, rightProposal, joined⟩

theorem disposeAdmitted_retains_the_proposals
    (left right : PayloadAccount) (leftProposal rightProposal : PayloadClaim) :
    (disposeAdmitted left right leftProposal rightProposal).leftAccount = left ∧
      (disposeAdmitted left right leftProposal rightProposal).rightAccount = right ∧
      (disposeAdmitted left right leftProposal rightProposal).leftProposal = leftProposal ∧
      (disposeAdmitted left right leftProposal rightProposal).rightProposal = rightProposal := by
  unfold disposeAdmitted
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Different world paths are the OR boundary. The algebraic merge is not
consulted, and both accounts and both proposals stay. -/
theorem split_paths_refuse_the_join
    (left right : PayloadAccount) (leftProposal rightProposal : PayloadClaim)
    (distinct : left.occurrence.state.world.path ≠ right.occurrence.state.world.path) :
    (disposeAdmitted left right leftProposal rightProposal).joined = none := by
  have paths :
      decide (left.occurrence.state.world.path = right.occurrence.state.world.path) = false :=
    decide_eq_false distinct
  unfold disposeAdmitted
  rw [paths]
  rfl

/-- Same-world copies join only to the receipt ledger the source machine
wrote. This is shared observation of one ledger. -/
theorem admitted_tests_join_the_written_ledger
    (left right : PayloadAccount) (leftProposal rightProposal : PayloadClaim)
    (samePath : left.occurrence.state.world.path = right.occurrence.state.world.path)
    (merged : PayloadClaim)
    (mergeEq : Scoped.merge? leftProposal rightProposal = some merged)
    (leftSource : sourceLedgerAdmitted left leftProposal = true)
    (rightSource : sourceLedgerAdmitted right rightProposal = true)
    (written : merged.productions = receiptLedger left.occurrence.state) :
    (disposeAdmitted left right leftProposal rightProposal).joined =
        some (receiptLedger left.occurrence.state) ∧
      (disposeAdmitted left right leftProposal rightProposal).leftAccount = left ∧
      (disposeAdmitted left right leftProposal rightProposal).rightAccount = right ∧
      (disposeAdmitted left right leftProposal rightProposal).leftProposal = leftProposal ∧
      (disposeAdmitted left right leftProposal rightProposal).rightProposal = rightProposal := by
  have paths :
      decide (left.occurrence.state.world.path = right.occurrence.state.world.path) = true :=
    decide_eq_true samePath
  have gate :
      (sourceLedgerAdmitted left leftProposal &&
          sourceLedgerAdmitted right rightProposal &&
          decide (merged.productions = receiptLedger left.occurrence.state)) = true := by
    rw [leftSource, rightSource, decide_eq_true written]
    rfl
  unfold disposeAdmitted
  rw [paths, mergeEq]
  dsimp
  rw [gate, written]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem failed_source_test_refuses_the_join
    (left right : PayloadAccount) (leftProposal rightProposal : PayloadClaim)
    (samePath : left.occurrence.state.world.path = right.occurrence.state.world.path)
    (merged : PayloadClaim)
    (mergeEq : Scoped.merge? leftProposal rightProposal = some merged)
    (rejected :
      (sourceLedgerAdmitted left leftProposal &&
          sourceLedgerAdmitted right rightProposal &&
          decide (merged.productions = receiptLedger left.occurrence.state)) = false) :
    (disposeAdmitted left right leftProposal rightProposal).joined = none ∧
      (disposeAdmitted left right leftProposal rightProposal).leftAccount = left ∧
      (disposeAdmitted left right leftProposal rightProposal).rightAccount = right ∧
      (disposeAdmitted left right leftProposal rightProposal).leftProposal = leftProposal ∧
      (disposeAdmitted left right leftProposal rightProposal).rightProposal = rightProposal := by
  have paths :
      decide (left.occurrence.state.world.path = right.occurrence.state.world.path) = true :=
    decide_eq_true samePath
  unfold disposeAdmitted
  rw [paths, mergeEq]
  dsimp
  rw [rejected]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem failed_claim_merge_refuses_the_join
    (left right : PayloadAccount) (leftProposal rightProposal : PayloadClaim)
    (samePath : left.occurrence.state.world.path = right.occurrence.state.world.path)
    (mergeEq : Scoped.merge? leftProposal rightProposal = none) :
    (disposeAdmitted left right leftProposal rightProposal).joined = none ∧
      (disposeAdmitted left right leftProposal rightProposal).leftAccount = left ∧
      (disposeAdmitted left right leftProposal rightProposal).rightAccount = right ∧
      (disposeAdmitted left right leftProposal rightProposal).leftProposal = leftProposal ∧
      (disposeAdmitted left right leftProposal rightProposal).rightProposal = rightProposal := by
  have paths :
      decide (left.occurrence.state.world.path = right.occurrence.state.world.path) = true :=
    decide_eq_true samePath
  unfold disposeAdmitted
  rw [paths, mergeEq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem checkpoint_keeps_its_account
    (expectedPath : WorldPath)
    (expectedSpine : List (HeapUpdate PayloadOrigin (Val CellId) Unit))
    (requested : Rights) (account : PayloadAccount) :
    payloadKept (payloadCheckpoint expectedPath expectedSpine requested account) = account := by
  unfold payloadCheckpoint
  split
  · unfold payloadKept
    rfl
  · split
    · unfold payloadKept
      rfl
    · split
      · unfold payloadKept
        rfl
      · split
        · unfold payloadKept
          rfl
        · split
          · unfold payloadKept
            rfl
          · split
            · unfold payloadKept
              rfl
            · split
              · unfold payloadKept
                rfl
              · unfold payloadKept
                rfl

/-- The concrete eight-entry sidecar. It is the algebraic source-order word,
not a source ledger of either returned world. -/
def sidecarClaim : PayloadClaim :=
  ⟨leftReceiptLedger ++ rightFreshReceipts,
    fun identity => (leftClaim.claims identity).or (rightClaim.claims identity)⟩

theorem replay_reads_these_traces :
    replayLedger suspensionTrace = some ([] : PayloadSemanticLedger) ∧
      replayLedger leftPaidTrace = some leftSemanticLedger ∧
      replayLedger rightPaidTrace = some rightSemanticLedger ∧
      replayLedger leftWorldTrace = some leftSemanticLedger ∧
      replayLedger rightWorldTrace = some rightSemanticLedger ∧
      denote leftSemanticLedger = 2 ∧
      denote rightSemanticLedger = 2 ∧
      denote ([] : PayloadSemanticLedger) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rfl

theorem receipt_cross_world_merge_is_neither_branch_account :
    (leftReceiptLedger ++ rightFreshReceipts).length = 8 ∧
      leftReceiptLedger.length = 5 ∧
      rightReceiptLedger.length = 5 ∧
      (disposeClaims leftAccount leftClaim rightClaim).1 = leftAccount ∧
      ∃ merged : PayloadClaim,
        (disposeClaims leftAccount leftClaim rightClaim).2 = some merged ∧
          merged.productions = leftReceiptLedger ++ rightFreshReceipts ∧
          merged.productions ≠ receiptLedger leftAccount.occurrence.state ∧
          merged.productions ≠ receiptLedger rightAccount.occurrence.state := by
  obtain ⟨merged, _, production, _, _, _, _, disposition⟩ :=
    receipt_agreed_claims_merge_in_source_order
  refine ⟨by decide, by decide, by decide,
    dispose_keeps_the_payload_account leftAccount leftClaim rightClaim, ?_⟩
  refine ⟨merged, disposition, production, ?_, ?_⟩
  · intro same
    have lengths := congrArg List.length same
    rw [production] at lengths
    have joined : (leftReceiptLedger ++ rightFreshReceipts).length = 8 := by decide
    have actual : (receiptLedger leftAccount.occurrence.state).length = 5 := by decide
    rw [joined, actual] at lengths
    omega
  · intro same
    have lengths := congrArg List.length same
    rw [production] at lengths
    have joined : (leftReceiptLedger ++ rightFreshReceipts).length = 8 := by decide
    have actual : (receiptLedger rightAccount.occurrence.state).length = 5 := by decide
    rw [joined, actual] at lengths
    omega

theorem or_worlds_keep_both_accounts :
    ∃ merged : PayloadClaim,
      Scoped.merge? leftClaim rightClaim = some merged ∧
        merged.productions.length = 8 ∧
        (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).joined = none ∧
        (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).leftProposal.productions =
          leftReceiptLedger ∧
        (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).rightProposal.productions =
          rightReceiptLedger ∧
        (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).leftAccount.paidProduction =
          2 ∧
        (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).rightAccount.paidProduction =
          2 ∧
        (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).leftAccount.demand =
          sharedCell ∧
        (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).rightAccount.demand =
          sharedCell ∧
        receiptLedger (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).leftAccount.occurrence.state =
          leftReceiptLedger ∧
        receiptLedger (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).rightAccount.occurrence.state =
          rightReceiptLedger := by
  obtain ⟨merged, mergeEq, production, _, _, _, _, _⟩ :=
    receipt_agreed_claims_merge_in_source_order
  refine ⟨merged, mergeEq, ?_,
    split_paths_refuse_the_join leftAccount rightAccount leftClaim rightClaim
      payload_branches_do_not_join.2.2.2,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  rw [production]
  decide

theorem same_world_admission_joins_the_written_ledger :
    (disposeAdmitted leftAccount leftAccount leftClaim leftClaim).joined =
        some leftReceiptLedger ∧
      (disposeAdmitted leftAccount leftAccount leftClaim leftClaim).joined ≠
        some (leftReceiptLedger ++ rightFreshReceipts) ∧
      leftReceiptLedger.length = 5 ∧
      denote leftReceiptLedger = ⟨[0, 0, 0]⟩ ∧
      denote leftSemanticLedger = 2 ∧
      leftAccount.paidProduction = 2 ∧
      occurrencesOf compoundValue = [sharedCell, sharedCell] := by
  have joined :
      (disposeAdmitted leftAccount leftAccount leftClaim leftClaim).joined =
        some leftReceiptLedger := by
    decide
  refine ⟨joined, ?_, by decide, by decide, by decide, by decide,
    compound_value_retains_two_occurrences.1⟩
  intro same
  rw [joined] at same
  injection same with lists
  have lengths := congrArg List.length lists
  have sourceLength : leftReceiptLedger.length = 5 := by decide
  have sidecarLength : (leftReceiptLedger ++ rightFreshReceipts).length = 8 := by decide
  rw [sourceLength, sidecarLength] at lengths
  omega

theorem same_world_printed_sidecar_is_refused :
    sidecarClaim.productions = leftReceiptLedger ++ rightFreshReceipts ∧
      (disposeAdmitted leftAccount leftAccount leftClaim sidecarClaim).joined = none ∧
      (disposeAdmitted leftAccount leftAccount sidecarClaim sidecarClaim).joined = none ∧
      (disposeAdmitted leftAccount leftAccount leftClaim sidecarClaim).leftProposal.productions =
        leftReceiptLedger ∧
      (disposeAdmitted leftAccount leftAccount leftClaim sidecarClaim).rightProposal.productions =
        sidecarClaim.productions := by
  decide

theorem rival_proposals_are_retained :
    (disposeAdmitted leftAccount leftAccount leftClaim rivalClaim).joined = none ∧
      (disposeAdmitted leftAccount leftAccount leftClaim rivalClaim).leftProposal.productions =
        leftReceiptLedger ∧
      (disposeAdmitted leftAccount leftAccount leftClaim rivalClaim).rightProposal.productions =
        leftReceiptLedger ∧
      (disposeAdmitted leftAccount leftAccount leftClaim rivalClaim).leftProposal.claims
          leftProductionId = some 0 ∧
      (disposeAdmitted leftAccount leftAccount leftClaim rivalClaim).rightProposal.claims
          leftProductionId = some 1 ∧
      (disposeAdmitted leftAccount leftAccount leftClaim rivalClaim).leftAccount.paidProduction =
        2 ∧
      (disposeAdmitted leftAccount leftAccount leftClaim rivalClaim).leftAccount.cut.length = 1 := by
  decide

def paidPendingCut : PayloadCut := contributions payloadSource 6 payloadInitial

def continuePaid : PayloadCut :=
  sequence paidPendingCut fun leaf =>
    match leaf with
    | .inl done => [(.inl done, (1 : Nat))]
    | .inr pending => contributions payloadSource 4 pending

def restartPaid : PayloadCut :=
  paidPendingCut.flatMap fun item =>
    match item.1 with
    | .inl _ => []
    | .inr pending => contributions payloadSource 4 pending

/-- Path, successor trace, payment, receipt ledger, and halted flag.
The semantic production ledger is not stored here. It is the history
account proved from `productionLedger`. -/
private def executionView (cut : PayloadCut) :
    List (List Nat × List Nat × Nat × PayloadReceiptLedger × Bool) :=
  cut.map fun item =>
    let occurrence := retained item.1
    (occurrence.state.world.path, occurrence.trace, item.2,
      receiptLedger occurrence.state, isHalted occurrence.state)

theorem suspension_coefficient_work_stays_unfinished :
    ∃ leaf ∈ payloadSuspendedCut,
      payloadReady.occurrence = retained leaf.1 ∧
        payloadReady.paidProduction = leaf.2 ∧
        ∃ history : History (pathMachine payloadSpec payloadStart) payloadStart
            (retained leaf.1).state,
          indices (pathMachine payloadSpec payloadStart) history = suspensionTrace ∧
            productionLedger payloadSpec payloadSemanticAssignment
                (historyEventPath payloadSpec payloadStart history) = [] ∧
              Valid ([] : PayloadSemanticLedger) ∧
              denote ([] : PayloadSemanticLedger) = 1 ∧
              suspensionTrace.length = 3 ∧
              payloadReady.paidProduction = 1 ∧
              payloadReady.occurrence.state.control =
                .force sharedCell [.resume (.afterDemand sharedCell)] ∧
              receiptLedger payloadReady.occurrence.state = suspensionReceiptLedger ∧
              productionLedgerOf payloadReady.occurrence.state = [] ∧
              denote suspensionReceiptLedger = ⟨[]⟩ ∧
              (disposeAdmitted payloadReady payloadReady suspensionClaim
                  suspensionClaim).joined = some suspensionReceiptLedger := by
  have length : payloadSuspendedCut.length = 1 := by decide
  match hcut : payloadSuspendedCut with
  | [] => simp [hcut] at length
  | leaf :: rest =>
      cases rest with
      | cons _ _ => simp [hcut] at length
      | nil =>
          have occurrence : payloadReady.occurrence = retained leaf.1 := by
            cases leaf with
            | mk which _paid =>
                cases which with
                | inl _ =>
                    have pending : payloadSuspendedCut.all (fun item =>
                        match item.1 with | .inl _ => false | .inr _ => true) = true := by
                      decide
                    simp [hcut] at pending
                | inr pending =>
                    simp [payloadReady, adoptPayload, hcut, retained]
          have paidEq : payloadReady.paidProduction = leaf.2 := by
            cases leaf with
            | mk which paid =>
                cases which with
                | inl _ =>
                    have pending : payloadSuspendedCut.all (fun item =>
                        match item.1 with | .inl _ => false | .inr _ => true) = true := by
                      decide
                    simp [hcut] at pending
                | inr pending =>
                    simp [payloadReady, adoptPayload, hcut]
          have member : leaf ∈ contributions payloadSource 3 payloadInitial := by
            rw [show contributions payloadSource 3 payloadInitial =
                payloadSuspendedCut from rfl, hcut]
            exact List.mem_cons_self
          have traceEq : (retained leaf.1).trace = suspensionTrace := by
            have traces : payloadSuspendedCut.map (fun item => (retained item.1).trace) =
                [suspensionTrace] := by
              decide
            rw [hcut] at traces
            simp at traces
            exact traces
          obtain ⟨history, indicesEq, productionEq, validLedger, denoted, _recorded, _closed⟩ :=
            source_contribution_transport 3 member traceEq replay_reads_these_traces.1
          refine ⟨leaf, ?_, occurrence, paidEq, history, indicesEq, productionEq,
            validLedger, ?_, rfl, receipt_suspension_is_the_unfinished_prefix.2.2.2.1,
            receipt_suspension_is_the_unfinished_prefix.2.2.2.2,
            receipt_suspension_is_the_unfinished_prefix.1,
            receipt_suspension_is_the_unfinished_prefix.2.1,
            receipt_suspension_is_the_unfinished_prefix.2.2.1, by decide⟩
          · exact List.mem_cons_self
          · rw [show denote ([] : PayloadSemanticLedger) = leaf.2 from by
              simpa [productionEq] using denoted, ← paidEq]
            exact receipt_suspension_is_the_unfinished_prefix.2.2.2.1

theorem paid_receipt_projection_is_not_completion :
    executionView paidPendingCut =
        [([0], leftPaidTrace, 2, leftReceiptLedger, false),
          ([1], rightPaidTrace, 2, rightReceiptLedger, false)] ∧
      executionView payloadRun =
        [([0], leftWorldTrace, 2, leftReceiptLedger, true),
          ([1], rightWorldTrace, 2, rightReceiptLedger, true)] ∧
      ∃ leaf ∈ paidPendingCut, ∃ history :
          History (pathMachine payloadSpec payloadStart) payloadStart
            (retained leaf.1).state,
        (retained leaf.1).trace = leftPaidTrace ∧
          productionLedger payloadSpec payloadSemanticAssignment
              (historyEventPath payloadSpec payloadStart history) = leftSemanticLedger ∧
            denote leftSemanticLedger = 2 ∧
            isHalted (retained leaf.1).state = false ∧
            receiptLedger (retained leaf.1).state = leftReceiptLedger ∧
            leftPaidTrace.length = 6 ∧
            leftSemanticLedger.length = 1 := by
  have pendingView :
      executionView paidPendingCut =
        [([0], leftPaidTrace, 2, leftReceiptLedger, false),
          ([1], rightPaidTrace, 2, rightReceiptLedger, false)] := by
    rfl
  have returnedView :
      executionView payloadRun =
        [([0], leftWorldTrace, 2, leftReceiptLedger, true),
          ([1], rightWorldTrace, 2, rightReceiptLedger, true)] := by
    rfl
  have witness :
      ∃ leaf ∈ paidPendingCut, ∃ history :
          History (pathMachine payloadSpec payloadStart) payloadStart
            (retained leaf.1).state,
        (retained leaf.1).trace = leftPaidTrace ∧
          productionLedger payloadSpec payloadSemanticAssignment
              (historyEventPath payloadSpec payloadStart history) = leftSemanticLedger ∧
            denote leftSemanticLedger = 2 ∧
            isHalted (retained leaf.1).state = false ∧
            receiptLedger (retained leaf.1).state = leftReceiptLedger ∧
            leftPaidTrace.length = 6 ∧
            leftSemanticLedger.length = 1 := by
    have length : paidPendingCut.length = 2 := by decide
    match hcut : paidPendingCut with
    | [] => simp [hcut] at length
    | leaf :: rest =>
        cases rest with
        | nil => simp [hcut] at length
        | cons _next more =>
            cases more with
            | cons _ _ => simp [hcut] at length
            | nil =>
                have member : leaf ∈ contributions payloadSource 6 payloadInitial := by
                  rw [show contributions payloadSource 6 payloadInitial =
                      paidPendingCut from rfl, hcut]
                  exact List.mem_cons_self
                have traceEq : (retained leaf.1).trace = leftPaidTrace := by
                  have viewed := pendingView
                  simp [executionView, hcut] at viewed
                  exact viewed.1.2.1
                obtain ⟨history, _indicesEq, productionEq, _valid, denoted, _recorded, _closed⟩ :=
                  source_contribution_transport 6 member traceEq replay_reads_these_traces.2.1
                have haltedFlag : isHalted (retained leaf.1).state = false := by
                  have viewed := pendingView
                  simp [executionView, hcut] at viewed
                  exact viewed.1.2.2.2.2
                have ledgerFlag : receiptLedger (retained leaf.1).state =
                    leftReceiptLedger := by
                  have viewed := pendingView
                  simp [executionView, hcut] at viewed
                  exact viewed.1.2.2.2.1
                have payment : leaf.2 = 2 := by
                  have viewed := pendingView
                  simp [executionView, hcut] at viewed
                  exact viewed.1.2.2.1
                refine ⟨leaf, ?_, history, traceEq, productionEq, ?_, haltedFlag,
                  ledgerFlag, rfl, rfl⟩
                · exact List.mem_cons_self
                · rw [show denote leftSemanticLedger = leaf.2 from by
                    simpa [productionEq] using denoted, payment]
  exact ⟨pendingView, returnedView, witness⟩

/-- A later source slice keeps the coefficient already earned. Returned
leaves stay at the monoid unit. Pending leaves take the next slice. -/
theorem source_cut_continues_with_the_incoming_coefficient (first second : Nat) :
    contributions payloadSource (first + second) payloadInitial =
      sequence (contributions payloadSource first payloadInitial) fun leaf =>
        match leaf with
        | .inl answer => [(.inl answer, 1)]
        | .inr pending => contributions payloadSource second pending := by
  have added := contributions_add payloadSource first second payloadInitial
  rw [added]
  apply congrArg fun continuation =>
    sequence (contributions payloadSource first payloadInitial) continuation
  funext leaf
  cases leaf <;> rfl

theorem returned_residual_repeats_at_coefficient_one
    {fuel : Nat} {cut : PayloadCut}
    (cutEq : contributions payloadSource fuel payloadInitial = cut)
    (returned : cut.all (fun leaf => leaf.1.isLeft) = true) :
    contributions payloadSource (fuel + 1) payloadInitial =
      cut.map (fun item => (item.1, item.2 * 1)) := by
  have sequenced := contributions_add payloadSource fuel 1 payloadInitial
  rw [cutEq] at sequenced
  have preserved := continue_without_pending payloadSource 1 cut returned
  have same : contributions payloadSource (fuel + 1) payloadInitial = cut :=
    sequenced.trans preserved
  rw [same]
  simp [mul_one]

theorem continue_paid_is_the_source_run :
    continuePaid = payloadRun := by
  unfold continuePaid paidPendingCut payloadRun
  have fuel : (6 + 4 : Nat) = 3 + 7 := rfl
  rw [← fuel]
  exact (source_cut_continues_with_the_incoming_coefficient 6 4).symm

theorem restarted_suffix_loses_the_incoming_payment :
    continuePaid = payloadRun ∧
      executionView continuePaid =
        [([0], leftWorldTrace, 2, leftReceiptLedger, true),
          ([1], rightWorldTrace, 2, rightReceiptLedger, true)] ∧
      executionView restartPaid =
        [([0], leftWorldTrace, 1, leftReceiptLedger, true),
          ([1], rightWorldTrace, 1, rightReceiptLedger, true)] := by
  refine ⟨continue_paid_is_the_source_run, ?_, rfl⟩
  simpa [continue_paid_is_the_source_run] using
    paid_receipt_projection_is_not_completion.2.1

theorem repeated_observation_keeps_the_production_identity :
    payloadRun.all (fun leaf => leaf.1.isLeft) = true ∧
      contributions payloadSource 11 payloadInitial =
        payloadRun.map (fun item => (item.1, item.2 * 1)) ∧
      executionView (contributions payloadSource 11 payloadInitial) =
        executionView payloadRun ∧
      executionView payloadRun =
        [([0], leftWorldTrace, 2, leftReceiptLedger, true),
          ([1], rightWorldTrace, 2, rightReceiptLedger, true)] := by
  have returned : payloadRun.all (fun leaf => leaf.1.isLeft) = true := by
    decide
  have repeated :=
    returned_residual_repeats_at_coefficient_one
      (show contributions payloadSource (3 + 7) payloadInitial = payloadRun from rfl)
      returned
  have fuel : ((3 + 7) + 1 : Nat) = 11 := rfl
  rw [fuel] at repeated
  have sameCut : contributions payloadSource 11 payloadInitial = payloadRun := by
    rw [repeated]
    simp [mul_one]
  refine ⟨returned, repeated, ?_, paid_receipt_projection_is_not_completion.2.1⟩
  · rw [sameCut]

theorem left_semantic_ledger_is_the_production_payment :
    ∃ leaf ∈ payloadRun, ∃ history :
        History (pathMachine payloadSpec payloadStart) payloadStart
          (retained leaf.1).state,
      leftAccount.occurrence = retained leaf.1 ∧
        indices (pathMachine payloadSpec payloadStart) history = leftWorldTrace ∧
        productionLedger payloadSpec payloadSemanticAssignment
            (historyEventPath payloadSpec payloadStart history) = leftSemanticLedger ∧
          Valid leftSemanticLedger ∧
          denote leftSemanticLedger = leftAccount.paidProduction ∧
          leftAccount.paidProduction = 2 ∧
          leftSemanticLedger = [⟨(sharedCell, leftProductionId), .value (.sym 5), 2⟩] ∧
          productionLedgerOf leftAccount.occurrence.state = [leftProductionEntry] ∧
          leftProductionEntry.identity = (sharedCell, leftProductionId) ∧
          leftProductionEntry.coefficient = ⟨[0]⟩ ∧
          denote leftReceiptLedger = ⟨[0, 0, 0]⟩ ∧
          leftWorldTrace.length = 9 ∧
          leftSemanticLedger.length = 1 := by
  have length : payloadRun.length = 2 := by decide
  match hrun : payloadRun with
  | [] => simp [hrun] at length
  | leaf :: rest =>
      cases rest with
      | nil => simp [hrun] at length
      | cons _right more =>
          cases more with
          | cons _ _ => simp [hrun] at length
          | nil =>
              have account : leftAccount = branchAccount leaf := by
                simp [leftAccount, hrun]
              have member : leaf ∈ contributions payloadSource (3 + 7) payloadInitial := by
                rw [show contributions payloadSource (3 + 7) payloadInitial =
                    payloadRun from rfl, hrun]
                exact List.mem_cons_self
              have traceEq : (retained leaf.1).trace = leftWorldTrace := by
                have traces : payloadRun.map (fun item => (retained item.1).trace) =
                    [leftWorldTrace, rightWorldTrace] := by
                  decide
                rw [hrun] at traces
                simp at traces
                exact traces.1
              have occurrence : leftAccount.occurrence = retained leaf.1 := by
                simp [account, branchAccount, retained]
              have paid : leaf.2 = leftAccount.paidProduction := by
                simp [account, branchAccount]
              obtain ⟨history, indicesEq, productionEq, validLedger, denoted, _recorded, _closed⟩ :=
                source_contribution_transport (3 + 7) member traceEq
                  replay_reads_these_traces.2.2.2.1
              refine ⟨leaf, ?_, history, occurrence, indicesEq, productionEq, validLedger,
                ?_, receipt_left_branch_earns_one_production.2.2.1, rfl,
                receipt_left_branch_earns_one_production.2.1, rfl, rfl,
                receipt_left_branch_earns_one_production.2.2.2.1, rfl, rfl⟩
              · exact List.mem_cons_self
              · simpa [productionEq, paid] using denoted

theorem right_semantic_ledger_is_the_production_payment :
    ∃ leaf ∈ payloadRun, ∃ history :
        History (pathMachine payloadSpec payloadStart) payloadStart
          (retained leaf.1).state,
      rightAccount.occurrence = retained leaf.1 ∧
        indices (pathMachine payloadSpec payloadStart) history = rightWorldTrace ∧
        productionLedger payloadSpec payloadSemanticAssignment
            (historyEventPath payloadSpec payloadStart history) = rightSemanticLedger ∧
          denote rightSemanticLedger = rightAccount.paidProduction ∧
          rightAccount.paidProduction = 2 ∧
          rightSemanticLedger = [⟨(sharedCell, rightProductionId), .value (.sym 6), 2⟩] ∧
          productionLedgerOf rightAccount.occurrence.state = [rightProductionEntry] ∧
          rightProductionEntry.coefficient = ⟨[1]⟩ ∧
          denote rightReceiptLedger = ⟨[1, 1, 1]⟩ ∧
          rightWorldTrace.length = 9 ∧
          rightSemanticLedger.length = 1 ∧
          leftProductionId ≠ rightProductionId := by
  have length : payloadRun.length = 2 := by decide
  match hrun : payloadRun with
  | [] => simp [hrun] at length
  | leftLeaf :: rest =>
      cases rest with
      | nil => simp [hrun] at length
      | cons leaf more =>
          cases more with
          | cons _ _ => simp [hrun] at length
          | nil =>
              have account : rightAccount = branchAccount leaf := by
                simp [rightAccount, hrun]
              have member : leaf ∈ contributions payloadSource (3 + 7) payloadInitial := by
                rw [show contributions payloadSource (3 + 7) payloadInitial =
                    payloadRun from rfl, hrun]
                exact List.mem_cons_of_mem leftLeaf List.mem_cons_self
              have traceEq : (retained leaf.1).trace = rightWorldTrace := by
                have traces : payloadRun.map (fun item => (retained item.1).trace) =
                    [leftWorldTrace, rightWorldTrace] := by
                  decide
                rw [hrun] at traces
                simp at traces
                exact traces.2
              have occurrence : rightAccount.occurrence = retained leaf.1 := by
                simp [account, branchAccount, retained]
              have paid : leaf.2 = rightAccount.paidProduction := by
                simp [account, branchAccount]
              obtain ⟨history, indicesEq, productionEq, _valid, denoted, _recorded, _closed⟩ :=
                source_contribution_transport (3 + 7) member traceEq
                  replay_reads_these_traces.2.2.2.2.1
              refine ⟨leaf, ?_, history, occurrence, indicesEq, productionEq, ?_,
                receipt_right_branch_earns_the_other_production.2.2.1, rfl,
                receipt_right_branch_earns_the_other_production.2.1, rfl,
                receipt_right_branch_earns_the_other_production.2.2.2.1, rfl, rfl,
                receipt_right_branch_earns_the_other_production.2.2.2.2.2⟩
              · exact List.mem_cons_of_mem leftLeaf List.mem_cons_self
              · simpa [productionEq, paid] using denoted

theorem split_resumption_keeps_both_source_accounts :
    leftAccount.occurrence.state.world.path ≠ rightAccount.occurrence.state.world.path ∧
      (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).joined = none ∧
      (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).leftAccount =
        leftAccount ∧
      (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).rightAccount =
        rightAccount ∧
      (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).leftProposal =
        leftClaim ∧
      (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).rightProposal =
        rightClaim ∧
      payloadRefused .splitWorlds (payloadCheckpoint [] [] {Right.inspect}
        (advancePayload payloadReady)) = true ∧
      leftAccount.paidProduction = 2 ∧
      rightAccount.paidProduction = 2 ∧
      occurrencesOf compoundValue = [sharedCell, sharedCell] := by
  have distinct := payload_branches_do_not_join.2.2.2
  have kept :=
    disposeAdmitted_retains_the_proposals leftAccount rightAccount leftClaim rightClaim
  exact ⟨distinct,
    split_paths_refuse_the_join leftAccount rightAccount leftClaim rightClaim distinct,
    kept.1, kept.2.1, kept.2.2.1, kept.2.2.2, payload_joined_resume_is_split_worlds,
    receipt_left_branch_earns_one_production.2.2.1,
    receipt_right_branch_earns_the_other_production.2.2.1,
    compound_value_retains_two_occurrences.1⟩

theorem returned_pending_delivery_keeps_the_earned_payment :
    executionView paidPendingCut =
        [([0], leftPaidTrace, 2, leftReceiptLedger, false),
          ([1], rightPaidTrace, 2, rightReceiptLedger, false)] ∧
      replayLedger leftPaidTrace = some leftSemanticLedger ∧
      denote leftSemanticLedger = 2 ∧
      replayLedger rightPaidTrace = some rightSemanticLedger ∧
      denote rightSemanticLedger = 2 ∧
      payloadOperationRights paidPendingCut = {Right.force} ∧
      ∀ leaf ∈ paidPendingCut,
        (retained leaf.1).state.world.heap.Recorded ∧
          payloadDiscipline.machineClosed (retained leaf.1).state ∧
          leaf.2 = 2 := by
  refine ⟨paid_receipt_projection_is_not_completion.1, replay_reads_these_traces.2.1,
    replay_reads_these_traces.2.2.2.2.2.1, replay_reads_these_traces.2.2.1,
    replay_reads_these_traces.2.2.2.2.2.2.1, ?_, ?_⟩
  · decide
  · intro leaf member
    have anchored :=
      payload_contributions_stay_anchored 6 payloadInitial payload_initial_is_anchored leaf
        (by simpa [paidPendingCut] using member)
    have payments : paidPendingCut.all (fun item => decide (item.2 = 2)) = true := by
      decide
    exact ⟨anchored.1, anchored.2,
      decide_eq_true_eq.mp ((List.all_eq_true.mp payments) leaf member)⟩

theorem rejected_delivery_keeps_the_full_account :
    payloadRefused .missingRights (payloadCheckpoint payloadReady.occurrence.state.world.path
        payloadReady.occurrence.state.world.heap.spine ∅
        { payloadReady with rights := {Right.inspect} }) = true ∧
      payloadKept (payloadCheckpoint payloadReady.occurrence.state.world.path
        payloadReady.occurrence.state.world.heap.spine ∅
        { payloadReady with rights := {Right.inspect} }) =
        { payloadReady with rights := {Right.inspect} } ∧
      (disposeAdmitted leftAccount leftAccount leftClaim rivalClaim).joined = none ∧
      (disposeAdmitted leftAccount leftAccount leftClaim rivalClaim).leftAccount =
        leftAccount ∧
      (disposeAdmitted leftAccount leftAccount leftClaim rivalClaim).leftProposal =
        leftClaim ∧
      (disposeAdmitted leftAccount leftAccount leftClaim rivalClaim).rightProposal =
        rivalClaim ∧
      leftClaim.productions = leftReceiptLedger ∧
      rivalClaim.productions = leftReceiptLedger ∧
      (disposeAdmitted leftAccount leftAccount leftClaim sidecarClaim).joined = none ∧
      (disposeAdmitted leftAccount leftAccount leftClaim sidecarClaim).rightProposal =
        sidecarClaim ∧
      sidecarClaim.productions = leftReceiptLedger ++ rightFreshReceipts := by
  have keptInput :=
    checkpoint_keeps_its_account payloadReady.occurrence.state.world.path
      payloadReady.occurrence.state.world.heap.spine ∅
      { payloadReady with rights := {Right.inspect} }
  have rivalKept :=
    disposeAdmitted_retains_the_proposals leftAccount leftAccount leftClaim rivalClaim
  have sidecarKept :=
    disposeAdmitted_retains_the_proposals leftAccount leftAccount leftClaim sidecarClaim
  exact ⟨payload_pending_empty_request_needs_force, keptInput, rival_proposals_are_retained.1,
    rivalKept.1, rivalKept.2.2.1, rivalKept.2.2.2, rfl, rfl,
    same_world_printed_sidecar_is_refused.2.1, sidecarKept.2.2.2,
    same_world_printed_sidecar_is_refused.1⟩

theorem accepted_final_return_does_not_release_the_other_owner :
    payloadAdmitted (payloadCheckpoint leftAccount.occurrence.state.world.path
        leftAccount.occurrence.state.world.heap.spine ∅ leftAccount) = true ∧
      payloadOperationRights leftAccount.cut = {Right.inspect} ∧
      unread (cancelConsumer (consumersOf compoundValue) 0).log 0 = [] ∧
      unread (cancelConsumer (consumersOf compoundValue) 0).log 1 =
        [sharedCell, sharedCell] ∧
      rightAccount.occurrence.state.world.path = [1] ∧
      rightAccount.paidProduction = 2 ∧
      leftAccount.paidProduction = 2 ∧
      leftAccount.demand = sharedCell ∧
      rightAccount.demand = sharedCell := by
  exact ⟨payload_returned_inspection_accepts_an_empty_request.1,
    payload_returned_inspection_accepts_an_empty_request.2,
    cancellation_drops_only_the_one_consumer.1, cancellation_drops_only_the_one_consumer.2,
    payload_branches_do_not_join.2.2.1,
    receipt_right_branch_earns_the_other_production.2.2.1,
    receipt_left_branch_earns_one_production.2.2.1, by decide, by decide⟩

theorem accepted_final_return_leaves_the_unforced_payload :
    payloadAdmitted (payloadCheckpoint leftAccount.occurrence.state.world.path
        leftAccount.occurrence.state.world.heap.spine ∅ leftAccount) = true ∧
      payloadRefused .missingRights (payloadCheckpoint payloadReady.occurrence.state.world.path
        payloadReady.occurrence.state.world.heap.spine ∅
        { payloadReady with rights := {Right.inspect} }) = true ∧
      payloadReady.paidProduction = 1 ∧
      payloadReady.occurrence.state.control =
        .force sharedCell [.resume (.afterDemand sharedCell)] ∧
      isHalted payloadReady.occurrence.state = false ∧
      payloadReady.demand = sharedCell ∧
      payloadReady.rights = {Right.force, Right.inspect} := by
  refine ⟨payload_returned_inspection_accepts_an_empty_request.1,
    payload_pending_empty_request_needs_force,
    receipt_suspension_is_the_unfinished_prefix.2.2.2.1,
    receipt_suspension_is_the_unfinished_prefix.2.2.2.2, ?_, by decide, by decide⟩
  unfold isHalted
  rw [receipt_suspension_is_the_unfinished_prefix.2.2.2.2]

theorem cancelled_consumer_keeps_the_other_live_root :
    let machine := leftAccount.occurrence.state
    let resources :=
      payloadResources machine left_branch_is_anchored.1 left_branch_is_anchored.2.1.1
    payloadAdmitted (payloadCheckpoint leftAccount.occurrence.state.world.path
        leftAccount.occurrence.state.world.heap.spine ∅ leftAccount) = true ∧
      (collect resources (roots (trimLog (cancelConsumer (consumersOf compoundValue) 0)))).lookup
          sharedCell = resources.lookup sharedCell ∧
        (collect resources (roots (trimLog (cancelConsumer (consumersOf compoundValue) 0)))).lookup
            bindingCell = resources.lookup bindingCell ∧
          occurrencesOf compoundValue = [sharedCell, sharedCell] ∧
            leftAccount.paidProduction = 2 ∧
              rightAccount.paidProduction = 2 ∧
                leftAccount.occurrence.state.world.heap.Recorded ∧
                  rightAccount.occurrence.state.world.heap.Recorded := by
  have preserved := left_payload_cancellation_preserves_the_other_consumer
  refine ⟨payload_returned_inspection_accepts_an_empty_request.1, ?_, ?_,
    compound_value_retains_two_occurrences.1,
    receipt_left_branch_earns_one_production.2.2.1,
    receipt_right_branch_earns_the_other_production.2.2.1,
    left_branch_is_anchored.1, right_branch_is_anchored.1⟩
  · exact preserved.1
  · exact preserved.2.1

/-- Copies of one written ledger are shared observation of that ledger.
An independent AND join needs two distinct source productions in one
recorded world. These productions differ, and their worlds are `[0]` and
`[1]`. That witness is not this run. -/
theorem copied_ledger_is_not_an_independent_and :
    (disposeAdmitted leftAccount leftAccount leftClaim leftClaim).joined =
        some leftReceiptLedger ∧
      leftReceiptLedger.length = 5 ∧
      denote leftSemanticLedger = 2 ∧
      denote leftReceiptLedger = ⟨[0, 0, 0]⟩ ∧
      leftAccount.occurrence.state.world.heap.Recorded ∧
      rightAccount.occurrence.state.world.heap.Recorded ∧
      leftAccount.occurrence.state.world.heap ≠ rightAccount.occurrence.state.world.heap ∧
      leftProductionId ≠ rightProductionId ∧
      leftAccount.occurrence.state.world.path ≠ rightAccount.occurrence.state.world.path ∧
      (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).joined = none := by
  exact ⟨same_world_admission_joins_the_written_ledger.1,
    same_world_admission_joins_the_written_ledger.2.2.1,
    same_world_admission_joins_the_written_ledger.2.2.2.2.1,
    same_world_admission_joins_the_written_ledger.2.2.2.1,
    left_branch_is_anchored.1, right_branch_is_anchored.1,
    payload_branch_heaps_stay_separate,
    receipt_right_branch_earns_the_other_production.2.2.2.2.2,
    payload_branches_do_not_join.2.2.2,
    split_paths_refuse_the_join leftAccount rightAccount leftClaim rightClaim
      payload_branches_do_not_join.2.2.2⟩

end LiveRoots

/-! ## Same-world independent productions

Two singleton forces, issued in source order against two cells allocated
before either fork. The productions are not sibling OR worlds and they are
not two copies of one ledger. The combined account is the production ledger
of this one execution. Lookup agreement of the two cache writes is not
permission to reorder their spines, and a synchronized valuation is not the
independent grade of either production.
-/

section JointSource

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
open Mettapedia.Machines.BranchLocalNeed.NeedReference.Heap
open Mettapedia.Machines.BranchLocalNeed.NeedInteractionValuation
open Mettapedia.GSLT.Dynamics.EffectTraceInterleaving
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.IndependentEventValuationProduct
open Mettapedia.GSLT.Dynamics.EventValuationFunctor
open Mettapedia.Machines.BranchLocalNeed.NeedInferenceControl.Reference
open Mettapedia.Machines.BranchLocalNeed.NeedInteractionAuthority
open Mettapedia.GSLT.Causality.OccurrenceMachineHistory
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open _root_.CategoryTheory

inductive JointOrigin where
  | symbol (name : Nat)
  deriving DecidableEq, Repr

inductive JointRule where
  | sole
  deriving DecidableEq, Repr

inductive JointResume where
  | afterLeft
  | afterRight (left : CellId)
  | afterLeftValue (left right : CellId)
  | afterRightValue (left right : CellId)
  deriving DecidableEq, Repr

inductive JointLocal where
  | start
  | haveLeft (left : CellId)
  | haveRight (left right : CellId)
  | needRight (left right : CellId)
  | finish (left right : CellId)
  | emit (name : Nat)
  deriving DecidableEq, Repr

abbrev JointMachine :=
  Machine JointOrigin JointLocal JointResume JointRule (Val CellId) Unit Unit Unit

abbrev JointOccurrence := WorkOccurrence JointMachine

abbrev JointCut := List ((JointOccurrence ⊕ JointOccurrence) × Nat)

def jointSpec :
    Spec JointOrigin JointLocal JointResume JointRule (Val CellId) Unit Unit Unit where
  alternatives
    | .symbol name => [(.sole, .emit name)]
  action
    | .start => .allocate (.symbol 3) .afterLeft
    | .haveLeft left => .allocate (.symbol 4) (.afterRight left)
    | .haveRight left right => .demand left (.afterLeftValue left right)
    | .needRight left right => .demand right (.afterRightValue left right)
    | .finish left right => .done (.value (.app (.need left) (.need right)))
    | .emit name => .done (.value (.sym name))
  afterDemand
    | .afterLeftValue left right, .value _ => .needRight left right
    | .afterRightValue left right, .value _ => .finish left right
    | .afterLeft, _ => .start
    | .afterRight _, _ => .start
    | .afterLeftValue _ _, _ => .start
    | .afterRightValue _ _, _ => .start
  afterAllocation
    | .afterLeft, cell => .haveLeft cell
    | .afterRight left, cell => .haveRight left cell
    | .afterLeftValue _ _, _ => .start
    | .afterRightValue _ _, _ => .start

def jointLeftCell : CellId := ⟨2, [], 0, 0⟩

def jointRightCell : CellId := ⟨2, [], 1, 0⟩

def jointCoefficient : JointMachine → JointMachine → Nat :=
  productionCoefficient (fun _ => (2 : Nat))

def jointSource : Coalgebra JointOccurrence JointOccurrence Nat :=
  source jointSpec jointCoefficient

def jointStart : JointMachine :=
  { world :=
      { lineage := 2
        path := []
        heap := empty
        receipts := ReceiptGraph.empty
        nextCell := 0
        nextEvaluator := 0 }
    control := .run .start [] }

def jointInitial : JointOccurrence := ⟨jointStart, []⟩

/-- Admission keeps the account it was given. A rejected delivery does not
install a replacement, and an accepted delivery does not allocate a new one. -/
inductive RetainedAdmit (Account : Type) where
  | accept (account : Account)
  | reject (reason : Refusal) (kept : Account)

def RetainedAdmit.kept {Account : Type} : RetainedAdmit Account → Account
  | .accept account => account
  | .reject _ account => account

def admitRetainedCut {Account : Type} (nonempty uniformPaths uniformSpines agrees
    expectedPath expectedSpine rightsHeld requestHeld : Bool) (account : Account) :
    RetainedAdmit Account :=
  if !nonempty then
    .reject .incompleteResidual account
  else if !uniformPaths || !uniformSpines then
    .reject .splitWorlds account
  else if !agrees then
    .reject .incoherentResidual account
  else if !expectedPath then
    .reject .staleWorld account
  else if !expectedSpine then
    .reject .changedDependency account
  else if !rightsHeld || !requestHeld then
    .reject .missingRights account
  else
    .accept account

theorem admitRetainedCut_keeps {Account : Type}
    (nonempty uniformPaths uniformSpines agrees expectedPath expectedSpine
      rightsHeld requestHeld : Bool) (account : Account) :
    (admitRetainedCut nonempty uniformPaths uniformSpines agrees expectedPath
      expectedSpine rightsHeld requestHeld account).kept = account := by
  cases nonempty <;> cases uniformPaths <;> cases uniformSpines <;> cases agrees <;>
    cases expectedPath <;> cases expectedSpine <;> cases rightsHeld <;>
    cases requestHeld <;>
    simp [admitRetainedCut, RetainedAdmit.kept]

theorem joint_source_cut_continues (first second : Nat) :
    contributions jointSource (first + second) jointInitial =
      sequence (contributions jointSource first jointInitial) fun leaf =>
        match leaf with
        | .inl answer => [(.inl answer, (1 : Nat))]
        | .inr pending => contributions jointSource second pending := by
  unfold jointSource
  have added := resume_exact jointSpec jointCoefficient first second jointInitial
  rw [added]
  apply congrArg fun continuation =>
    sequence (contributions (source jointSpec jointCoefficient) first jointInitial) continuation
  funext leaf
  cases leaf <;> rfl

/-- Nested fork words `⟨[0]⟩` and `⟨[0, 0]⟩` denote the same product either
way. That equality is not an execution interchange. The negative control is
a word whose two orders differ. -/
theorem nested_fork_words_commute_and_branch_words_do_not :
    (⟨[0]⟩ : Coeff) * ⟨[0, 0]⟩ = ⟨[0, 0]⟩ * ⟨[0]⟩ ∧
      (⟨[0, 1]⟩ : Coeff) * ⟨[1]⟩ ≠ ⟨[1]⟩ * ⟨[0, 1]⟩ := by
  decide

abbrev JointRecord (Origin Value StableFault : Type*) :=
  Mettapedia.Machines.BranchLocalNeed.NeedReference.CellRecord Origin Value StableFault

abbrev JointCacheState (Value StableFault : Type*) :=
  Mettapedia.Machines.BranchLocalNeed.NeedReference.Cache Value StableFault

inductive CellWrite (Origin Value StableFault : Type*) where
  | set (cell : CellId) (record : JointRecord Origin Value StableFault)
      (state : JointCacheState Value StableFault)

def applyCellWrite {Origin Value StableFault : Type*}
    (heap : Heap Origin Value StableFault) :
    CellWrite Origin Value StableFault → Heap Origin Value StableFault
  | .set cell record state => heap.setKnownCache cell record state

def observeCellPair {Origin Value StableFault : Type*} (left right : CellId)
    (heap : Heap Origin Value StableFault) :
    Option (JointRecord Origin Value StableFault) ×
      Option (JointRecord Origin Value StableFault) :=
  (heap.lookup left, heap.lookup right)

theorem observeCellPair_respects_the_write
    {Origin Value StableFault : Type*} (left right : CellId)
    {first second : Heap Origin Value StableFault}
    (agreed : observeCellPair left right first = observeCellPair left right second)
    (event : CellWrite Origin Value StableFault) :
    observeCellPair left right (applyCellWrite first event) =
      observeCellPair left right (applyCellWrite second event) := by
  cases event with
  | set cell record state =>
      obtain ⟨leftEq, rightEq⟩ := Prod.ext_iff.mp agreed
      unfold observeCellPair at leftEq rightEq
      dsimp only at leftEq rightEq
      by_cases cellLeft : cell = left
      · subst cell
        by_cases same : left = right
        · subst right
          simp [observeCellPair, applyCellWrite, Heap.setKnownCache_lookup_same]
        · have rightDiff : right ≠ left := fun eq => same eq.symm
          simp [observeCellPair, applyCellWrite, Heap.setKnownCache_lookup_same,
            Heap.setKnownCache_preserves_other, rightDiff, rightEq]
      · by_cases cellRight : cell = right
        · subst cell
          have leftDiff : left ≠ right := fun eq => cellLeft eq.symm
          simp [observeCellPair, applyCellWrite, Heap.setKnownCache_lookup_same,
            Heap.setKnownCache_preserves_other, leftDiff, leftEq]
        · have leftDiff : left ≠ cell := fun eq => cellLeft eq.symm
          have rightDiff : right ≠ cell := fun eq => cellRight eq.symm
          simp [observeCellPair, applyCellWrite, Heap.setKnownCache_preserves_other,
            leftDiff, rightDiff, leftEq, rightEq]

theorem distinct_cell_writes_commute_at_the_pair
    {Origin Value StableFault : Type*}
    {left right : CellId} (distinct : left ≠ right)
    (leftRecord rightRecord : JointRecord Origin Value StableFault)
    (leftState rightState : JointCacheState Value StableFault)
    (heap : Heap Origin Value StableFault) :
    observeCellPair left right
        (applyCellWrite (applyCellWrite heap (.set left leftRecord leftState))
          (.set right rightRecord rightState)) =
      observeCellPair left right
        (applyCellWrite (applyCellWrite heap (.set right rightRecord rightState))
          (.set left leftRecord leftState)) := by
  simp [observeCellPair, applyCellWrite, Heap.setKnownCache_lookup_same,
    Heap.setKnownCache_preserves_other, distinct, distinct.symm]

/-- The two cache writes may be read in either order. `EffectTraceInterleaving`
supplies the observer schedule. The heaps themselves stay in source order. -/
theorem swapped_distinct_writes_keep_both_lookups
    {Origin Value StableFault : Type*}
    {left right : CellId} (distinct : left ≠ right)
    (leftRecord rightRecord : JointRecord Origin Value StableFault)
    (leftState rightState : JointCacheState Value StableFault)
    (heap : Heap Origin Value StableFault) :
    observeCellPair left right
        (run applyCellWrite heap
          [.set right rightRecord rightState, .set left leftRecord leftState]) =
      observeCellPair left right
        (run applyCellWrite heap
          [.set left leftRecord leftState, .set right rightRecord rightState]) := by
  refine observed_run_eq_leftSerial_of_crossCommutes applyCellWrite
      (observeCellPair left right) ?_
      (Shuffle.append_commuted [.set left leftRecord leftState]
        [.set right rightRecord rightState]) ?_ heap
  · intro first second agreed event
    exact observeCellPair_respects_the_write left right agreed event
  · intro leftEvent leftMember rightEvent rightMember state
    obtain rfl := List.mem_singleton.mp leftMember
    obtain rfl := List.mem_singleton.mp rightMember
    exact distinct_cell_writes_commute_at_the_pair distinct leftRecord rightRecord
      leftState rightState state

theorem distinct_cell_writes_do_not_commute_as_heaps
    {Origin Value StableFault : Type*}
    (heap : Heap Origin Value StableFault)
    {left right : CellId} (distinct : left ≠ right)
    (leftRecord rightRecord : JointRecord Origin Value StableFault)
    (leftState rightState : JointCacheState Value StableFault) :
    ¬ CrossCommutes applyCellWrite
        [.set left leftRecord leftState] [.set right rightRecord rightState] := by
  intro commutes
  have same := commutes (.set left leftRecord leftState) List.mem_cons_self
    (.set right rightRecord rightState) List.mem_cons_self heap
  have spines := congrArg Heap.spine same
  simp only [applyCellWrite, Heap.setKnownCache] at spines
  injection spines with head _
  injection head with cellEq _
  exact distinct cellEq.symm

/-- A grade that knows only its own cell still reports that cell. The
synchronized product of the two grades is `none` on that singleton history,
because the other grade refuses the event. -/
def paymentOn (cell : CellId) : Valuation CellId where
  Grade := Nat
  algebra := additivePartialMonoid Nat
  grade := fun event => if event = cell then some 2 else none

theorem left_production_is_independently_visible :
    independentGrade (paymentOn jointLeftCell) (paymentOn jointRightCell)
        [jointLeftCell] = (some (2 : Nat), (none : Option Nat)) ∧
      functorGrade ((paymentOn jointLeftCell).prod (paymentOn jointRightCell))
          [jointLeftCell] = (none : Option (Nat × Nat)) := by
  constructor
  · simp [independentGrade, functorGrade_eq_historyGrade, paymentOn, jointLeftCell,
        jointRightCell, Valuation.historyGrade_cons, Valuation.historyGrade_nil,
        additivePartialMonoid]
  · simp [functorGrade_eq_historyGrade, paymentOn, jointLeftCell, jointRightCell,
        Valuation.historyGrade_cons, Valuation.historyGrade_nil, additivePartialMonoid]

theorem joint_cell_marks_keep_source_order :
    (chronological fun cell : CellId =>
        if cell = jointLeftCell then (0 : Nat) else 1).historyGrade
        [jointLeftCell, jointRightCell] = some [0, 1] ∧
      (chronological fun cell : CellId =>
          if cell = jointLeftCell then (0 : Nat) else 1).historyGrade
          [jointRightCell, jointLeftCell] = some [1, 0] := by
  simp only [chronological_historyGrade]
  decide

/-! ### One source account for both productions

The ledger is `productionLedger` of this execution, recovered by the same
`traceReplay` lemma as the payload history. Prefixes are incomplete cuts.
An incoming ledger stays in front of the suffix, and the payment multiplies
in that order.
-/

def jointAssignment : CompletedReceipt (Val CellId) Unit Unit → Nat :=
  sourceCoefficient 2

theorem joint_coefficient_uses_the_assignment :
    jointCoefficient = productionCoefficient jointAssignment := rfl

def jointLeftFactor :
    Factor (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat :=
  ⟨(jointLeftCell, ⟨[0], 4⟩), .value (.sym 3), 2⟩

def jointRightFactor :
    Factor (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat :=
  ⟨(jointRightCell, ⟨[0, 0], 7⟩), .value (.sym 4), 2⟩

/-- The earned left occurrence at grade `1`. This is a factor, not the empty ledger. -/
def jointUnitFactor :
    Factor (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat :=
  { jointLeftFactor with coefficient := 1 }

/-- The same occurrence at grade `0`. Denotation `0` does not remove it. -/
def jointZeroFactor :
    Factor (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat :=
  { jointLeftFactor with coefficient := 0 }

def jointEarnedLedger :
    Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat :=
  [jointLeftFactor]

def jointProductionLedger :
    Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat :=
  [jointLeftFactor, jointRightFactor]

def jointReversedLedger :
    Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat :=
  [jointRightFactor, jointLeftFactor]

/-- One coefficient-`4` factor. It denotes the same payment as the two
coefficient-`2` occurrences and drops the second occurrence. -/
def jointDeduplicatedLedger :
    Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat :=
  [{ jointLeftFactor with coefficient := 4 }]

def jointForceTrace : List Nat := [0, 0, 0]

def jointEarnedTrace : List Nat := [0, 0, 0, 0, 0, 0]

def jointBothTrace : List Nat := List.replicate 11 0

def jointReturnTrace : List Nat := List.replicate 14 0

/-- An ordered coefficient interpretation of the same two-production source.
The cell labels are words, rather than natural-number multiplicities. -/
def jointOrderedAssignment
    (receipt : CompletedReceipt (Val CellId) Unit Unit) : Coeff :=
  ⟨[receipt.cell.slot]⟩

def jointOrderedLedger :
    Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Coeff :=
  [⟨jointLeftFactor.identity, jointLeftFactor.dependency, ⟨[jointLeftCell.slot]⟩⟩,
   ⟨jointRightFactor.identity, jointRightFactor.dependency, ⟨[jointRightCell.slot]⟩⟩]

/-- Replaying the actual source earns its two ordered factors. Exchanging
their completion order changes the coefficient, although both runs would
have the same natural-number product under the earlier interpretation. -/
theorem joint_source_replay_keeps_ordered_coefficients :
    let replayed :=
      (traceReplay jointSpec jointOrderedAssignment jointStart jointReturnTrace).map Prod.snd
    replayed = some jointOrderedLedger ∧
      (replayed.map fun ledger => (denote ledger).tokens) = some [0, 1] ∧
      (replayed.map fun ledger => (denote ledger).tokens) ≠ some [1, 0] := by
  have earned :
      (traceReplay jointSpec jointOrderedAssignment jointStart jointReturnTrace).map Prod.snd =
        some jointOrderedLedger := by rfl
  refine ⟨earned, ?_, ?_⟩
  · rw [earned]
    rfl
  · rw [earned]
    decide

/-- The suffix starts at the machine actually reconstructed by the prefix.
Keeping its earned factor retains the complete ordered account; resetting
that factor leaves only the later production. -/
theorem joint_ordered_resume_keeps_the_earned_factor :
    let earnedPrefix := traceReplay jointSpec jointOrderedAssignment jointStart jointEarnedTrace
    let resumed := (earnedPrefix.bind fun earlier =>
      traceReplayFrom jointSpec jointOrderedAssignment earlier.2 earlier.1
        (List.replicate 8 0)).map Prod.snd
    let reset := (earnedPrefix.bind fun earlier =>
      traceReplayFrom jointSpec jointOrderedAssignment [] earlier.1
        (List.replicate 8 0)).map Prod.snd
    resumed = some jointOrderedLedger ∧
      (resumed.map fun ledger => (denote ledger).tokens) = some [0, 1] ∧
      (reset.map fun ledger => (denote ledger).tokens) = some [1] ∧
      (reset.map fun ledger => (denote ledger).tokens) ≠ some [0, 1] := by
  refine ⟨by rfl, by rfl, by rfl, ?_⟩
  decide

def jointReplay (trace : List Nat) :
    Option (Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat) :=
  (traceReplay jointSpec jointAssignment jointStart trace).map Prod.snd

/-- The same source trace read at another grade of `sourceCoefficient`. -/
def sourceReplay (grade : Nat) (trace : List Nat) :
    Option (Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat) :=
  (traceReplay jointSpec (sourceCoefficient grade) jointStart trace).map Prod.snd

def jointValue : Val CellId := .app (.need jointLeftCell) (.need jointRightCell)

def jointRun : JointCut := contributions jointSource 15 jointInitial

def jointForceCut : JointCut := contributions jointSource 3 jointInitial

def jointEarnedCut : JointCut := contributions jointSource 6 jointInitial

def jointBothCut : JointCut := contributions jointSource 11 jointInitial

def jointSuspended (name : Nat) : JointRecord JointOrigin (Val CellId) Unit :=
  ⟨.symbol name, .suspended⟩

def jointValued (name : Nat) : JointRecord JointOrigin (Val CellId) Unit :=
  ⟨.symbol name, .value (.sym name)⟩

def jointEvaluating (name owner : Nat) : JointRecord JointOrigin (Val CellId) Unit :=
  ⟨.symbol name, .evaluating owner⟩

def jointCutMark (fuel : Nat) : List (Nat × Nat × List Nat × List Nat × Bool) :=
  (contributions jointSource fuel jointInitial).map fun item =>
    let machine := (retained item.1).state
    (match item.1 with | .inl _ => 1 | .inr _ => 0,
     item.2, machine.world.path, (retained item.1).trace, isHalted machine)

def jointLookupMark (fuel : Nat) :
    List (Option (JointRecord JointOrigin (Val CellId) Unit) ×
      Option (JointRecord JointOrigin (Val CellId) Unit)) :=
  (contributions jointSource fuel jointInitial).map fun item =>
    let heap := (retained item.1).state.world.heap
    (heap.lookup jointLeftCell, heap.lookup jointRightCell)

theorem joint_contributions_stay_recorded (fuel : Nat)
    (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat)
    (member : leaf ∈ contributions jointSource fuel jointInitial) :
    (retained leaf.1).state.world.heap.Recorded := by
  have preserved :=
    contributions_invariant jointSource
      (fun state => state.state.world.heap.Recorded)
      (fun state => state.state.world.heap.Recorded)
      (fun state answer recorded returned => by
        obtain ⟨same, _⟩ :=
          (source_return_iff jointSpec jointCoefficient state answer).mp returned
        cases same
        exact recorded)
      (fun state alternatives recorded branched next nextMember => by
        have notHalted : isHalted state.state = false := by
          cases control : state.state.control with
          | halted _ =>
              simp only [jointSource, source, control] at branched
              exact False.elim (Sum.inl_ne_inr branched)
          | force _ _ =>
              unfold isHalted
              rw [control]
          | run _ _ =>
              unfold isHalted
              rw [control]
          | returned _ _ =>
              unfold isHalted
              rw [control]
        have running := source_branches jointSpec jointCoefficient state notHalted
        have successorsEq :
            successors jointSpec jointCoefficient state = alternatives := by
          have joined := running.symm.trans branched
          injection joined
        rw [← successorsEq] at nextMember
        obtain ⟨_index, found, _trace, _value⟩ :=
          (successor_iff jointSpec jointCoefficient state next.1 next.2).mp nextMember
        exact step_heap_recorded jointSpec state.state next.1.state recorded
          (List.mem_of_getElem? found))
      fuel jointInitial
      (by simpa [jointInitial, jointStart] using
        (empty_recorded : Recorded (empty : Heap JointOrigin (Val CellId) Unit)))
      leaf member
  cases leaf with
  | mk which _coeff =>
      cases which with
      | inl _answer => exact preserved
      | inr _pending => exact preserved

theorem joint_prefix_replays_are_the_source_ledgers :
    jointReplay jointForceTrace = some [] ∧
      jointReplay jointEarnedTrace = some jointEarnedLedger ∧
      jointReplay jointBothTrace = some jointProductionLedger ∧
      jointReplay jointReturnTrace = some jointProductionLedger ∧
      denote jointEarnedLedger = 2 ∧
      denote jointProductionLedger = 4 ∧
      denote ([] : Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat) = 1 ∧
      denote jointReversedLedger = 4 ∧
      jointProductionLedger ≠ jointReversedLedger ∧
      jointEarnedLedger ++ [jointRightFactor] = jointProductionLedger ∧
      denote (jointEarnedLedger ++ [jointRightFactor]) =
        denote jointEarnedLedger * denote [jointRightFactor] := by
  refine ⟨by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, ?_, rfl,
    denote_append _ _⟩
  decide

/-- Grade `1` writes an actual factor. The fuel-3 replay is the empty ledger.
Both denote `1`, and the lists differ. The factor keeps the grade-`2`
occurrence and the recorded production. -/
theorem source_grade_one_is_a_factor_not_the_empty_ledger :
    sourceReplay 1 jointForceTrace = some [] ∧
      sourceReplay 1 jointEarnedTrace = some [jointUnitFactor] ∧
      denote ([] : Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat) = 1 ∧
      denote [jointUnitFactor] = 1 ∧
      ([jointUnitFactor] :
          Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat) ≠ [] ∧
      jointUnitFactor.identity = jointLeftFactor.identity ∧
      jointUnitFactor.dependency = jointLeftFactor.dependency := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  decide

/-- Grade `0` denotes `0` and still records the earned occurrence and its
production. The empty fuel-3 replay is a different list. -/
theorem source_grade_zero_keeps_the_occurrence :
    sourceReplay 0 jointEarnedTrace = some [jointZeroFactor] ∧
      denote [jointZeroFactor] = 0 ∧
      jointZeroFactor.identity = jointLeftFactor.identity ∧
      jointZeroFactor.dependency = jointLeftFactor.dependency ∧
      sourceReplay 0 jointEarnedTrace ≠ some ([] :
        Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat) ∧
      (sourceReplay 0 jointEarnedTrace).map (List.map Factor.identity) =
        (sourceReplay 2 jointEarnedTrace).map (List.map Factor.identity) ∧
      sourceReplay 0 jointForceTrace = some [] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  decide

theorem joint_cut_marks :
    jointCutMark 3 = [(0, 1, [], jointForceTrace, false)] ∧
      jointCutMark 6 = [(0, 2, [0], jointEarnedTrace, false)] ∧
      jointCutMark 11 = [(0, 4, [0, 0], jointBothTrace, false)] ∧
      jointCutMark 15 = [(1, 4, [0, 0], jointReturnTrace, true)] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem joint_cells_materialize_in_source_order :
    jointLookupMark 3 = [(some (jointSuspended 3), some (jointSuspended 4))] ∧
      jointLookupMark 5 = [(some (jointEvaluating 3 0), some (jointSuspended 4))] ∧
      jointLookupMark 6 = [(some (jointValued 3), some (jointSuspended 4))] ∧
      jointLookupMark 10 = [(some (jointValued 3), some (jointEvaluating 4 1))] ∧
      jointLookupMark 11 = [(some (jointValued 3), some (jointValued 4))] ∧
      jointLookupMark 15 = [(some (jointValued 3), some (jointValued 4))] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def jointProductionWitness (fuel : Nat) (cell : CellId) (owner symbol : Nat) : Bool :=
  (contributions jointSource fuel jointInitial).all fun item =>
    decide ((retained item.1).state.world.heap.lookup cell =
        some (jointEvaluating symbol owner)) &&
      match (retained item.1).state.control with
      | .returned (.value (.sym found)) (.commit foundCell foundOwner :: _) =>
          decide (found = symbol && foundCell = cell && foundOwner = owner)
      | _ => false

theorem joint_production_states_name_distinct_owners :
    jointProductionWitness 5 jointLeftCell 0 3 = true ∧
      jointProductionWitness 10 jointRightCell 1 4 = true ∧
      jointLeftCell ≠ jointRightCell ∧
      (0 : Nat) ≠ 1 := by
  decide

private theorem jointMarkFields {a a' b b' : Nat} {c c' d d' : List Nat} {e e' : Bool}
    (eq : ([(a, b, c, d, e)] : List (Nat × Nat × List Nat × List Nat × Bool)) =
      [(a', b', c', d', e')]) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' := by
  injection eq with head _
  injection head with ha rest
  injection rest with hb rest
  injection rest with hc rest
  injection rest with hd he
  exact ⟨ha, hb, hc, hd, he⟩

private theorem joint_one_pending
    (fuel payment : Nat) (path trace : List Nat)
    (shape : jointCutMark fuel = [(0, payment, path, trace, false)]) :
    ∃ pending,
      contributions jointSource fuel jointInitial = [(.inr pending, payment)] ∧
      (retained (.inr pending)).state.world.path = path ∧
      (retained (.inr pending)).trace = trace ∧
      isHalted (retained (.inr pending)).state = false := by
  have length : (contributions jointSource fuel jointInitial).length = 1 := by
    simpa [jointCutMark, List.length_map, List.length_singleton] using
      congrArg List.length shape
  match hcut : contributions jointSource fuel jointInitial with
  | [] => simp [hcut] at length
  | leaf :: rest =>
      cases rest with
      | cons _ _ => simp [hcut] at length
      | nil =>
          cases leaf with
          | mk which paid =>
              cases which with
              | inl _ =>
                  have marked := shape
                  simp only [jointCutMark, hcut, List.map_cons, List.map_nil] at marked
                  obtain ⟨tagEq, _, _, _, _⟩ := jointMarkFields marked
                  exact absurd tagEq (by decide : (1 : Nat) ≠ 0)
              | inr pending =>
                  have marked := shape
                  simp only [jointCutMark, hcut, List.map_cons, List.map_nil] at marked
                  obtain ⟨_, paidEq, pathEq, traceEq, haltedEq⟩ := jointMarkFields marked
                  refine ⟨pending, ?_, pathEq, traceEq, haltedEq⟩
                  exact congrArg (fun coefficient => [(Sum.inr pending, coefficient)]) paidEq

private theorem joint_one_returned
    (fuel payment : Nat) (path trace : List Nat)
    (shape : jointCutMark fuel = [(1, payment, path, trace, true)]) :
    ∃ answer,
      contributions jointSource fuel jointInitial = [(.inl answer, payment)] ∧
      (retained (.inl answer)).state.world.path = path ∧
      (retained (.inl answer)).trace = trace ∧
      isHalted (retained (.inl answer)).state = true := by
  have length : (contributions jointSource fuel jointInitial).length = 1 := by
    simpa [jointCutMark, List.length_map, List.length_singleton] using
      congrArg List.length shape
  match hcut : contributions jointSource fuel jointInitial with
  | [] => simp [hcut] at length
  | leaf :: rest =>
      cases rest with
      | cons _ _ => simp [hcut] at length
      | nil =>
          cases leaf with
          | mk which paid =>
              cases which with
              | inr _ =>
                  have marked := shape
                  simp only [jointCutMark, hcut, List.map_cons, List.map_nil] at marked
                  obtain ⟨tagEq, _, _, _, _⟩ := jointMarkFields marked
                  exact absurd tagEq (by decide : (0 : Nat) ≠ 1)
              | inl answer =>
                  have marked := shape
                  simp only [jointCutMark, hcut, List.map_cons, List.map_nil] at marked
                  obtain ⟨_, paidEq, pathEq, traceEq, haltedEq⟩ := jointMarkFields marked
                  refine ⟨answer, ?_, pathEq, traceEq, haltedEq⟩
                  exact congrArg (fun coefficient => [(Sum.inl answer, coefficient)]) paidEq

private theorem joint_trace_ends_at_the_leaf
    (fuel : Nat)
    {leaf : (JointOccurrence ⊕ JointOccurrence) × Nat}
    (member : leaf ∈ contributions jointSource fuel jointInitial)
    {trace : List Nat}
    {expected : Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat}
    (traceEq : (retained leaf.1).trace = trace)
    (replayed : jointReplay trace = some expected) :
    traceReplay jointSpec jointAssignment jointStart trace =
      some ((retained leaf.1).state, expected) := by
  obtain ⟨history, indicesEq, productionEq, _, _⟩ :=
    trace_account_of_contribution jointSpec jointAssignment jointStart fuel member traceEq
      (by simpa [jointReplay] using replayed)
  have agreed := trace_replay_of_history jointSpec jointAssignment jointStart history
  rw [indicesEq, productionEq] at agreed
  exact agreed

/-- The returned leaf is the account of this source execution. Both factors
are in the production ledger, in source order, and the heap is `Recorded`. -/
theorem joint_returned_source_account :
    ∃ leaf,
      jointRun = [leaf] ∧
      leaf.1.isLeft = true ∧
      leaf.2 = 4 ∧
      (retained leaf.1).trace = jointReturnTrace ∧
      (retained leaf.1).state.world.path = [0, 0] ∧
      isHalted (retained leaf.1).state = true ∧
      (retained leaf.1).state.control = .halted (.value jointValue) ∧
      (retained leaf.1).state.world.heap.lookup jointLeftCell = some (jointValued 3) ∧
      (retained leaf.1).state.world.heap.lookup jointRightCell = some (jointValued 4) ∧
      ∃ history : History (pathMachine jointSpec jointStart) jointStart
          (retained leaf.1).state,
        indices (pathMachine jointSpec jointStart) history = jointReturnTrace ∧
          productionLedger jointSpec jointAssignment
              (historyEventPath jointSpec jointStart history) = jointProductionLedger ∧
            Valid jointProductionLedger ∧
            denote jointProductionLedger = leaf.2 ∧
            (retained leaf.1).state.world.heap.Recorded := by
  obtain ⟨answer, cutEq, pathEq, traceEq, haltedEq⟩ :=
    joint_one_returned 15 4 [0, 0] jointReturnTrace joint_cut_marks.2.2.2
  have member : (.inl answer, 4) ∈ contributions jointSource 15 jointInitial := by
    rw [cutEq]
    exact List.mem_cons_self
  obtain ⟨history, indicesEq, productionEq, validLedger, denoted⟩ :=
    trace_account_of_contribution jointSpec jointAssignment jointStart 15 member traceEq
      (by simpa [jointReplay] using joint_prefix_replays_are_the_source_ledgers.2.2.2.1)
  have recorded := joint_contributions_stay_recorded 15 (.inl answer, 4) member
  have runEq : jointRun = [(.inl answer, 4)] := by
    simpa [jointRun] using cutEq
  have controlEq : (retained (.inl answer)).state.control =
      .halted (.value jointValue) := by
    have controls : jointRun.map (fun item => (retained item.1).state.control) =
        [.halted (.value jointValue)] := by rfl
    rw [runEq] at controls
    simpa [retained] using controls
  have lookups : (retained (.inl answer)).state.world.heap.lookup jointLeftCell =
      some (jointValued 3) ∧
      (retained (.inl answer)).state.world.heap.lookup jointRightCell =
        some (jointValued 4) := by
    have marked := joint_cells_materialize_in_source_order.2.2.2.2.2
    have asRun : jointRun.map (fun item =>
        ((retained item.1).state.world.heap.lookup jointLeftCell,
          (retained item.1).state.world.heap.lookup jointRightCell)) =
        [(some (jointValued 3), some (jointValued 4))] := by
      simpa [jointLookupMark, jointRun] using marked
    rw [runEq] at asRun
    simp only [List.map_cons, List.map_nil, retained] at asRun
    injection asRun with pairEq _
    exact Prod.ext_iff.mp pairEq
  refine ⟨(.inl answer, 4), runEq, rfl, rfl, traceEq, pathEq, haltedEq, controlEq,
    lookups.1, lookups.2, history, indicesEq, productionEq, validLedger, denoted, recorded⟩

/-- Fuel 3 still needs force and has earned no production. Fuel 6 has the
first payment. Fuel 11 has both factors and has not halted. Each cut is a
prefix of the same source execution. -/
theorem joint_incomplete_cuts_keep_the_earned_ledger :
    (∃ leaf,
      jointForceCut = [leaf] ∧ leaf.2 = 1 ∧ isHalted (retained leaf.1).state = false ∧
        ∃ history : History (pathMachine jointSpec jointStart) jointStart
            (retained leaf.1).state,
          productionLedger jointSpec jointAssignment
              (historyEventPath jointSpec jointStart history) = [] ∧
            denote ([] : Ledger (CellId × ReceiptId)
              (Produced (Val CellId) Unit Unit) Nat) = leaf.2 ∧
            (retained leaf.1).state.world.heap.Recorded) ∧
    (∃ leaf,
      jointEarnedCut = [leaf] ∧ leaf.2 = 2 ∧ isHalted (retained leaf.1).state = false ∧
        ∃ history : History (pathMachine jointSpec jointStart) jointStart
            (retained leaf.1).state,
          productionLedger jointSpec jointAssignment
              (historyEventPath jointSpec jointStart history) = jointEarnedLedger ∧
            denote jointEarnedLedger = leaf.2 ∧
            (retained leaf.1).state.world.heap.Recorded) ∧
    (∃ leaf,
      jointBothCut = [leaf] ∧ leaf.2 = 4 ∧ isHalted (retained leaf.1).state = false ∧
        ∃ history : History (pathMachine jointSpec jointStart) jointStart
            (retained leaf.1).state,
          productionLedger jointSpec jointAssignment
              (historyEventPath jointSpec jointStart history) = jointProductionLedger ∧
            denote jointProductionLedger = leaf.2 ∧
            (retained leaf.1).state.world.heap.Recorded) := by
  have replays := joint_prefix_replays_are_the_source_ledgers
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨pending, cutEq, _, traceEq, haltedEq⟩ :=
      joint_one_pending 3 1 [] jointForceTrace joint_cut_marks.1
    have member : (.inr pending, 1) ∈ contributions jointSource 3 jointInitial := by
      rw [cutEq]
      exact List.mem_cons_self
    obtain ⟨history, _, productionEq, _, denoted⟩ :=
      trace_account_of_contribution jointSpec jointAssignment jointStart 3 member traceEq
        (by simpa [jointReplay] using replays.1)
    exact ⟨(.inr pending, 1), by simpa [jointForceCut] using cutEq, rfl, haltedEq, history,
      productionEq, denoted, joint_contributions_stay_recorded 3 (.inr pending, 1) member⟩
  · obtain ⟨pending, cutEq, _, traceEq, haltedEq⟩ :=
      joint_one_pending 6 2 [0] jointEarnedTrace joint_cut_marks.2.1
    have member : (.inr pending, 2) ∈ contributions jointSource 6 jointInitial := by
      rw [cutEq]
      exact List.mem_cons_self
    obtain ⟨history, _, productionEq, _, denoted⟩ :=
      trace_account_of_contribution jointSpec jointAssignment jointStart 6 member traceEq
        (by simpa [jointReplay] using replays.2.1)
    exact ⟨(.inr pending, 2), by simpa [jointEarnedCut] using cutEq, rfl, haltedEq, history,
      productionEq, denoted, joint_contributions_stay_recorded 6 (.inr pending, 2) member⟩
  · obtain ⟨pending, cutEq, _, traceEq, haltedEq⟩ :=
      joint_one_pending 11 4 [0, 0] jointBothTrace joint_cut_marks.2.2.1
    have member : (.inr pending, 4) ∈ contributions jointSource 11 jointInitial := by
      rw [cutEq]
      exact List.mem_cons_self
    obtain ⟨history, _, productionEq, _, denoted⟩ :=
      trace_account_of_contribution jointSpec jointAssignment jointStart 11 member traceEq
        (by simpa [jointReplay] using replays.2.2.1)
    exact ⟨(.inr pending, 4), by simpa [jointBothCut] using cutEq, rfl, haltedEq, history,
      productionEq, denoted, joint_contributions_stay_recorded 11 (.inr pending, 4) member⟩

theorem joint_split_resumption_is_the_source_run :
    contributions jointSource (6 + 9) jointInitial =
      sequence jointEarnedCut fun leaf =>
        match leaf with
        | .inl answer => [(.inl answer, (1 : Nat))]
        | .inr pending => contributions jointSource 9 pending := by
  simpa [jointEarnedCut] using joint_source_cut_continues 6 9

/-- The payment already earned multiplies the suffix payment on the left.
Restarting is not this continuation. -/
theorem joint_incoming_payment_multiplies_the_suffix :
    ∃ pending suffix,
      jointEarnedCut = [(.inr pending, 2)] ∧
      contributions jointSource 9 pending = [suffix] ∧
      suffix.2 = 2 ∧
      (suffix.1, 2 * suffix.2) ∈ jointRun ∧
      (retained (.inr pending)).trace = jointEarnedTrace ∧
      (retained suffix.1).trace = jointReturnTrace ∧
      (traceReplayFrom jointSpec jointAssignment jointEarnedLedger pending.state
          ((retained suffix.1).trace.drop jointEarnedTrace.length)).map Prod.snd =
        some jointProductionLedger := by
  obtain ⟨pending, earnedCut, _, pendingTrace, _⟩ :=
    joint_one_pending 6 2 [0] jointEarnedTrace joint_cut_marks.2.1
  obtain ⟨answer, returnedCut, _, returnedTrace, _⟩ :=
    joint_one_returned 15 4 [0, 0] jointReturnTrace joint_cut_marks.2.2.2
  have earnedMember : (.inr pending, 2) ∈ contributions jointSource 6 jointInitial := by
    rw [earnedCut]
    exact List.mem_cons_self
  have returnedMember : (.inl answer, 4) ∈ contributions jointSource 15 jointInitial := by
    rw [returnedCut]
    exact List.mem_cons_self
  have replays := joint_prefix_replays_are_the_source_ledgers
  have earnedReplay := joint_trace_ends_at_the_leaf 6 earnedMember pendingTrace replays.2.1
  have fullReplay :=
    joint_trace_ends_at_the_leaf 15 returnedMember returnedTrace replays.2.2.2.1
  have earnedList : jointEarnedCut = [(.inr pending, 2)] := by
    simpa [jointEarnedCut] using earnedCut
  have returnedList : jointRun = [(.inl answer, 4)] := by
    simpa [jointRun] using returnedCut
  have sequenced : jointRun =
      (contributions jointSource 9 pending).map
        (fun second => (second.1, (2 : Nat) * second.2)) := by
    have split := joint_split_resumption_is_the_source_run
    rw [earnedList] at split
    simpa [jointRun, Mettapedia.GSLT.Dynamics.WeightedResumption.sequence] using split
  rw [returnedList] at sequenced
  have suffixLength : (contributions jointSource 9 pending).length = 1 := by
    have counted := congrArg List.length sequenced.symm
    simpa using counted
  match hsuffix : contributions jointSource 9 pending with
  | [] => simp [hsuffix] at suffixLength
  | suffix :: more =>
      cases more with
      | cons _ _ => simp [hsuffix] at suffixLength
      | nil =>
          rw [hsuffix] at sequenced
          have pair : (.inl answer, 4) = (suffix.1, (2 : Nat) * suffix.2) := by
            simpa using sequenced
          obtain ⟨answerEq, paidProd⟩ := Prod.ext_iff.mp pair
          have suffixPaid : suffix.2 = 2 := by
            have : (2 : Nat) * suffix.2 = 4 := paidProd.symm
            omega
          have headEq : suffix.1 = .inl answer := by
            simpa using answerEq.symm
          have suffixTrace : (retained suffix.1).trace = jointReturnTrace := by
            rw [headEq]
            simpa [retained] using returnedTrace
          have continued := contributions_continue jointSource earnedMember
            (by rw [hsuffix]; exact List.mem_cons_self)
          have traceSplit : jointReturnTrace =
              jointEarnedTrace ++ jointReturnTrace.drop jointEarnedTrace.length := by
            rfl
          have appended := trace_replay_append jointSpec jointAssignment jointStart
            jointEarnedTrace (jointReturnTrace.drop jointEarnedTrace.length)
          rw [← traceSplit, fullReplay, earnedReplay] at appended
          simp only [Option.bind_some] at appended
          cases hrest : traceReplay jointSpec jointAssignment (retained (.inr pending)).state
              (jointReturnTrace.drop jointEarnedTrace.length) with
          | none =>
              rw [hrest] at appended
              simp at appended
          | some later =>
              cases later with
              | mk _finalState suffixLedger =>
                  rw [hrest] at appended
                  simp only [Option.map_some] at appended
                  have ledgerEq : jointEarnedLedger ++ suffixLedger = jointProductionLedger :=
                    (Prod.ext_iff.mp (Option.some.inj appended)).2.symm
                  have stateEq : (retained (.inr pending)).state = pending.state := by
                    simp [retained]
                  have prefixed :
                      (traceReplayFrom jointSpec jointAssignment jointEarnedLedger pending.state
                          ((retained suffix.1).trace.drop jointEarnedTrace.length)).map Prod.snd =
                        some jointProductionLedger := by
                    rw [suffixTrace, ← stateEq]
                    simp [traceReplayFrom, hrest, ledgerEq]
                  exact ⟨pending, suffix,
                    by simpa [jointEarnedCut] using earnedCut, hsuffix, suffixPaid,
                    by simpa [jointRun] using continued, pendingTrace, suffixTrace, prefixed⟩

theorem joint_returned_residual_repeats_at_one :
    jointRun.all (fun leaf => leaf.1.isLeft) = true ∧
      contributions jointSource (15 + 1) jointInitial =
        jointRun.map (fun item => (item.1, item.2 * 1)) := by
  have returned : jointRun.all (fun leaf => leaf.1.isLeft) = true := by decide
  have sequenced := joint_source_cut_continues 15 1
  have preserved := continue_without_pending jointSource 1 jointRun returned
  have same : contributions jointSource (15 + 1) jointInitial = jointRun :=
    sequenced.trans preserved
  refine ⟨returned, ?_⟩
  rw [same]
  simp [mul_one]

def jointRights (cut : JointCut) : Rights :=
  cut.foldl (fun acc leaf =>
    match leaf.1 with
    | .inl _ => acc ∪ {Right.inspect}
    | .inr pending =>
        match pending.state.control with
        | .halted _ => acc ∪ {Right.inspect}
        | _ => acc ∪ {Right.force}) ∅

def jointUniformPaths (cut : JointCut) : Bool :=
  match cut with
  | [] => false
  | leaf :: rest =>
      rest.all fun other =>
        decide ((retained other.1).state.world.path = (retained leaf.1).state.world.path)

def jointUniformSpines (cut : JointCut) : Bool :=
  match cut with
  | [] => false
  | leaf :: rest =>
      rest.all fun other =>
        decide ((retained other.1).state.world.heap.spine =
          (retained leaf.1).state.world.heap.spine)

def jointAgrees (cut : JointCut) : Bool :=
  match cut with
  | [_] => true
  | _ => false

def jointOwnPath (cut : JointCut) : List Nat :=
  match cut with
  | leaf :: _ => (retained leaf.1).state.world.path
  | [] => []

def jointOwnSpine (cut : JointCut) :
    List (HeapUpdate JointOrigin (Val CellId) Unit) :=
  match cut with
  | leaf :: _ => (retained leaf.1).state.world.heap.spine
  | [] => []

def jointRequestHeld (held requested : Rights) : Bool :=
  (restrict? held requested).isSome

def admitJointAt (cut : JointCut) (path : List Nat)
    (spine : List (HeapUpdate JointOrigin (Val CellId) Unit))
    (held requested : Rights) : RetainedAdmit JointCut :=
  admitRetainedCut (decide (cut ≠ [])) (jointUniformPaths cut) (jointUniformSpines cut)
    (jointAgrees cut)
    (match cut with
      | [] => false
      | _ => cut.all fun leaf => decide ((retained leaf.1).state.world.path = path))
    (match cut with
      | [] => false
      | _ => cut.all fun leaf =>
          decide ((retained leaf.1).state.world.heap.spine = spine))
    (decide (jointRights cut ⊆ held)) (jointRequestHeld held requested) cut

def retainedTag {Account : Type} : RetainedAdmit Account → Nat
  | .accept _ => 0
  | .reject reason _ =>
      match reason with
      | .staleWorld => 1
      | .changedDependency => 2
      | .missingRights => 3
      | .incompleteResidual => 4
      | .incoherentResidual => 5
      | .splitWorlds => 6

theorem joint_admission_keeps_the_cut (cut : JointCut) (path : List Nat)
    (spine : List (HeapUpdate JointOrigin (Val CellId) Unit))
    (held requested : Rights) :
    (admitJointAt cut path spine held requested).kept = cut := by
  unfold admitJointAt jointRequestHeld
  exact admitRetainedCut_keeps (decide (cut ≠ [])) (jointUniformPaths cut)
    (jointUniformSpines cut) (jointAgrees cut)
    (match cut with
      | [] => false
      | _ => cut.all fun leaf => decide ((retained leaf.1).state.world.path = path))
    (match cut with
      | [] => false
      | _ => cut.all fun leaf => decide ((retained leaf.1).state.world.heap.spine = spine))
    (decide (jointRights cut ⊆ held)) ((restrict? held requested).isSome) cut

theorem joint_pending_cuts_require_force :
    retainedTag (admitJointAt jointForceCut (jointOwnPath jointForceCut)
        (jointOwnSpine jointForceCut) {Right.inspect} ∅) = 3 ∧
      retainedTag (admitJointAt jointEarnedCut (jointOwnPath jointEarnedCut)
        (jointOwnSpine jointEarnedCut) {Right.inspect} ∅) = 3 ∧
      retainedTag (admitJointAt jointForceCut (jointOwnPath jointForceCut)
        (jointOwnSpine jointForceCut) {Right.force} ∅) = 0 ∧
      retainedTag (admitJointAt jointEarnedCut (jointOwnPath jointEarnedCut)
        (jointOwnSpine jointEarnedCut) {Right.force, Right.inspect} ∅) = 0 ∧
      (admitJointAt jointForceCut (jointOwnPath jointForceCut)
        (jointOwnSpine jointForceCut) {Right.inspect} ∅).kept = jointForceCut ∧
      (admitJointAt jointEarnedCut (jointOwnPath jointEarnedCut)
        (jointOwnSpine jointEarnedCut) {Right.inspect} ∅).kept = jointEarnedCut ∧
      jointCutMark 3 = [(0, 1, [], jointForceTrace, false)] ∧
      jointCutMark 6 = [(0, 2, [0], jointEarnedTrace, false)] := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, joint_cut_marks.1,
    joint_cut_marks.2.1⟩
  · exact joint_admission_keeps_the_cut jointForceCut (jointOwnPath jointForceCut)
      (jointOwnSpine jointForceCut) {Right.inspect} ∅
  · exact joint_admission_keeps_the_cut jointEarnedCut (jointOwnPath jointEarnedCut)
      (jointOwnSpine jointEarnedCut) {Right.inspect} ∅

theorem joint_returned_inspect_keeps_both_payments :
    retainedTag (admitJointAt jointRun (jointOwnPath jointRun) (jointOwnSpine jointRun)
        {Right.inspect} ∅) = 0 ∧
      retainedTag (admitJointAt jointRun (jointOwnPath jointRun) (jointOwnSpine jointRun)
        {Right.inspect} {Right.inspect}) = 0 ∧
      retainedTag (admitJointAt jointRun (jointOwnPath jointRun) (jointOwnSpine jointRun)
        ∅ {Right.inspect}) = 3 ∧
      retainedTag (admitJointAt jointRun [9] (jointOwnSpine jointRun)
        {Right.inspect} {Right.inspect}) = 1 ∧
      (admitJointAt jointRun (jointOwnPath jointRun) (jointOwnSpine jointRun)
        ∅ {Right.inspect}).kept = jointRun ∧
      jointCutMark 15 = [(1, 4, [0, 0], jointReturnTrace, true)] := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, joint_cut_marks.2.2.2⟩
  exact joint_admission_keeps_the_cut jointRun (jointOwnPath jointRun)
    (jointOwnSpine jointRun) ∅ {Right.inspect}

theorem joint_live_roots_keep_both_cells :
    occurrencesOf jointValue = [jointLeftCell, jointRightCell] ∧
      jointValue.referenceSet = {jointLeftCell, jointRightCell} ∧
      unread (consumersOf jointValue).log 0 = [jointLeftCell, jointRightCell] ∧
      unread (consumersOf jointValue).log 1 = [jointLeftCell, jointRightCell] ∧
      unread (cancelConsumer (consumersOf jointValue) 0).log 0 = [] ∧
      unread (cancelConsumer (consumersOf jointValue) 0).log 1 =
        [jointLeftCell, jointRightCell] ∧
      jointLeftCell ≠ jointRightCell := by
  decide

def eraseJointCurrent (occurrence : JointOccurrence) : JointOccurrence :=
  { occurrence with
      state := { occurrence.state with
        world := { occurrence.state.world with
          heap := { occurrence.state.world.heap with current := fun _ => none } } } }

def jointErasedRun : JointCut :=
  jointRun.map fun leaf => (Sum.map eraseJointCurrent eraseJointCurrent leaf.1, leaf.2)

theorem joint_erased_current_keeps_the_spine :
    jointOwnPath jointErasedRun = jointOwnPath jointRun ∧
      jointOwnSpine jointErasedRun = jointOwnSpine jointRun ∧
      retainedTag (admitJointAt jointErasedRun (jointOwnPath jointRun)
        (jointOwnSpine jointRun) {Right.inspect} {Right.inspect}) = 0 := by
  decide

theorem joint_erased_current_is_not_recorded :
    ∃ leaf, jointRun = [leaf] ∧
      ¬ (eraseJointCurrent (retained leaf.1)).state.world.heap.Recorded := by
  obtain ⟨leaf, runEq, _, _, _, _, _, _, leftLookup, _,
      ⟨_, _, _, _, _, recorded⟩⟩ := joint_returned_source_account
  refine ⟨leaf, runEq, ?_⟩
  intro erased
  have spineEq : (eraseJointCurrent (retained leaf.1)).state.world.heap.spine =
      (retained leaf.1).state.world.heap.spine := rfl
  have noneLookup :
      (eraseJointCurrent (retained leaf.1)).state.world.heap.lookup jointLeftCell = none := by
    unfold eraseJointCurrent lookup
    rfl
  have realSpine := recorded jointLeftCell
  rw [leftLookup] at realSpine
  have erasedSpine := erased jointLeftCell
  rw [noneLookup, spineEq, ← realSpine] at erasedSpine
  cases erasedSpine

def jointClaimOwner (owner : Nat) (identity : CellId × ReceiptId) : Option Nat :=
  if identity = jointLeftFactor.identity then some owner else none

def jointOwnerClaim (owner : Nat) :
    Scoped (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat Nat :=
  ⟨jointProductionLedger, jointClaimOwner owner⟩

theorem joint_owner_claim_is_supported (owner : Nat) : (jointOwnerClaim owner).Supported := by
  intro identity claimedOwner claimed
  have claimedFun : jointClaimOwner owner identity = some claimedOwner := by
    simpa [jointOwnerClaim] using claimed
  unfold jointClaimOwner at claimedFun
  split at claimedFun
  · next same =>
      cases claimedFun
      rw [same]
      simp only [jointOwnerClaim, identities, jointProductionLedger, List.map_cons, List.map_nil]
      exact List.mem_cons_self
  · next _ =>
      cases claimedFun

theorem joint_rival_owners_are_refused :
    Scoped.merge? (jointOwnerClaim 0) (jointOwnerClaim 1) = none :=
  Scoped.conflicting_claims_refused (jointOwnerClaim 0) (jointOwnerClaim 1)
    (joint_owner_claim_is_supported 1)
    (by decide : (jointOwnerClaim 0).claims jointLeftFactor.identity = some 0)
    (by decide : (jointOwnerClaim 1).claims jointLeftFactor.identity = some 1)
    (by decide : (0 : Nat) ≠ 1)

/-- The earned prefix merges to the source ledger. The opposite factor order
is a successful algebraic sidecar, and it is not that ledger. Equal Nat
denotations are not an execution interchange. The branch words are the order
that fails to commute. -/
theorem joint_source_order_is_not_the_reversed_sidecar :
    Mettapedia.Algebra.SharedCoefficientLedger.merge?
        jointEarnedLedger jointProductionLedger = some jointProductionLedger ∧
      Mettapedia.Algebra.SharedCoefficientLedger.merge?
          [jointRightFactor] [jointLeftFactor] = some jointReversedLedger ∧
      jointReversedLedger ≠ jointProductionLedger ∧
      denote jointReversedLedger = denote jointProductionLedger ∧
      (⟨[0]⟩ : Coeff) * ⟨[0, 0]⟩ = ⟨[0, 0]⟩ * ⟨[0]⟩ ∧
      (⟨[0, 1]⟩ : Coeff) * ⟨[1]⟩ ≠ ⟨[1]⟩ * ⟨[0, 1]⟩ := by
  exact ⟨by decide, by decide, by decide, by decide,
    nested_fork_words_commute_and_branch_words_do_not.1,
    nested_fork_words_commute_and_branch_words_do_not.2⟩

theorem joint_cell_lookups_commute_without_commuting_the_spines
    (heap : Heap JointOrigin (Val CellId) Unit)
    (leftRecord rightRecord : JointRecord JointOrigin (Val CellId) Unit)
    (leftState rightState : JointCacheState (Val CellId) Unit) :
    observeCellPair jointLeftCell jointRightCell
        (run applyCellWrite heap
          [.set jointRightCell rightRecord rightState,
            .set jointLeftCell leftRecord leftState]) =
      observeCellPair jointLeftCell jointRightCell
        (run applyCellWrite heap
          [.set jointLeftCell leftRecord leftState,
            .set jointRightCell rightRecord rightState]) ∧
      ¬ CrossCommutes applyCellWrite
          [.set jointLeftCell leftRecord leftState]
          [.set jointRightCell rightRecord rightState] := by
  exact ⟨swapped_distinct_writes_keep_both_lookups (by decide : jointLeftCell ≠ jointRightCell)
      leftRecord rightRecord leftState rightState heap,
    distinct_cell_writes_do_not_commute_as_heaps heap
      (by decide : jointLeftCell ≠ jointRightCell)
      leftRecord rightRecord leftState rightState⟩

theorem joint_execution_is_not_the_payload_split :
    jointLeftCell ≠ sharedCell ∧
      jointRightCell ≠ sharedCell ∧
      jointLeftCell ≠ jointRightCell ∧
      leftAccount.occurrence.state.world.path = [0] ∧
      rightAccount.occurrence.state.world.path = [1] ∧
      leftAccount.occurrence.state.world.path ≠ rightAccount.occurrence.state.world.path ∧
      (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).joined = none ∧
      (disposeAdmitted leftAccount leftAccount leftClaim leftClaim).joined =
        some leftReceiptLedger := by
  exact ⟨by decide, by decide, by decide,
    payload_branches_do_not_join.2.1, payload_branches_do_not_join.2.2.1,
    payload_branches_do_not_join.2.2.2,
    split_paths_refuse_the_join leftAccount rightAccount leftClaim rightClaim
      payload_branches_do_not_join.2.2.2,
    copied_ledger_is_not_an_independent_and.1⟩

/-! ### Source-issued admission

`issueSelf` copies the submitted payment, trace, and control. A forged
leaf can satisfy that copier by itself. `replayAccount` is only an
external finite-source check: `traceReplay` calls `step` and reruns the
source callbacks, so it is not an issuer for effectful work that has
already been retained.

`issueEarned` is the passive issuer. It reads the existing `History`
identity — successor indices, `historyEventPath`, and `productionLedger`
— and the history's endpoint. It does not call `step` or `traceReplay`.
The earned debit is `denote` of that production ledger. The transition
clock is the existing path length (`transitions_eq_pathLength`); it is
not added into the debit. `issueLeaf` consumes a leaf that is already in
hand and likewise does not replay. `issueBudget` only selects the
reachable singleton of one budget, then uses that passive reading.

`admitViews` compares the path, census, ledger, and roots. It does not
read the control or the allocator and evaluator counters, so a replaced
continuation still passes there. `admitComparable` then compares the
finite residual on the same certificate: control, halted flag, work,
receipt graph, `nextCell`, `nextEvaluator`, and the derived debit. That
comparison does not call `step` or `traceReplay`.

Admission reuses `Refusal` and `RetainedAdmit`. These failures all keep
the submitted account, and the existing constructors already separate
the decisions made below, so no new refusal reason is added.

An evaluate owner and a live-root consumer are different roles. This
execution uses the numbers `0` and `1` for both. Native issuance of
retained work is this history identity, not a second execution and not
`replayAccount`. `releaseIssued` does not release native memory.

`consumeAuthenticated` receives a `History` from `jointStart`, builds the
certificate with `issueEarned`, and admits the presented account.
Refusal returns that account and does not call `contributions`.
Acceptance resumes through `weightedResume`, the existing
`contributions_add` continuation. `pathMachine` and `historyEventPath`
stay `Type`. The occurrence trace is `indices` because this history
starts from the empty trace. Payload uses the same `weightedResume`;
one payload leaf is not the whole frontier.
-/

abbrev JointLedger :=
  Ledger (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat

abbrev JointReceiptNode :=
  ReceiptNode JointOrigin JointRule (Val CellId) Unit Unit Unit

abbrev JointHeap :=
  Mettapedia.Machines.BranchLocalNeed.NeedReference.Heap JointOrigin (Val CellId) Unit

abbrev JointCellRecord := JointRecord JointOrigin (Val CellId) Unit

abbrev JointControl :=
  Mettapedia.Machines.BranchLocalNeed.NeedReference.Control
    JointLocal JointResume (Val CellId) Unit Unit

abbrev JointReceipts :=
  ReceiptGraph JointOrigin JointRule (Val CellId) Unit Unit Unit

abbrev JointScoped :=
  Scoped (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat Nat

abbrev JointIssuedRow :=
  Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Row CellId Nat

abbrev JointIssuedHandle :=
  Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Handle CellId Nat

abbrev JointIssuedRegistry :=
  Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Registry CellId Nat

abbrev lookupJoint :=
  Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.lookup
    (Address := CellId) (Provider := Nat)

abbrev releaseJoint :=
  Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.releaseIssued
    (Address := CellId) (Provider := Nat)

def censusCells : List (HeapUpdate JointOrigin (Val CellId) Unit) → List CellId
  | [] => []
  | .allocate cell _ :: olderUpdates =>
      let older := censusCells olderUpdates
      if decide (cell ∈ older) then older else older ++ [cell]
  | .cache _ _ :: olderUpdates => censusCells olderUpdates

def censusAgrees (heap : JointHeap) : Bool :=
  (censusCells heap.spine).all fun cell =>
    decide (heap.lookup cell = lookupSpine heap.spine cell)

structure GraphAccount where
  owners : List (CellId × Nat)
  pending : List (CellId × Nat)
  factors : JointLedger

def ownerOf : List (CellId × Nat) → CellId → Option Nat
  | [], _ => none
  | (cell, owner) :: rest, wanted =>
      if decide (cell = wanted) then some owner else ownerOf rest wanted

/-- An observe closes a production only after this graph has recorded the
matching evaluate. A later observe of an already closed cell is a delivery
and adds no factor. The coefficient is the source assignment. -/
def readReceipt (account : GraphAccount) (node : JointReceiptNode) : GraphAccount :=
  match node.payload with
  | .evaluate cell owner =>
      { owners := (cell, owner) ::
          account.owners.filter fun pair => decide (pair.1 ≠ cell)
        pending := (cell, owner) ::
          account.pending.filter fun pair => decide (pair.1 ≠ cell)
        factors := account.factors }
  | .observe cell outcome =>
      if account.pending.any fun pair => decide (pair.1 = cell) then
        { account with
            pending := account.pending.filter fun pair => decide (pair.1 ≠ cell)
            factors := account.factors ++
              [⟨(cell, node.id), outcome,
                jointAssignment ⟨CompletedReceiptKind.production, cell, node.id, outcome⟩⟩] }
      else
        account
  | _ => account

def readGraph (nodes : List JointReceiptNode) : GraphAccount :=
  nodes.reverse.foldl readReceipt (⟨[], [], []⟩ : GraphAccount)

def issueRow (owners : List (CellId × Nat))
    (factor : Factor (CellId × ReceiptId) (Produced (Val CellId) Unit Unit) Nat) :
    Option JointIssuedRow :=
  let token := factor.identity.2.serial
  if decide (token = 0) then
    none
  else
    match ownerOf owners factor.identity.1 with
    | none => none
    | some provider => some ⟨token, token, factor.identity.1, provider⟩

def issueRows (owners : List (CellId × Nat)) : JointLedger → Option (List JointIssuedRow)
  | [] => some []
  | factor :: rest =>
      match issueRow owners factor with
      | none => none
      | some row =>
          match issueRows owners rest with
          | none => none
          | some rows => some (row :: rows)

def claimOf (ledger : JointLedger) (owners : List (CellId × Nat)) : JointScoped :=
  ⟨ledger, fun identity =>
    if ledger.any fun factor => decide (factor.identity = identity) then
      ownerOf owners identity.1
    else
      none⟩

def outcomeRoots : Produced (Val CellId) Unit Unit → List CellId
  | .value value => occurrencesOf value
  | _ => []

def rootedCells (machine : JointMachine) : List CellId :=
  match machine.control with
  | .halted outcome => outcomeRoots outcome
  | .returned outcome _ => outcomeRoots outcome
  | _ => []

/-- A halted leaf is inspected. Every earlier control, including a returned
frame that has not halted, still requires force. -/
def requiredRights (machine : JointMachine) : Rights :=
  match machine.control with
  | .halted _ => {Right.inspect}
  | _ => {Right.force}

structure SourceCertificate where
  producer : Nat
  path : List Nat
  trace : List Nat
  payment : Nat
  halted : Bool
  ledger : JointLedger
  roots : List CellId
  spine : List (HeapUpdate JointOrigin (Val CellId) Unit)
  present : List (CellId × Option JointCellRecord)
  absent : CellId
  rights : Rights
  control : JointControl
  work : Work
  receipts : JointReceipts
  nextCell : Nat
  nextEvaluator : Nat
  registry : JointIssuedRegistry
  handles : List JointIssuedHandle
  claim : JointScoped

/-- The copier. Payment, trace, and control come from the leaf that was
handed in. This is the boundary a forged leaf can satisfy alone. -/
def issueSelf (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat) : Option SourceCertificate :=
  let occurrence := retained leaf.1
  let machine := occurrence.state
  let heap := machine.world.heap
  let absent := machine.world.freshCell 0
  let cells := censusCells heap.spine
  let read := readGraph machine.world.receipts.nodes
  if decide (machine.world.lineage = 0) then
    none
  else if !censusAgrees heap then
    none
  else if decide (absent ∈ cells) then
    none
  else if !decide (heap.lookup absent = none) then
    none
  else
    match issueRows read.owners read.factors with
    | none => none
    | some rows =>
        some {
          producer := machine.world.lineage
          path := machine.world.path
          trace := occurrence.trace
          payment := leaf.2
          halted := isHalted machine
          ledger := read.factors
          roots := rootedCells machine
          spine := heap.spine
          present := cells.map fun cell => (cell, heap.lookup cell)
          absent := absent
          rights := requiredRights machine
          control := machine.control
          work := machine.work
          receipts := machine.world.receipts
          nextCell := machine.world.nextCell
          nextEvaluator := machine.world.nextEvaluator
          registry := (⟨machine.world.lineage, rows⟩ : JointIssuedRegistry)
          handles := rows.map fun row =>
            (⟨machine.world.lineage, row.provider, row⟩ : JointIssuedHandle)
          claim := claimOf read.factors read.owners }

/-- External finite-source verification. This calls `traceReplay`, and
therefore `step`. It is not the issuer. -/
abbrev replayAccount (trace : List Nat) : Option (JointMachine × JointLedger) :=
  traceReplay jointSpec jointAssignment jointStart trace

/-- Successor indices of a retained history. Reading them does not step. -/
abbrev earnedTrace {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target) : List Nat :=
  indices (pathMachine jointSpec jointStart) history

/-- Production ledger of a retained history. Reading it does not step. -/
abbrev earnedLedger {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target) : JointLedger :=
  productionLedger jointSpec jointAssignment
    (historyEventPath jointSpec jointStart history)

abbrev certificateOf (machine : JointMachine) (trace : List Nat)
    (ledger : JointLedger) (rows : List JointIssuedRow) : SourceCertificate :=
  let heap := machine.world.heap
  let cells := censusCells heap.spine
  let read := readGraph machine.world.receipts.nodes
  { producer := machine.world.lineage
    path := machine.world.path
    trace := trace
    payment := denote ledger
    halted := isHalted machine
    ledger := ledger
    roots := rootedCells machine
    spine := heap.spine
    present := cells.map fun cell => (cell, heap.lookup cell)
    absent := machine.world.freshCell 0
    rights := requiredRights machine
    control := machine.control
    work := machine.work
    receipts := machine.world.receipts
    nextCell := machine.world.nextCell
    nextEvaluator := machine.world.nextEvaluator
    registry := (⟨machine.world.lineage, rows⟩ : JointIssuedRegistry)
    handles := rows.map fun row =>
      (⟨machine.world.lineage, row.provider, row⟩ : JointIssuedHandle)
    claim := claimOf ledger read.owners }

/-- Census, absence, and receipt-graph checks on an endpoint already in
hand. The ledger is an argument; this does not recompute it by stepping. -/
def retainedRows (machine : JointMachine) (ledger : JointLedger) :
    Option (List JointIssuedRow) :=
  let heap := machine.world.heap
  let absent := machine.world.freshCell 0
  let cells := censusCells heap.spine
  let read := readGraph machine.world.receipts.nodes
  if decide (machine.world.lineage = 0) then
    none
  else if !censusAgrees heap then
    none
  else if decide (absent ∈ cells) then
    none
  else if !decide (heap.lookup absent = none) then
    none
  else if decide (read.factors ≠ ledger) then
    none
  else
    issueRows read.owners ledger

/-- Passive reading of a leaf already in hand. The debit is `denote` of
the receipt graph stored on that leaf. A copied payment that disagrees is
`none`. This does not call `step` or `traceReplay`, and a substituted
trace or control is not repaired here. -/
def issueLeaf (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat) : Option SourceCertificate :=
  if decide (leaf.2 ≠ denote
      ((readGraph (retained leaf.1).state.world.receipts.nodes).factors)) then
    none
  else
    match retainedRows (retained leaf.1).state
        ((readGraph (retained leaf.1).state.world.receipts.nodes).factors) with
    | none => none
    | some rows =>
        some (certificateOf (retained leaf.1).state (retained leaf.1).trace
          ((readGraph (retained leaf.1).state.world.receipts.nodes).factors) rows)

/-- Passive issuer for a history that was already earned. The trace is
`indices`, the debit is `denote` of `productionLedger`, and the residual
is the history's endpoint. Nothing here calls `step` or `traceReplay`. -/
def issueEarned {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target) :
    Option SourceCertificate :=
  match retainedRows target (earnedLedger history) with
  | none => none
  | some rows =>
      some (certificateOf target (earnedTrace history) (earnedLedger history) rows)

/-- The budget selects the reachable singleton. Issuing that leaf does not
replay it. -/
def issueBudget (budget : Nat) : Option SourceCertificate :=
  match contributions jointSource budget jointInitial with
  | [leaf] => issueLeaf leaf
  | _ => none

def issueSelfCut (cut : JointCut) : Option SourceCertificate :=
  match cut with
  | [leaf] => issueSelf leaf
  | _ => none

def issueCut (cut : JointCut) : Option SourceCertificate :=
  match cut with
  | [leaf] => issueLeaf leaf
  | _ => none

structure PresentedAccount where
  cut : JointCut
  ledger : JointLedger
  roots : List CellId
  held : Rights
  requested : Rights
  rival : Option JointScoped

/-- Path, census, ledger, and roots. The control, halted flag, work,
receipt graph, and allocator and evaluator counters are not inputs. A
replaced continuation can pass here. -/
def admitViews (issued : SourceCertificate) (presented : PresentedAccount) :
    RetainedAdmit PresentedAccount :=
  match presented.cut with
  | [] => .reject .incompleteResidual presented
  | leaf :: more =>
      match more with
      | _ :: _ => .reject .splitWorlds presented
      | [] =>
          let occurrence := retained leaf.1
          let machine := occurrence.state
          let heap := machine.world.heap
          let read := readGraph machine.world.receipts.nodes
          let present := (censusCells heap.spine).map fun cell => (cell, heap.lookup cell)
          if decide (machine.world.lineage = 0) ||
              decide (machine.world.lineage ≠ issued.producer) then
            .reject .staleWorld presented
          else if decide (occurrence.trace ≠ issued.trace) ||
              decide (leaf.2 ≠ issued.payment) ||
              decide (presented.ledger ≠ issued.ledger) ||
              decide (read.factors ≠ issued.ledger) then
            .reject .incoherentResidual presented
          else if decide (presented.roots ≠ issued.roots) ||
              decide (rootedCells machine ≠ issued.roots) then
            .reject .incompleteResidual presented
          else if decide (machine.world.path ≠ issued.path) then
            .reject .staleWorld presented
          else if decide (heap.spine ≠ issued.spine) ||
              decide (present ≠ issued.present) ||
              !decide (heap.lookup issued.absent = none) then
            .reject .changedDependency presented
          else if !decide (issued.rights ⊆ presented.held) ||
              (restrict? presented.held presented.requested).isNone then
            .reject .missingRights presented
          else
            .accept presented

/-- Finite residual of one retained leaf: continuation, halted flag, paid
work, receipt graph, allocator and evaluator counters, and the debit
derived from the issued ledger. -/
def residualAgrees (issued : SourceCertificate) (presented : PresentedAccount) : Bool :=
  match presented.cut with
  | [leaf] =>
      let machine := (retained leaf.1).state
      decide (machine.control = issued.control) &&
        decide (isHalted machine = issued.halted) &&
        decide (machine.work = issued.work) &&
        decide (machine.world.receipts = issued.receipts) &&
        decide (machine.world.nextCell = issued.nextCell) &&
        decide (machine.world.nextEvaluator = issued.nextEvaluator) &&
        decide (issued.payment = denote issued.ledger) &&
        decide (leaf.2 = denote issued.ledger)
  | _ => false

def admitComparable (issued : SourceCertificate) (presented : PresentedAccount) :
    RetainedAdmit PresentedAccount :=
  match admitViews issued presented with
  | .reject reason kept => .reject reason kept
  | .accept account =>
      if residualAgrees issued presented then
        .accept account
      else
        .reject .incoherentResidual presented

def admitIssued (issued : SourceCertificate) (presented : PresentedAccount) :
    RetainedAdmit PresentedAccount :=
  match presented.rival with
  | some rival =>
      match Scoped.merge? issued.claim rival with
      | none => .reject .incoherentResidual presented
      | some _ => admitComparable issued presented
  | none => admitComparable issued presented

/-- `admitViews` acceptance checks the submitted held set. Issued rights must
already be held, and the request must attenuate. The other view comparisons
are not re-proved here. -/
theorem admissionChecksHeld (issued : SourceCertificate) (presented accepted : PresentedAccount)
    (admitted : admitViews issued presented = .accept accepted) :
    issued.rights ⊆ presented.held ∧ presented.requested ⊆ presented.held := by
  unfold admitViews at admitted
  split at admitted
  · cases admitted
  · split at admitted
    · cases admitted
    · dsimp only at admitted
      repeat' first | split at admitted | cases admitted
      all_goals simp_all [restrict?]

theorem comparableChecksHeld (issued : SourceCertificate) (presented accepted : PresentedAccount)
    (admitted : admitComparable issued presented = .accept accepted) :
    issued.rights ⊆ presented.held ∧ presented.requested ⊆ presented.held := by
  unfold admitComparable at admitted
  split at admitted
  · cases admitted
  · rename_i checked hchecked
    split at admitted
    · exact admissionChecksHeld issued presented checked hchecked
    · cases admitted

theorem issuedChecksHeld (issued : SourceCertificate) (presented accepted : PresentedAccount)
    (admitted : admitIssued issued presented = .accept accepted) :
    issued.rights ⊆ presented.held ∧ presented.requested ⊆ presented.held := by
  unfold admitIssued at admitted
  split at admitted
  · split at admitted
    · cases admitted
    · exact comparableChecksHeld issued presented accepted admitted
  · exact comparableChecksHeld issued presented accepted admitted

/-- Cut, ledger, and roots agree with an accepted account, but the submitted
held set does not grant the issued rights or the request. Held may differ
from the accepted account. -/
private theorem admitViews_missing_submitted_held
    (issued : SourceCertificate) (account presented : PresentedAccount)
    (cutEq : presented.cut = account.cut)
    (ledgerEq : presented.ledger = account.ledger)
    (rootsEq : presented.roots = account.roots)
    (accepted : admitViews issued account = .accept account)
    (missing :
      (!decide (issued.rights ⊆ presented.held) ||
          (restrict? presented.held presented.requested).isNone) = true) :
    admitViews issued presented = .reject .missingRights presented := by
  rcases account with ⟨cut, ledger, roots, held, requested, oldRival⟩
  rcases presented with ⟨presentedCut, presentedLedger, presentedRoots,
    presentedHeld, presentedRequest, presentedRival⟩
  simp only at cutEq ledgerEq rootsEq
  subst presentedCut
  subst presentedLedger
  subst presentedRoots
  unfold admitViews at accepted ⊢
  dsimp only at accepted ⊢
  rw [missing]
  repeat' first
    | (solve | cases accepted)
    | split at accepted
  all_goals simp_all
  all_goals aesop

def admitTag (issued : SourceCertificate) (cut : JointCut) (ledger : JointLedger)
    (roots : List CellId) (held requested : Rights) (rival : Option JointScoped) : Nat :=
  retainedTag (admitIssued issued ⟨cut, ledger, roots, held, requested, rival⟩)

def admitViewTag (issued : SourceCertificate) (cut : JointCut) (ledger : JointLedger)
    (roots : List CellId) (held requested : Rights) (rival : Option JointScoped) : Nat :=
  retainedTag (admitViews issued ⟨cut, ledger, roots, held, requested, rival⟩)

def keptLedger (issued : SourceCertificate) (cut : JointCut) (ledger : JointLedger)
    (roots : List CellId) (held requested : Rights) (rival : Option JointScoped) :
    JointLedger :=
  (admitIssued issued ⟨cut, ledger, roots, held, requested, rival⟩).kept.ledger

def mapOccurrence (f : JointOccurrence → JointOccurrence) (cut : JointCut) : JointCut :=
  cut.map fun leaf => (Sum.map f f leaf.1, leaf.2)

def mapPayment (payment : Nat) (cut : JointCut) : JointCut :=
  cut.map fun leaf => (leaf.1, payment)

def withLineage (lineage : Nat) (occurrence : JointOccurrence) : JointOccurrence :=
  { occurrence with
      state := { occurrence.state with
        world := { occurrence.state.world with lineage := lineage } } }

def withPath (path : List Nat) (occurrence : JointOccurrence) : JointOccurrence :=
  { occurrence with
      state := { occurrence.state with
        world := { occurrence.state.world with path := path } } }

def withTrace (trace : List Nat) (occurrence : JointOccurrence) : JointOccurrence :=
  { occurrence with trace := trace }

def withControl (control : JointControl) (occurrence : JointOccurrence) : JointOccurrence :=
  { occurrence with
      state := { occurrence.state with control := control } }

def withWork (work : Work) (occurrence : JointOccurrence) : JointOccurrence :=
  { occurrence with
      state := { occurrence.state with work := work } }

/-- Replace the allocator and evaluator counters. The heap, control, and
receipt graph stay the occurrence's own. -/
def withCounters (nextCell nextEvaluator : Nat) (occurrence : JointOccurrence) :
    JointOccurrence :=
  { occurrence with
      state := { occurrence.state with
        world := { occurrence.state.world with
          nextCell := nextCell
          nextEvaluator := nextEvaluator } } }

/-- A second observe of a cell the graph has already closed. The production
ledger does not gain a factor. The receipt graph does gain a node. -/
def repeatObservation (occurrence : JointOccurrence) : JointOccurrence :=
  let machine := occurrence.state
  let appended := machine.world.receipts.append machine.world.path
    (.observe jointLeftCell (.value (.sym 3)))
  { occurrence with
      state := { machine with
        world := { machine.world with receipts := appended.1 } } }

def spoofedSuspension : JointCut :=
  mapOccurrence (withControl (.run .start [])) jointForceCut

def spoofedOwner : JointCut :=
  mapOccurrence
    (withControl (.returned (.value jointValue) [.commit jointLeftCell 9])) jointRun

def repeatedObservation : JointCut :=
  mapOccurrence repeatObservation jointRun

def bumpedWork : JointCut :=
  mapOccurrence (fun occurrence =>
    withWork (occurrence.state.work.bump 9 0 0 0) occurrence) jointRun

def substitutedCounters : JointCut :=
  mapOccurrence (withCounters 9 9) jointRun

def plantEvaluating (occurrence : JointOccurrence) : JointOccurrence :=
  { occurrence with
      state := { occurrence.state with
        world := { occurrence.state.world with
          heap := { occurrence.state.world.heap with
            current := Function.update occurrence.state.world.heap.current
              jointLeftCell (some (jointEvaluating 3 9)) } } } }

def evaluatingOwner : JointCut := mapOccurrence plantEvaluating jointEarnedCut

def withSpine (spine : List (HeapUpdate JointOrigin (Val CellId) Unit))
    (occurrence : JointOccurrence) : JointOccurrence :=
  { occurrence with
      state := { occurrence.state with
        world := { occurrence.state.world with
          heap := { occurrence.state.world.heap with spine := spine } } } }

def plantCurrent (cell : CellId) (occurrence : JointOccurrence) : JointOccurrence :=
  { occurrence with
      state := { occurrence.state with
        world := { occurrence.state.world with
          heap := { occurrence.state.world.heap with
            current := Function.update occurrence.state.world.heap.current cell
              (some (jointSuspended 9)) } } } }

def orWorlds : JointCut := jointRun ++ mapOccurrence (withPath [1]) jointRun

def handleKey (handle : JointIssuedHandle) :
    Nat × Nat × Nat × Nat × CellId × Nat :=
  (handle.store, handle.parent, handle.row.occurrence, handle.row.token,
    handle.row.payload, handle.row.provider)

def cutView (cert : SourceCertificate) :
    Nat × List Nat × List Nat × Nat × Bool × JointLedger × List CellId × Nat :=
  (cert.producer, cert.path, cert.trace, cert.payment, cert.halted, cert.ledger,
    cert.roots, cert.handles.length)

theorem source_issue_reads_the_three_cuts :
    (issueCut jointForceCut).map cutView =
        some (2, [], jointForceTrace, 1, false, [], [], 0) ∧
      (issueCut jointEarnedCut).map cutView =
        some (2, [0], jointEarnedTrace, 2, false, jointEarnedLedger, [], 1) ∧
      (issueCut jointRun).map cutView =
        some (2, [0, 0], jointReturnTrace, 4, true, jointProductionLedger,
          [jointLeftCell, jointRightCell], 2) ∧
      (issueCut jointForceCut).map SourceCertificate.rights = some {Right.force} ∧
      (issueCut jointEarnedCut).map SourceCertificate.rights = some {Right.force} ∧
      (issueCut jointRun).map SourceCertificate.rights = some {Right.inspect} ∧
      (issueCut jointRun).map (fun cert =>
          cert.present.map fun item => (item.1, item.2.isSome)) =
        some [(jointLeftCell, true), (jointRightCell, true)] ∧
      (issueCut jointRun).map (fun cert =>
          cert.present.all fun item =>
            decide (item.2 = lookupSpine cert.spine item.1)) = some true ∧
      (issueCut jointRun).map (fun cert =>
          decide (cert.present.all fun item => decide (item.1 ≠ cert.absent))) =
        some true ∧
      (issueCut jointRun).map (fun cert => cert.claim.claims jointLeftFactor.identity) =
        some (some 0) ∧
      (issueCut jointRun).map (fun cert => cert.claim.claims jointRightFactor.identity) =
        some (some 1) ∧
      (issueCut jointEarnedCut).map (fun cert =>
          cert.claim.claims jointLeftFactor.identity) = some (some 0) ∧
      (issueCut jointForceCut).map (fun cert =>
          cert.claim.claims jointLeftFactor.identity) = some none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem source_issue_names_the_production_handles :
    (issueCut jointForceCut).map (fun cert => cert.handles.map handleKey) = some [] ∧
      (issueCut jointEarnedCut).map (fun cert => cert.handles.map handleKey) =
        some [(2, 0, 4, 4, jointLeftCell, 0)] ∧
      (issueCut jointRun).map (fun cert => cert.handles.map handleKey) =
        some [(2, 0, 4, 4, jointLeftCell, 0), (2, 1, 7, 7, jointRightCell, 1)] ∧
      (issueCut jointRun).map SourceCertificate.registry =
        (issueCut jointRun).map fun cert =>
          (⟨cert.producer, cert.handles.map fun handle => handle.row⟩ : JointIssuedRegistry) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem source_admission_requires_force_until_return :
    (issueCut jointForceCut).bind (fun pending =>
        some (admitTag pending jointForceCut pending.ledger pending.roots
            {Right.inspect} ∅ none,
          admitTag pending jointForceCut pending.ledger pending.roots
            {Right.force} ∅ none)) = some (3, 0) ∧
      (issueCut jointEarnedCut).bind (fun earned =>
        some (admitTag earned jointEarnedCut earned.ledger earned.roots
            {Right.inspect} ∅ none,
          admitTag earned jointEarnedCut earned.ledger earned.roots
            {Right.force} ∅ none)) = some (3, 0) ∧
      (issueCut jointRun).bind (fun returned =>
        some (admitTag returned jointRun returned.ledger returned.roots
            {Right.inspect} ∅ none,
          admitTag returned jointRun returned.ledger returned.roots
            {Right.inspect} {Right.inspect} none,
          admitTag returned jointRun returned.ledger returned.roots
            ∅ {Right.inspect} none,
          admitTag returned jointRun returned.ledger returned.roots
            {Right.inspect} {Right.force} none)) = some (0, 0, 3, 3) ∧
      (issueCut jointForceCut).bind (fun pending =>
        some ((admitIssued pending ⟨jointForceCut, pending.ledger, pending.roots,
          {Right.inspect} , ∅, none⟩).kept.cut)) = some jointForceCut ∧
      (issueCut jointRun).bind (fun returned =>
        some ((admitIssued returned ⟨jointRun, returned.ledger, returned.roots,
          ∅, {Right.inspect}, none⟩).kept.ledger)) = some jointProductionLedger := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `admitIssued` reads the retained leaf. Repeating it does not extend the
trace or replace the payment. The incoming product is the returned payment
`4`, so a suffix-only payment `2` and a restarted payment `1` are refused. -/
theorem source_admission_repeats_returned_inspection :
    (issueCut jointRun).bind (fun returned =>
        some (admitTag returned jointRun returned.ledger returned.roots
            {Right.inspect} ∅ none,
          admitTag returned jointRun returned.ledger returned.roots
            {Right.inspect} ∅ none,
          returned.payment, returned.trace)) =
      some (0, 0, 4, jointReturnTrace) ∧
      (issueCut jointRun).bind (fun returned =>
        some (keptLedger returned jointRun returned.ledger returned.roots
          {Right.inspect} {Right.inspect} none)) = some jointProductionLedger := by
  exact ⟨rfl, rfl⟩

theorem source_admission_keeps_the_incoming_payment :
    (issueCut jointEarnedCut).bind (fun earned =>
        some (earned.payment,
          admitTag earned (mapPayment 1 jointEarnedCut) earned.ledger earned.roots
            {Right.force} ∅ none,
          keptLedger earned (mapPayment 1 jointEarnedCut) earned.ledger earned.roots
            {Right.force} ∅ none)) = some (2, 5, jointEarnedLedger) ∧
      (issueCut jointRun).bind (fun returned =>
        some (returned.payment,
          admitTag returned (mapPayment 2 jointRun) returned.ledger returned.roots
            {Right.inspect} ∅ none,
          keptLedger returned (mapPayment 2 jointRun) returned.ledger returned.roots
            {Right.inspect} ∅ none,
          denote returned.ledger)) = some (4, 5, jointProductionLedger, 4) ∧
      (2 : Nat) * 2 = 4 := by
  exact ⟨rfl, rfl, rfl⟩

theorem erased_current_fails_source_admission :
    retainedTag (admitJointAt jointErasedRun (jointOwnPath jointRun)
        (jointOwnSpine jointRun) {Right.inspect} {Right.inspect}) = 0 ∧
      issueCut jointErasedRun = none ∧
      (issueCut jointRun).bind (fun issued =>
        some (admitTag issued jointErasedRun issued.ledger issued.roots
          {Right.inspect} {Right.inspect} none)) = some 2 ∧
      (issueCut jointRun).bind (fun issued =>
        some (keptLedger issued jointErasedRun issued.ledger issued.roots
          {Right.inspect} {Right.inspect} none,
          (admitIssued issued ⟨jointErasedRun, issued.ledger, issued.roots,
            {Right.inspect}, {Right.inspect}, none⟩).kept.cut)) =
        some (jointProductionLedger, jointErasedRun) := by
  exact ⟨joint_erased_current_keeps_the_spine.2.2, rfl, rfl, rfl⟩

theorem forged_source_accounts_are_refused :
    (issueCut jointRun).bind (fun issued =>
        some (admitTag issued (mapPayment 9 jointRun) issued.ledger issued.roots
            {Right.inspect} {Right.inspect} none,
          admitTag issued (mapOccurrence (withTrace [9]) jointRun) issued.ledger
            issued.roots {Right.inspect} {Right.inspect} none,
          admitTag issued jointRun jointReversedLedger issued.roots
            {Right.inspect} {Right.inspect} none,
          admitTag issued jointRun issued.ledger [] {Right.inspect} {Right.inspect} none,
          admitTag issued (mapOccurrence (withLineage 0) jointRun) issued.ledger
            issued.roots {Right.inspect} {Right.inspect} none,
          admitTag issued (mapOccurrence (withLineage 9) jointRun) issued.ledger
            issued.roots {Right.inspect} {Right.inspect} none,
          admitTag issued (mapOccurrence (withPath [9]) jointRun) issued.ledger
            issued.roots {Right.inspect} {Right.inspect} none,
          admitTag issued (mapOccurrence (plantCurrent issued.absent) jointRun)
            issued.ledger issued.roots {Right.inspect} {Right.inspect} none,
          admitTag issued (mapOccurrence (withSpine []) jointRun) issued.ledger
            issued.roots {Right.inspect} {Right.inspect} none,
          admitTag issued orWorlds issued.ledger issued.roots
            {Right.inspect} {Right.inspect} none,
          admitTag issued [] issued.ledger issued.roots
            {Right.inspect} {Right.inspect} none)) =
      some (5, 5, 5, 4, 1, 1, 1, 2, 2, 6, 4) ∧
      retainedTag (admitJointAt (mapPayment 9 jointRun) (jointOwnPath jointRun)
          (jointOwnSpine jointRun) {Right.inspect} {Right.inspect}) = 0 ∧
      retainedTag (admitJointAt (mapOccurrence (withTrace [9]) jointRun)
          (jointOwnPath jointRun) (jointOwnSpine jointRun)
          {Right.inspect} {Right.inspect}) = 0 ∧
      retainedTag (admitJointAt (mapOccurrence (withLineage 0) jointRun)
          (jointOwnPath jointRun) (jointOwnSpine jointRun)
          {Right.inspect} {Right.inspect}) = 0 ∧
      (issueCut jointRun).bind (fun issued =>
        some (retainedTag (admitJointAt
            (mapOccurrence (plantCurrent issued.absent) jointRun)
            (jointOwnPath jointRun) (jointOwnSpine jointRun)
            {Right.inspect} {Right.inspect}))) = some 0 ∧
      (issueCut jointRun).bind (fun issued =>
        some (keptLedger issued (mapPayment 9 jointRun) issued.ledger issued.roots
          {Right.inspect} {Right.inspect} none)) = some jointProductionLedger ∧
      (issueCut jointRun).bind (fun issued =>
        some ((admitIssued issued ⟨jointRun, issued.ledger, [], {Right.inspect},
          {Right.inspect}, none⟩).kept.cut)) = some jointRun := by
  exact ⟨rfl, by decide, by decide, by decide, rfl, rfl, rfl⟩

theorem conflicting_owner_fails_source_admission :
    (issueCut jointRun).bind (fun issued =>
        some (admitTag issued jointRun issued.ledger issued.roots
          {Right.inspect} ∅ (some (jointOwnerClaim 1)))) = some 5 ∧
      (issueCut jointRun).bind (fun issued =>
        some (keptLedger issued jointRun issued.ledger issued.roots
          {Right.inspect} ∅ (some (jointOwnerClaim 1)))) = some jointProductionLedger ∧
      Scoped.merge? (jointOwnerClaim 0) (jointOwnerClaim 1) = none := by
  exact ⟨rfl, rfl, joint_rival_owners_are_refused⟩

theorem retiring_one_owner_keeps_the_other :
    (issueCut jointRun).bind (fun issued =>
        match issued.handles with
        | [left, right] =>
            match releaseJoint issued.registry left with
            | (some (next, cleared), visits) =>
                some (visits, cleared.store, cleared.row.token, next.identity,
                  (lookupJoint next right).1, (lookupJoint next left).1,
                  decide (left.row ∉ next.rows), decide (right.row ∈ next.rows),
                  decide (issued.registry.rows.Nodup), issued.payment,
                  decide (issued.ledger = jointProductionLedger),
                  denote issued.ledger)
            | (none, _) => none
        | _ => none) = some (1, 0, 0, 2, some 0, none, true, true, true, 4, true, 4) ∧
      (issueCut jointRun).bind (fun issued =>
        match issued.handles with
        | [left, right] =>
            some ((releaseJoint issued.registry { right with store := 0 }).1.isNone,
              (releaseJoint issued.registry { right with store := 0 }).2,
              (releaseJoint issued.registry { right with row.token := 0 }).1.isNone,
              (releaseJoint issued.registry { right with row.token := 0 }).2,
              (releaseJoint issued.registry
                { right with row.provider := left.row.provider }).1.isNone,
              (releaseJoint issued.registry
                { right with row.provider := left.row.provider }).2,
              (lookupJoint issued.registry left).1,
              (lookupJoint issued.registry right).1)
        | _ => none) = some (true, 0, true, 0, true, 2, some 0, some 1) ∧
      unread (cancelConsumer (consumersOf jointValue) 0).log 0 = [] ∧
      unread (cancelConsumer (consumersOf jointValue) 0).log 1 =
        [jointLeftCell, jointRightCell] := by
  exact ⟨rfl, rfl, by decide, by decide⟩

theorem source_registry_uses_the_issued_return_laws
    {registry : JointIssuedRegistry} {left right : JointIssuedHandle}
    {next : JointIssuedRegistry} {cleared : JointIssuedHandle} {visits : Nat}
    (released : releaseJoint registry left = (some (next, cleared), visits))
    (different : right.row ≠ left.row)
    (unique : registry.rows.Nodup) :
    (Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Authenticated next right ↔
        Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Authenticated
          registry right) ∧
      left.row ∉ next.rows ∧ next.rows.Nodup ∧
      next.rows.length + 1 = registry.rows.length ∧
      ((lookupJoint registry left).1 ≠ none ↔
        Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Authenticated
          registry left) := by
  have removedPack :=
    Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.releaseIssued_removes_unique
      registry left next cleared visits released unique
  exact ⟨
    Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.releaseIssued_keeps_other
      registry left right next cleared visits released different,
    removedPack.1, removedPack.2.1, removedPack.2.2,
    Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.lookup_authenticates
      registry left⟩

theorem source_registry_refuses_a_missing_lookup
    {registry : JointIssuedRegistry} {handle : JointIssuedHandle}
    (missing : (lookupJoint registry handle).1 = none) :
    releaseJoint registry handle = (none, (lookupJoint registry handle).2) :=
  Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.releaseIssued_refused
    registry handle missing

theorem source_issue_preserves_the_or_boundary :
    (issueCut jointRun).map SourceCertificate.ledger = some jointProductionLedger ∧
      jointProductionLedger ≠ jointReversedLedger ∧
      (disposeAdmitted leftAccount leftAccount leftClaim leftClaim).joined =
        some leftReceiptLedger ∧
      (disposeAdmitted leftAccount rightAccount leftClaim rightClaim).joined = none ∧
      (⟨[0]⟩ : Coeff) * ⟨[0, 0]⟩ = ⟨[0, 0]⟩ * ⟨[0]⟩ ∧
      (⟨[0, 1]⟩ : Coeff) * ⟨[1]⟩ ≠ ⟨[1]⟩ * ⟨[0, 1]⟩ := by
  exact ⟨rfl,
    joint_source_order_is_not_the_reversed_sidecar.2.2.1.symm,
    copied_ledger_is_not_an_independent_and.1,
    joint_execution_is_not_the_payload_split.2.2.2.2.2.2.1,
    nested_fork_words_commute_and_branch_words_do_not.1,
    nested_fork_words_commute_and_branch_words_do_not.2⟩

/-- Replacing the suspended continuation, or the halted leaf's commit owner,
keeps the path, census, ledger, and roots. `admitViews` accepts both.
The issued fuel-3 control is not `.run .start []`. The issued fuel-15
control is the halted value. -/
theorem spoofed_continuation_passes_the_view_gate :
    (issueCut jointForceCut).bind (fun issued =>
        some (admitViewTag issued spoofedSuspension issued.ledger issued.roots
          {Right.force} {Right.force} none,
          decide (issued.control = .run .start []),
          decide (issued.halted = false))) = some (0, false, true) ∧
      (spoofedSuspension.map fun leaf => (retained leaf.1).state.control) =
        [.run .start []] ∧
      (issueCut jointRun).bind (fun issued =>
        some (admitViewTag issued spoofedOwner issued.ledger issued.roots
          {Right.inspect} {Right.inspect} none,
          issued.control)) = some (0, .halted (.value jointValue)) ∧
      (spoofedOwner.map fun leaf => (retained leaf.1).state.control) =
        [.returned (.value jointValue) [.commit jointLeftCell 9]] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A payment copied from the leaf issues itself and the view gate accepts
that copy. The copied debit is `9` while the ledger denotes `4`. The
passive reader refuses that payment. It does not replay, so it copies a
spoofed continuation instead of repairing it. `replayAccount [9]` is the
external check and returns `none`. -/
theorem forged_leaf_issues_itself :
    (issueSelfCut (mapPayment 9 jointRun)).bind (fun copied =>
        some (copied.payment, denote copied.ledger,
          admitViewTag copied (mapPayment 9 jointRun) copied.ledger copied.roots
            {Right.inspect} {Right.inspect} none,
          admitTag copied (mapPayment 9 jointRun) copied.ledger copied.roots
            {Right.inspect} {Right.inspect} none)) = some (9, 4, 0, 5) ∧
      issueCut (mapPayment 9 jointRun) = none ∧
      replayAccount [9] = none ∧
      (issueCut spoofedSuspension).map SourceCertificate.control =
        some (.run .start []) ∧
      (issueCut jointForceCut).bind (fun issued =>
        some (decide (issued.control = .run .start []))) = some false ∧
      (issueCut spoofedOwner).map SourceCertificate.control =
        some (.returned (.value jointValue) [.commit jointLeftCell 9]) ∧
      (issueBudget 15).map SourceCertificate.payment = some 4 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Budgets `0`, `3`, `6`, `11`, and `15` are slices of this source. The
debit on each issued certificate is the denotation of its retained ledger. -/
theorem source_budgets_issue_the_reached_slices :
    issueBudget 0 = issueCut (contributions jointSource 0 jointInitial) ∧
      issueBudget 3 = issueCut jointForceCut ∧
      issueBudget 6 = issueCut jointEarnedCut ∧
      issueBudget 11 = issueCut jointBothCut ∧
      issueBudget 15 = issueCut jointRun ∧
      (issueBudget 0).map SourceCertificate.payment =
        some (denote ([] : JointLedger)) ∧
      (issueBudget 3).map SourceCertificate.payment = some 1 ∧
      (issueBudget 6).map SourceCertificate.ledger = some jointEarnedLedger ∧
      (issueBudget 6).map SourceCertificate.payment =
        some (denote jointEarnedLedger) ∧
      (issueBudget 11).map SourceCertificate.ledger = some jointProductionLedger ∧
      (issueBudget 15).map SourceCertificate.ledger = some jointProductionLedger ∧
      (issueBudget 15).map SourceCertificate.payment =
        some (denote jointProductionLedger) ∧
      (issueBudget 15).map SourceCertificate.control =
        some (.halted (.value jointValue)) ∧
      contributions jointSource (6 + 9) jointInitial = jointRun := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem issueLeaf_exposes_the_earned_leaf
    {leaf : (JointOccurrence ⊕ JointOccurrence) × Nat}
    {cert : SourceCertificate}
    (issued : issueLeaf leaf = some cert) :
    ∃ ledger rows,
      ledger = (readGraph (retained leaf.1).state.world.receipts.nodes).factors ∧
        leaf.2 = denote ledger ∧
        retainedRows (retained leaf.1).state ledger = some rows ∧
        cert = certificateOf (retained leaf.1).state (retained leaf.1).trace
          ledger rows := by
  unfold issueLeaf at issued
  split at issued
  · simp at issued
  · rename_i payOk
    split at issued
    · simp at issued
    · rename_i rows hrows
      cases issued
      refine ⟨(readGraph (retained leaf.1).state.world.receipts.nodes).factors,
        rows, rfl, ?_, hrows, rfl⟩
      by_cases hEq : leaf.2 =
          denote (readGraph (retained leaf.1).state.world.receipts.nodes).factors
      · exact hEq
      · exact (payOk (decide_eq_true hEq)).elim

/-- External verification agrees with a retained history, and the
transition clock is that history's path length. Neither quantity is the
earned debit. This walk calls `step`; `issueEarned` does not. -/
theorem replay_verifies_the_earned_history
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target) :
    replayAccount (earnedTrace history) = some (target, earnedLedger history) ∧
      target.work.transitions =
        jointStart.work.transitions +
          EventPath.pathLength (machinePresentation jointSpec)
            (historyEventPath jointSpec jointStart history) := by
  refine ⟨?_, transitions_eq_pathLength jointSpec
      (historyEventPath jointSpec jointStart history)⟩
  simpa [replayAccount, earnedTrace, earnedLedger] using
    trace_replay_of_history jointSpec jointAssignment jointStart history

/-- A history that issues passively stores the history trace, the
production-ledger debit, and the endpoint residual, including the
allocator and evaluator counters. `replayAccount` agrees afterwards; it
is not used to build the certificate. -/
theorem earned_history_is_the_passive_issuer
    {target : JointMachine}
    {history : History (pathMachine jointSpec jointStart) jointStart target}
    {cert : SourceCertificate}
    (issued : issueEarned history = some cert) :
    cert.trace = earnedTrace history ∧
      cert.ledger = earnedLedger history ∧
      cert.payment = denote cert.ledger ∧
      cert.control = target.control ∧
      cert.work = target.work ∧
      cert.receipts = target.world.receipts ∧
      cert.halted = isHalted target ∧
      cert.nextCell = target.world.nextCell ∧
      cert.nextEvaluator = target.world.nextEvaluator ∧
      target.work.transitions =
        jointStart.work.transitions +
          EventPath.pathLength (machinePresentation jointSpec)
            (historyEventPath jointSpec jointStart history) ∧
      replayAccount cert.trace = some (target, cert.ledger) ∧
      residualAgrees cert ⟨[(Sum.inr ⟨target, cert.trace⟩, cert.payment)],
        cert.ledger, cert.roots, cert.rights, ∅, none⟩ = true := by
  unfold issueEarned at issued
  split at issued
  · simp at issued
  · rename_i rows _hrows
    cases issued
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · exact transitions_eq_pathLength jointSpec
        (historyEventPath jointSpec jointStart history)
    · simpa [replayAccount, earnedTrace, earnedLedger] using
        trace_replay_of_history jointSpec jointAssignment jointStart history
    · simp only [residualAgrees, retained, Sum.elim_inr, Bool.and_eq_true]
      repeat (first | apply And.intro | (apply decide_eq_true; rfl) | rfl)

/-- A budget that issues has a real history from `jointStart`. The
certificate debit equals that history's production denotation. The
residual, including the allocator and evaluator counters, is the reached
leaf. Replay of the trace is a separate verification. -/
theorem issueBudget_derives_the_source_account
    (budget : Nat) {cert : SourceCertificate}
    (issued : issueBudget budget = some cert) :
    ∃ leaf,
      contributions jointSource budget jointInitial = [leaf] ∧
        ∃ history : History (pathMachine jointSpec jointStart) jointStart
            (retained leaf.1).state,
          indices (pathMachine jointSpec jointStart) history = cert.trace ∧
            denote (productionLedger jointSpec jointAssignment
                (historyEventPath jointSpec jointStart history)) =
              cert.payment ∧
              Valid (productionLedger jointSpec jointAssignment
                (historyEventPath jointSpec jointStart history)) ∧
              denote cert.ledger = cert.payment ∧
              (retained leaf.1).state.control = cert.control ∧
              (retained leaf.1).trace = cert.trace ∧
              (retained leaf.1).state.work = cert.work ∧
              (retained leaf.1).state.world.receipts = cert.receipts ∧
              isHalted (retained leaf.1).state = cert.halted ∧
              (retained leaf.1).state.world.nextCell = cert.nextCell ∧
              (retained leaf.1).state.world.nextEvaluator = cert.nextEvaluator ∧
              replayAccount cert.trace =
                some ((retained leaf.1).state,
                  productionLedger jointSpec jointAssignment
                    (historyEventPath jointSpec jointStart history)) ∧
              (retained leaf.1).state.work.transitions =
                jointStart.work.transitions +
                  EventPath.pathLength (machinePresentation jointSpec)
                    (historyEventPath jointSpec jointStart history) := by
  unfold issueBudget at issued
  split at issued
  · rename_i leaf hcut
    have exposed := issueLeaf_exposes_the_earned_leaf issued
    obtain ⟨ledger, _rows, _ledgerEq, payEq, _rowsEq, certEq⟩ := exposed
    have traceEq : (retained leaf.1).trace = cert.trace := by
      rw [certEq]
    have paymentEq : cert.payment = denote ledger := by
      rw [certEq]
    have hcutStart :
        contributions jointSource budget ⟨jointStart, []⟩ = [leaf] := by
      simpa [jointInitial] using hcut
    have member : leaf ∈ contributions jointSource budget ⟨jointStart, []⟩ := by
      rw [hcutStart]
      exact List.mem_cons_self
    obtain ⟨history, traced, validLedger, denoted⟩ :=
      retained_production_ledger jointSpec jointAssignment jointStart budget
        ⟨jointStart, []⟩ member
    have indicesEq : indices (pathMachine jointSpec jointStart) history = cert.trace := by
      have raw : indices (pathMachine jointSpec jointStart) history =
          (retained leaf.1).trace := by
        simpa [List.nil_append] using traced
      rw [raw, traceEq]
    have replayed := trace_replay_of_history jointSpec jointAssignment jointStart history
    rw [indicesEq] at replayed
    refine ⟨leaf, ⟨hcut, history, indicesEq, ?_, validLedger, ?_, ?_, traceEq,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact (denoted.trans payEq).trans paymentEq.symm
    · rw [certEq]
    · rw [certEq]
    · rw [certEq]
    · rw [certEq]
    · rw [certEq]
    · rw [certEq]
    · rw [certEq]
    · simpa [replayAccount] using replayed
    · exact transitions_eq_pathLength jointSpec
        (historyEventPath jointSpec jointStart history)
  · simp at issued

/-- The view gate still accepts the replaced suspension and the forged
commit owner. Residual admission rejects both and keeps the submitted cut
and ledger. -/
theorem spoofed_continuation_fails_residual_admission :
    (issueCut jointForceCut).bind (fun issued =>
        some (admitTag issued spoofedSuspension issued.ledger issued.roots
          {Right.force} {Right.force} none,
          (admitIssued issued ⟨spoofedSuspension, issued.ledger, issued.roots,
            {Right.force}, {Right.force}, none⟩).kept.cut,
          (admitIssued issued ⟨spoofedSuspension, issued.ledger, issued.roots,
            {Right.force}, {Right.force}, none⟩).kept.ledger)) =
      (issueCut jointForceCut).bind (fun issued =>
        some (5, spoofedSuspension, issued.ledger)) ∧
      (issueCut jointRun).bind (fun issued =>
        some (admitTag issued spoofedOwner issued.ledger issued.roots
          {Right.inspect} {Right.inspect} none,
          (admitIssued issued ⟨spoofedOwner, issued.ledger, issued.roots,
            {Right.inspect}, {Right.inspect}, none⟩).kept.cut,
          (admitIssued issued ⟨spoofedOwner, issued.ledger, issued.roots,
            {Right.inspect}, {Right.inspect}, none⟩).kept.ledger)) =
        (issueCut jointRun).bind (fun _issued =>
          some (5, spoofedOwner, jointProductionLedger)) := by
  exact ⟨rfl, rfl⟩

/-- An extra observe leaves the production ledger in place and changes the
receipt graph. A bumped work counter leaves the graph in place. The view
gate accepts both. Residual admission rejects both and keeps the cut. -/
theorem repeated_observation_fails_residual_admission :
    (issueCut jointRun).bind (fun issued =>
        some (admitViewTag issued repeatedObservation issued.ledger issued.roots
            {Right.inspect} {Right.inspect} none,
          admitTag issued repeatedObservation issued.ledger issued.roots
            {Right.inspect} {Right.inspect} none,
          admitViewTag issued bumpedWork issued.ledger issued.roots
            {Right.inspect} {Right.inspect} none,
          admitTag issued bumpedWork issued.ledger issued.roots
            {Right.inspect} {Right.inspect} none,
          (admitIssued issued ⟨repeatedObservation, issued.ledger, issued.roots,
            {Right.inspect}, {Right.inspect}, none⟩).kept.cut,
          (admitIssued issued ⟨bumpedWork, issued.ledger, issued.roots,
            {Right.inspect}, {Right.inspect}, none⟩).kept.ledger)) =
        (issueCut jointRun).bind (fun _issued =>
          some (0, 5, 0, 5, repeatedObservation, jointProductionLedger)) ∧
      decide ((issueCut repeatedObservation).map
          (fun cert => cert.receipts.nodes.length) =
        (issueCut jointRun).map (fun cert => cert.receipts.nodes.length)) = false ∧
      decide ((issueCut bumpedWork).map SourceCertificate.work =
        (issueCut jointRun).map SourceCertificate.work) = false := by
  exact ⟨rfl, by decide, by decide⟩

/-- An evaluating owner planted on the earned cell changes the census
lookup. Both gates refuse it as `changedDependency` and keep the earned
ledger. -/
theorem evaluating_owner_fails_the_census :
    (issueCut jointEarnedCut).bind (fun issued =>
        some (admitViewTag issued evaluatingOwner issued.ledger issued.roots
            {Right.force} {Right.force} none,
          admitTag issued evaluatingOwner issued.ledger issued.roots
            {Right.force} {Right.force} none,
          keptLedger issued evaluatingOwner issued.ledger issued.roots
            {Right.force} {Right.force} none)) = some (2, 2, jointEarnedLedger) := by
  exact rfl

/-- Substituting the allocator and evaluator counters leaves the halted
control, the heap spine, and the receipt ledger in place. The view gate
accepts that presentation. The residual on the same certificate rejects
it and keeps the submitted cut. The passive reader of the substituted
leaf copies the forged counters. -/
theorem substituted_counters_fail_the_residual :
    (issueCut jointRun).bind (fun issued =>
        some (admitViewTag issued substitutedCounters issued.ledger issued.roots
            {Right.inspect} {Right.inspect} none,
          admitTag issued substitutedCounters issued.ledger issued.roots
            {Right.inspect} {Right.inspect} none,
          decide (issued.nextCell = 9),
          decide (issued.nextEvaluator = 9),
          (admitIssued issued ⟨substitutedCounters, issued.ledger,
            issued.roots, {Right.inspect}, {Right.inspect}, none⟩).kept.cut)) =
        (issueCut jointRun).bind (fun _issued =>
          some (0, 5, false, false, substitutedCounters)) ∧
      (substitutedCounters.map fun leaf =>
        ((retained leaf.1).state.control,
          (retained leaf.1).state.world.heap.spine,
          (readGraph (retained leaf.1).state.world.receipts.nodes).factors,
          (retained leaf.1).state.world.nextCell,
          (retained leaf.1).state.world.nextEvaluator)) =
        (jointRun.map fun leaf =>
          ((retained leaf.1).state.control,
            (retained leaf.1).state.world.heap.spine,
            (readGraph (retained leaf.1).state.world.receipts.nodes).factors,
            9, 9)) ∧
      (issueCut substitutedCounters).map
        (fun cert => (cert.nextCell, cert.nextEvaluator)) = some (9, 9) := by
  exact ⟨rfl, rfl, rfl⟩

/-- The external walk's length is not the earned debit. Fuel 15 takes 14
source steps and pays `4`. `replayAccount` is that walk. -/
theorem verification_walk_is_not_the_earned_debit :
    replayAccount = traceReplay jointSpec jointAssignment jointStart ∧
      (issueCut jointForceCut).map
        (fun cert => (cert.trace.length, cert.work.transitions, cert.payment)) =
        some (3, 3, 1) ∧
      (issueCut jointEarnedCut).map
        (fun cert => (cert.trace.length, cert.work.transitions, cert.payment)) =
        some (6, 6, 2) ∧
      (issueCut jointRun).map
        (fun cert => (cert.trace.length, cert.work.transitions, cert.payment)) =
        some (14, 14, 4) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Releasing one issued row of any budget that actually issued clears only
that row's store and token. The derived debit stays the denotation of the
issued ledger. -/
theorem authenticated_release_keeps_the_earned_debit
    (budget : Nat) {cert : SourceCertificate}
    (issued : issueBudget budget = some cert)
    {handle : JointIssuedHandle}
    {next : JointIssuedRegistry} {cleared : JointIssuedHandle} {visits : Nat}
    (released : releaseJoint cert.registry handle = (some (next, cleared), visits))
    (unique : cert.registry.rows.Nodup) :
    denote cert.ledger = cert.payment ∧
      handle.row ∉ next.rows ∧ next.rows.Nodup ∧
      next.rows.length + 1 = cert.registry.rows.length ∧
      cleared.store = 0 ∧ cleared.row.token = 0 := by
  obtain ⟨_leaf, _cutEq, historyPack⟩ :=
    issueBudget_derives_the_source_account budget issued
  obtain ⟨_history, _indicesEq, _denoteHist, _validLedger, denoteEq, _controlEq,
      _traceEq, _workEq, _receiptsEq, _haltedEq, _nextCellEq, _nextEvaluatorEq,
      _replayEq, _clockEq⟩ := historyPack
  have removed :=
    Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.releaseIssued_removes_unique
      cert.registry handle next cleared visits released unique
  cases hlookup : (lookupJoint cert.registry handle).1 with
  | none =>
      have refused :=
        Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.releaseIssued_refused
          cert.registry handle hlookup
      simp [refused] at released
  | some index =>
      obtain ⟨_remaining, exactRelease, _perm⟩ :=
        Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.releaseIssued_selected
          cert.registry handle index hlookup
      have clearedStore : cleared.store = 0 ∧ cleared.row.token = 0 := by
        unfold releaseJoint at released
        rw [exactRelease] at released
        obtain ⟨optionEq, _visitsEq⟩ := Prod.mk.inj released
        obtain ⟨_registryEq, clearedEq⟩ := Prod.mk.inj (Option.some.inj optionEq)
        subst clearedEq
        exact ⟨rfl, rfl⟩
      exact ⟨denoteEq, removed.1, removed.2.1, removed.2.2, clearedStore.1, clearedStore.2⟩

/-! ### Authenticated resumption

`weightedResume` is the common continuation already used by
`joint_source_cut_continues` and
`source_cut_continues_with_the_incoming_coefficient`. Returned leaves
keep their weight. Pending leaves are the suffix run, multiplied on the
left by the payment already earned. It does not take a caller-supplied
correspondence.

The joint consumer is `consumeAuthenticated`. The certificate comes from
`issueEarned`. The gate is `admitIssued`. The honest presentation is
`endpointAccount`: the history endpoint, its earned trace, and the
denotation of its production ledger. A raw `SourceCertificate` is not
this entry.
-/

def weightedResume {State : Type*}
    (source : Coalgebra State State Nat) (suffix : Nat)
    (prefixCut : List ((State ⊕ State) × Nat)) :
    List ((State ⊕ State) × Nat) :=
  sequence prefixCut fun leaf =>
    match leaf with
    | .inl answer => [(.inl answer, (1 : Nat))]
    | .inr pending => contributions source suffix pending

theorem weighted_resume_is_the_source_run
    {State : Type*} (source : Coalgebra State State Nat)
    (first suffix : Nat) (before : State) :
    contributions source (first + suffix) before =
      weightedResume source suffix (contributions source first before) := by
  rw [contributions_add]
  unfold weightedResume
  apply congrArg fun continuation =>
    sequence (contributions source first before) continuation
  funext leaf
  cases leaf <;> rfl

theorem resumed_payment_keeps_the_prefix
    {State : Type*} (source : Coalgebra State State Nat)
    {first suffix : Nat} {before pending : State} {prior : Nat}
    {leaf : (State ⊕ State) × Nat}
    (reached : (Sum.inr pending, prior) ∈ contributions source first before)
    (continued : leaf ∈ contributions source suffix pending) :
    (leaf.1, prior * leaf.2) ∈ contributions source (first + suffix) before :=
  contributions_continue source reached continued

theorem resumed_returns_keep_prefix_answers
    {State : Type*} (source : Coalgebra State State Nat)
    (first suffix : Nat) (before : State) :
    (returnedContributions (contributions source first before)).Sublist
      (returnedContributions (contributions source (first + suffix) before)) :=
  returned_sublist_add source first suffix before

theorem joint_resume_uses_the_recorded_composition (first second : Nat) :
    weightedResume jointSource second (contributions jointSource first jointInitial) =
      contributions jointSource (first + second) jointInitial := by
  unfold weightedResume
  have continued := joint_source_cut_continues first second
  rw [continued]
  apply congrArg fun continuation =>
    sequence (contributions jointSource first jointInitial) continuation
  funext leaf
  cases leaf <;> rfl

theorem payload_resume_uses_the_recorded_composition (first second : Nat) :
    weightedResume payloadSource second
        (contributions payloadSource first payloadInitial) =
      contributions payloadSource (first + second) payloadInitial := by
  unfold weightedResume
  have continued :=
    source_cut_continues_with_the_incoming_coefficient first second
  rw [continued]
  apply congrArg fun continuation =>
    sequence (contributions payloadSource first payloadInitial) continuation
  funext leaf
  cases leaf <;> rfl

theorem joint_resumed_frontier_is_the_reference (first suffix : Nat) :
    ((weightedResume jointSource suffix
        (contributions jointSource first jointInitial)).map
      (fun leaf => (retained leaf.1).state)) =
      Mettapedia.Machines.BranchLocalNeed.NeedFrontierLaws.frontier
        jointSpec (first + suffix) jointStart := by
  rw [joint_resume_uses_the_recorded_composition first suffix]
  simpa [jointSource, jointInitial] using
    frontier_erasure jointSpec jointCoefficient (first + suffix) jointInitial

theorem payload_resumed_frontier_is_the_reference (first suffix : Nat) :
    ((weightedResume payloadSource suffix
        (contributions payloadSource first payloadInitial)).map
      (fun leaf => (retained leaf.1).state)) =
      Mettapedia.Machines.BranchLocalNeed.NeedFrontierLaws.frontier
        payloadSpec (first + suffix) payloadStart := by
  rw [payload_resume_uses_the_recorded_composition first suffix]
  simpa [payloadSource, payloadInitial] using
    frontier_erasure payloadSpec payloadCoefficient (first + suffix) payloadInitial

theorem payload_one_leaf_continues_inside_the_run
    {first suffix : Nat} {pending : PayloadOccurrence} {prior : Nat}
    {leaf : (PayloadOccurrence ⊕ PayloadOccurrence) × Nat}
    (reached : (Sum.inr pending, prior) ∈
      contributions payloadSource first payloadInitial)
    (continued : leaf ∈ contributions payloadSource suffix pending) :
    (leaf.1, prior * leaf.2) ∈
      contributions payloadSource (first + suffix) payloadInitial :=
  contributions_continue payloadSource reached continued

theorem payload_leaf_is_not_the_whole_frontier
    (fuel : Nat) (before : PayloadOccurrence)
    (leaf : (PayloadOccurrence ⊕ PayloadOccurrence) × Nat)
    (member : leaf ∈ contributions payloadSource fuel before)
    (longer : (contributions payloadSource fuel before).length ≠ 1) :
    (retained leaf.1).state ∈
        (contributions payloadSource fuel before).map
          (fun item => (retained item.1).state) ∧
      [(retained leaf.1).state] ≠
        (contributions payloadSource fuel before).map
          (fun item => (retained item.1).state) := by
  refine ⟨List.mem_map.mpr ⟨leaf, member, rfl⟩, ?_⟩
  intro same
  have lengths := congrArg List.length same
  simp only [List.length_singleton, List.length_map] at lengths
  exact longer lengths.symm

theorem payload_pending_cut_is_two_leaves :
    paidPendingCut.length = 2 := by decide

/-- A joint contribution's history starts at `jointStart` with the empty
trace, so `indices` is the occurrence trace and the debit is the
production denotation. This does not identify the receipt-graph factor
list with that production ledger at an arbitrary budget. -/
theorem joint_history_trace_starts_empty
    (fuel : Nat)
    {leaf : (JointOccurrence ⊕ JointOccurrence) × Nat}
    (member : leaf ∈ contributions jointSource fuel jointInitial) :
    ∃ history : History (pathMachine jointSpec jointStart) jointStart
        (retained leaf.1).state,
      indices (pathMachine jointSpec jointStart) history =
          (retained leaf.1).trace ∧
        denote (productionLedger jointSpec jointAssignment
          (historyEventPath jointSpec jointStart history)) = leaf.2 := by
  have memberStart : leaf ∈ contributions jointSource fuel ⟨jointStart, []⟩ := by
    simpa [jointInitial] using member
  obtain ⟨history, traced, _valid, denoted⟩ :=
    retained_production_ledger jointSpec jointAssignment jointStart fuel
      ⟨jointStart, []⟩ memberStart
  refine ⟨history, ?_, denoted⟩
  simpa [List.nil_append] using traced

theorem resumed_split_keeps_the_ordered_ledger
    {middle target : Mettapedia.OSLF.Binding.RewriteEventHistory.State
      (system (pathMachine jointSpec jointStart))}
    (earlier : Quiver.Path
      (⟨jointStart⟩ : Mettapedia.OSLF.Binding.RewriteEventHistory.State
        (system (pathMachine jointSpec jointStart))) middle)
    (later : Quiver.Path middle target) :
    traceReplayFrom jointSpec jointAssignment
        (productionLedger jointSpec jointAssignment
          (historyEventPath jointSpec jointStart earlier))
        middle.term (indices (pathMachine jointSpec jointStart) later) =
      some (target.term,
        productionLedger jointSpec jointAssignment
            (historyEventPath jointSpec jointStart earlier) ++
          productionLedger jointSpec jointAssignment
            (historyEventPath jointSpec jointStart later)) ∧
      denote (productionLedger jointSpec jointAssignment
          (historyEventPath jointSpec jointStart (earlier.comp later))) =
        denote (productionLedger jointSpec jointAssignment
            (historyEventPath jointSpec jointStart earlier)) *
          denote (productionLedger jointSpec jointAssignment
            (historyEventPath jointSpec jointStart later)) ∧
      target.term.work.transitions =
        jointStart.work.transitions +
          EventPath.pathLength (machinePresentation jointSpec)
            (historyEventPath jointSpec jointStart (earlier.comp later)) := by
  obtain ⟨replayed, denoted, prefixClock, suffixClock, _counted, _graded⟩ :=
    resumed_replay_accounts_the_work_clock jointSpec jointAssignment jointStart
      earlier later
  have lengths :
      EventPath.pathLength (machinePresentation jointSpec)
          (historyEventPath jointSpec jointStart (earlier.comp later)) =
        EventPath.pathLength (machinePresentation jointSpec)
            (historyEventPath jointSpec jointStart earlier) +
          EventPath.pathLength (machinePresentation jointSpec)
            (historyEventPath jointSpec jointStart later) := by
    rw [historyEventPath_comp]
    exact EventPath.pathLength_append (machinePresentation jointSpec)
      (historyEventPath jointSpec jointStart earlier)
      (historyEventPath jointSpec jointStart later)
  refine ⟨replayed, denoted, ?_⟩
  rw [suffixClock, prefixClock, Nat.add_assoc, lengths]

theorem joint_halt_clock_is_not_the_payment :
    (issueCut jointRun).map (fun cert =>
      decide (cert.work.transitions = cert.payment)) = some false ∧
      (issueCut jointRun).map (fun cert =>
        (cert.work.transitions, cert.payment, denote cert.ledger)) =
        some (14, 4, 4) := by
  exact ⟨rfl, rfl⟩

def endpointAccount {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target) :
    PresentedAccount :=
  ⟨[(if isHalted target then
        Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence)
      else
        Sum.inr (⟨target, earnedTrace history⟩ : JointOccurrence),
      denote (earnedLedger history))],
    earnedLedger history, rootedCells target, requiredRights target,
    requiredRights target, none⟩

structure ResumedAccount where
  account : PresentedAccount
  delivered : JointLedger
  produced : JointCut
  resumed : JointCut

def resumeAccepted (account : PresentedAccount) (delivered : JointLedger)
    (suffix : Nat) : ResumedAccount :=
  ⟨account, delivered,
    match account.cut with
    | [leaf] =>
        match leaf.1 with
        | .inl _ => []
        | .inr pending => contributions jointSource suffix pending
    | _ => [],
    weightedResume jointSource suffix account.cut⟩

def consumeAuthenticated {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (presented : PresentedAccount) (suffix : Nat) : RetainedAdmit ResumedAccount :=
  match issueEarned history with
  | none =>
      .reject .incoherentResidual
        ⟨presented, presented.ledger, [], presented.cut⟩
  | some cert =>
      match admitIssued cert presented with
      | .reject reason kept =>
          .reject reason ⟨kept, kept.ledger, [], kept.cut⟩
      | .accept account =>
          .accept (resumeAccepted account cert.ledger suffix)

def resumeEarned {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (suffix : Nat) : RetainedAdmit ResumedAccount :=
  consumeAuthenticated history (endpointAccount history) suffix

private theorem retainedRows_success
    {machine : JointMachine} {ledger : JointLedger} {rows : List JointIssuedRow}
    (kept : retainedRows machine ledger = some rows) :
    machine.world.lineage ≠ 0 ∧
      censusAgrees machine.world.heap = true ∧
      machine.world.freshCell 0 ∉ censusCells machine.world.heap.spine ∧
      machine.world.heap.lookup (machine.world.freshCell 0) = none ∧
      (readGraph machine.world.receipts.nodes).factors = ledger ∧
      issueRows (readGraph machine.world.receipts.nodes).owners ledger = some rows := by
  unfold retainedRows at kept
  simp (config := { zeta := true }) only [] at kept
  by_cases hlin : machine.world.lineage = 0
  · simp [decide_eq_true hlin] at kept
  · have hd : decide (machine.world.lineage = 0) = false := decide_eq_false hlin
    rw [hd] at kept
    have step2 : censusAgrees machine.world.heap = true ∧
        (if decide (machine.world.freshCell 0 ∈ censusCells machine.world.heap.spine) then
            none
          else if !decide (machine.world.heap.lookup (machine.world.freshCell 0) = none) then
            none
          else if decide ((readGraph machine.world.receipts.nodes).factors ≠ ledger) then
            none
          else
            issueRows (readGraph machine.world.receipts.nodes).owners ledger) =
          some rows := by
      cases hc : censusAgrees machine.world.heap with
      | false => simp [hc] at kept
      | true =>
          refine ⟨rfl, ?_⟩
          simpa [hc] using kept
    obtain ⟨censusOk, kept3⟩ := step2
    by_cases hmem : machine.world.freshCell 0 ∈ censusCells machine.world.heap.spine
    · simp [decide_eq_true hmem] at kept3
    · have hdMem : decide (machine.world.freshCell 0 ∈
          censusCells machine.world.heap.spine) = false := decide_eq_false hmem
      rw [hdMem] at kept3
      by_cases hlook : machine.world.heap.lookup (machine.world.freshCell 0) = none
      · have hdLook : decide (machine.world.heap.lookup (machine.world.freshCell 0) =
            none) = true := decide_eq_true hlook
        have hnot : (!decide (machine.world.heap.lookup (machine.world.freshCell 0) =
            none)) = false := by simp [hdLook]
        rw [hnot] at kept3
        by_cases hfac : (readGraph machine.world.receipts.nodes).factors = ledger
        · have hdFac : decide ((readGraph machine.world.receipts.nodes).factors ≠
              ledger) = false := decide_eq_false (by intro h; exact h hfac)
          rw [hdFac] at kept3
          exact ⟨hlin, censusOk, hmem, hlook, hfac, kept3⟩
        · simp [decide_eq_true hfac] at kept3
      · have hdLook : decide (machine.world.heap.lookup (machine.world.freshCell 0) =
            none) = false := decide_eq_false hlook
        have hnot : (!decide (machine.world.heap.lookup (machine.world.freshCell 0) =
            none)) = true := by simp [hdLook]
        simp [hnot] at kept3

private theorem admitViews_accepts
    (issued : SourceCertificate) (presented : PresentedAccount)
    (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat)
    (cutEq : presented.cut = [leaf])
    (lineagePos : (retained leaf.1).state.world.lineage ≠ 0)
    (producerEq : (retained leaf.1).state.world.lineage = issued.producer)
    (traceEq : (retained leaf.1).trace = issued.trace)
    (paymentEq : leaf.2 = issued.payment)
    (ledgerEq : presented.ledger = issued.ledger)
    (factorEq : (readGraph (retained leaf.1).state.world.receipts.nodes).factors =
      issued.ledger)
    (rootsEq : presented.roots = issued.roots)
    (rootedEq : rootedCells (retained leaf.1).state = issued.roots)
    (pathEq : (retained leaf.1).state.world.path = issued.path)
    (spineEq : (retained leaf.1).state.world.heap.spine = issued.spine)
    (presentEq : ((censusCells (retained leaf.1).state.world.heap.spine).map
        fun cell => (cell, (retained leaf.1).state.world.heap.lookup cell)) =
      issued.present)
    (absentEq : (retained leaf.1).state.world.heap.lookup issued.absent = none)
    (rightsHeld : issued.rights ⊆ presented.held)
    (requestHeld : (restrict? presented.held presented.requested).isNone = false) :
    admitViews issued presented = .accept presented := by
  unfold admitViews
  rw [cutEq]
  dsimp only
  have notZero : ¬ ((retained leaf.1).state.world.lineage = 0) := lineagePos
  have notForeign : ¬ ((retained leaf.1).state.world.lineage ≠ issued.producer) :=
    fun h => h producerEq
  have gStale : (decide ((retained leaf.1).state.world.lineage = 0) ||
      decide ((retained leaf.1).state.world.lineage ≠ issued.producer)) = false := by
    rw [decide_eq_false notZero, decide_eq_false notForeign]
    rfl
  rw [gStale]
  have notTrace : ¬ ((retained leaf.1).trace ≠ issued.trace) := fun h => h traceEq
  have notPay : ¬ (leaf.2 ≠ issued.payment) := fun h => h paymentEq
  have notLedger : ¬ (presented.ledger ≠ issued.ledger) := fun h => h ledgerEq
  have notFactor : ¬ ((readGraph (retained leaf.1).state.world.receipts.nodes).factors ≠
      issued.ledger) := fun h => h factorEq
  have gLedger : (decide ((retained leaf.1).trace ≠ issued.trace) ||
      decide (leaf.2 ≠ issued.payment) ||
      decide (presented.ledger ≠ issued.ledger) ||
      decide ((readGraph (retained leaf.1).state.world.receipts.nodes).factors ≠
        issued.ledger)) = false := by
    rw [decide_eq_false notTrace, decide_eq_false notPay,
      decide_eq_false notLedger, decide_eq_false notFactor]
    rfl
  rw [gLedger]
  have notRoots : ¬ (presented.roots ≠ issued.roots) := fun h => h rootsEq
  have notRooted : ¬ (rootedCells (retained leaf.1).state ≠ issued.roots) :=
    fun h => h rootedEq
  have gRoots : (decide (presented.roots ≠ issued.roots) ||
      decide (rootedCells (retained leaf.1).state ≠ issued.roots)) = false := by
    rw [decide_eq_false notRoots, decide_eq_false notRooted]
    rfl
  rw [gRoots]
  have gPath : decide ((retained leaf.1).state.world.path ≠ issued.path) = false :=
    decide_eq_false (fun h => h pathEq)
  rw [gPath]
  have notSpine : ¬ ((retained leaf.1).state.world.heap.spine ≠ issued.spine) :=
    fun h => h spineEq
  have notPresent : ¬ (((censusCells (retained leaf.1).state.world.heap.spine).map
      fun cell => (cell, (retained leaf.1).state.world.heap.lookup cell)) ≠
      issued.present) := fun h => h presentEq
  have gSpine : (decide ((retained leaf.1).state.world.heap.spine ≠ issued.spine) ||
      decide (((censusCells (retained leaf.1).state.world.heap.spine).map
          fun cell => (cell, (retained leaf.1).state.world.heap.lookup cell)) ≠
        issued.present) ||
      !decide ((retained leaf.1).state.world.heap.lookup issued.absent = none)) = false := by
    rw [decide_eq_false notSpine, decide_eq_false notPresent, decide_eq_true absentEq]
    rfl
  rw [gSpine]
  have gRights : (!decide (issued.rights ⊆ presented.held) ||
      (restrict? presented.held presented.requested).isNone) = false := by
    rw [decide_eq_true rightsHeld]
    exact requestHeld
  rw [gRights]
  rfl

private theorem admit_tagged_endpoint
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (rows : List JointIssuedRow)
    (hrows : retainedRows target (earnedLedger history) = some rows)
    (tag : JointOccurrence ⊕ JointOccurrence)
    (tagState : (retained tag).state = target)
    (tagTrace : (retained tag).trace = earnedTrace history) :
    let presented : PresentedAccount :=
      ⟨[(tag, denote (earnedLedger history))], earnedLedger history,
        rootedCells target, requiredRights target, requiredRights target, none⟩
    admitIssued (certificateOf target (earnedTrace history) (earnedLedger history) rows)
        presented = .accept presented ∧
      residualAgrees
        (certificateOf target (earnedTrace history) (earnedLedger history) rows)
        presented = true := by
  intro presented
  have facts := retainedRows_success hrows
  obtain ⟨lineagePos, _censusOk, _absentFresh, absentLookup, factorEq, _issuedRows⟩ := facts
  have views := admitViews_accepts
      (certificateOf target (earnedTrace history) (earnedLedger history) rows) presented
      (tag, denote (earnedLedger history)) rfl
      (by simpa [tagState] using lineagePos)
      (by rw [tagState])
      (by rw [tagTrace])
      (by rfl)
      (by rfl)
      (by rw [tagState]; exact factorEq)
      (by rfl)
      (by rw [tagState])
      (by rw [tagState])
      (by rw [tagState])
      (by rw [tagState])
      (by rw [tagState]; exact absentLookup)
      (by exact Finset.Subset.refl _)
      (by simp only [presented, restrict_same]; rfl)
  have residual : residualAgrees
      (certificateOf target (earnedTrace history) (earnedLedger history) rows)
      presented = true := by
    simp only [presented, residualAgrees, tagState, Bool.and_eq_true]
    repeat apply And.intro
    all_goals (first | exact decide_eq_true rfl | rfl)
  refine ⟨?_, residual⟩
  unfold admitIssued admitComparable
  simp only [presented, views, residual, if_true]

private theorem earned_endpoint_is_admitted
    {target : JointMachine}
    {history : History (pathMachine jointSpec jointStart) jointStart target}
    {cert : SourceCertificate}
    (issued : issueEarned history = some cert) :
    admitIssued cert (endpointAccount history) = .accept (endpointAccount history) := by
  unfold issueEarned at issued
  split at issued
  · simp at issued
  · rename_i rows hrows
    cases issued
    cases hhalt : isHalted target with
    | false =>
        have tagged := admit_tagged_endpoint history rows hrows
          (Sum.inr (⟨target, earnedTrace history⟩ : JointOccurrence))
          (by simp [retained]) (by simp [retained])
        have accountEq : endpointAccount history =
            ⟨[(Sum.inr (⟨target, earnedTrace history⟩ : JointOccurrence),
                denote (earnedLedger history))],
              earnedLedger history, rootedCells target, requiredRights target,
              requiredRights target, none⟩ := by
          simp [endpointAccount, hhalt]
        simpa [accountEq] using tagged.1
    | true =>
        have tagged := admit_tagged_endpoint history rows hrows
          (Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence))
          (by simp [retained]) (by simp [retained])
        have accountEq : endpointAccount history =
            ⟨[(Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence),
                denote (earnedLedger history))],
              earnedLedger history, rootedCells target, requiredRights target,
              requiredRights target, none⟩ := by
          simp [endpointAccount, hhalt]
        simpa [accountEq] using tagged.1

private theorem endpoint_admission_exposes_the_checked_views
    {target : JointMachine}
    {history : History (pathMachine jointSpec jointStart) jointStart target}
    {cert : SourceCertificate}
    (issued : issueEarned history = some cert) :
    admitViews cert (endpointAccount history) =
        .accept (endpointAccount history) ∧
      residualAgrees cert (endpointAccount history) = true := by
  have pack := earned_endpoint_is_admitted issued
  unfold admitIssued at pack
  have rivalNone : (endpointAccount history).rival = none := by
    unfold endpointAccount
    rfl
  rw [rivalNone] at pack
  change admitComparable cert (endpointAccount history) =
    .accept (endpointAccount history) at pack
  unfold admitComparable at pack
  split at pack
  · cases pack
  · rename_i _account viewsEq
    split at pack
    · rename_i residualEq
      have accountEq : _account = endpointAccount history := by
        injection pack
      cases accountEq
      exact ⟨viewsEq, residualEq⟩
    · cases pack

theorem earned_endpoint_is_consumed
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (suffix : Nat) {cert : SourceCertificate}
    (issued : issueEarned history = some cert) :
    resumeEarned history suffix =
      .accept (resumeAccepted (endpointAccount history) cert.ledger suffix) ∧
      cert.ledger = earnedLedger history ∧
      cert.payment = denote cert.ledger ∧
      cert.trace = earnedTrace history ∧
      cert.nextCell = target.world.nextCell ∧
      cert.nextEvaluator = target.world.nextEvaluator ∧
      cert.control = target.control := by
  obtain ⟨traceEq, ledgerEq, payEq, controlEq, _workEq, _receiptsEq, _haltedEq,
      cellEq, evalEq, _clockEq, _replayEq, _residualEq⟩ :=
    earned_history_is_the_passive_issuer issued
  have admitted := earned_endpoint_is_admitted issued
  refine ⟨?_, ledgerEq, payEq, traceEq, cellEq, evalEq, controlEq⟩
  unfold resumeEarned consumeAuthenticated
  simp only [issued, admitted]

private theorem admitViews_keeps (issued : SourceCertificate) (presented : PresentedAccount) :
    (admitViews issued presented).kept = presented := by
  unfold admitViews
  dsimp only
  repeat (first | rfl | split)

private theorem admitComparable_keeps (issued : SourceCertificate)
    (presented : PresentedAccount) :
    (admitComparable issued presented).kept = presented := by
  unfold admitComparable
  have keptViews := admitViews_keeps issued presented
  split
  · next reason kept hviews =>
      rw [hviews] at keptViews
      simpa [RetainedAdmit.kept] using keptViews
  · next account hviews =>
      rw [hviews] at keptViews
      have accountEq : account = presented := by
        simpa [RetainedAdmit.kept] using keptViews
      by_cases hres : residualAgrees issued presented = true
      · rw [if_pos hres]
        simpa [RetainedAdmit.kept] using accountEq
      · rw [if_neg hres]
        simp [RetainedAdmit.kept]

private theorem admitIssued_keeps (issued : SourceCertificate) (presented : PresentedAccount) :
    (admitIssued issued presented).kept = presented := by
  unfold admitIssued
  split
  · split
    · rfl
    · exact admitComparable_keeps issued presented
  · exact admitComparable_keeps issued presented

theorem consume_refusal_keeps_the_submitted_account
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (presented : PresentedAccount) (suffix : Nat)
    {reason : Refusal} {kept : ResumedAccount}
    (refused : consumeAuthenticated history presented suffix = .reject reason kept) :
    kept.account = presented ∧ kept.delivered = presented.ledger ∧
      kept.produced = [] ∧ kept.resumed = presented.cut := by
  unfold consumeAuthenticated at refused
  split at refused
  · cases refused
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rename_i cert _issuedSome
    split at refused
    · rename_i reason' keptAccount hadmit
      have keptEq : keptAccount = presented := by
        have same := admitIssued_keeps cert presented
        rw [hadmit] at same
        simpa [RetainedAdmit.kept] using same
      cases refused
      simp [keptEq]
    · simp at refused

private theorem issueEarned_matches_issueLeaf
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    {leaf : (JointOccurrence ⊕ JointOccurrence) × Nat}
    {cert : SourceCertificate}
    (endpoint : (retained leaf.1).state = target)
    (traceEq : (retained leaf.1).trace = earnedTrace history)
    (ledgerEq : earnedLedger history =
      (readGraph target.world.receipts.nodes).factors)
    (issued : issueLeaf leaf = some cert) :
    issueEarned history = some cert := by
  obtain ⟨ledger, rows, readEq, _leafPay, rowsEq, certEq⟩ :=
    issueLeaf_exposes_the_earned_leaf issued
  unfold issueEarned
  have sameLedger : ledger = earnedLedger history := by
    rw [readEq, endpoint]
    exact ledgerEq.symm
  have sameRows : retainedRows target (earnedLedger history) = some rows := by
    rw [endpoint] at rowsEq
    rw [sameLedger] at rowsEq
    exact rowsEq
  rw [sameRows]
  rw [certEq, endpoint, traceEq, sameLedger]

theorem suspended_consumer_resumes_the_source (suffix : Nat) :
    ∃ (pending : JointOccurrence)
      (history : History (pathMachine jointSpec jointStart) jointStart pending.state)
      (cert : SourceCertificate),
      issueEarned history = some cert ∧
        cert.halted = false ∧
        cert.rights = {Right.force} ∧
        cert.payment = 1 ∧
        cert.ledger = ([] : JointLedger) ∧
        cert.trace = jointForceTrace ∧
        decide (cert.control = .run .start []) = false ∧
        cert.nextCell = pending.state.world.nextCell ∧
        cert.nextEvaluator = pending.state.world.nextEvaluator ∧
        resumeEarned history suffix =
          .accept (resumeAccepted (endpointAccount history) cert.ledger suffix) ∧
        (resumeAccepted (endpointAccount history) cert.ledger suffix).delivered =
          ([] : JointLedger) ∧
        (resumeAccepted (endpointAccount history) cert.ledger suffix).resumed =
          contributions jointSource (3 + suffix) jointInitial ∧
        denote cert.ledger = 1 ∧
        issueCut jointForceCut = some cert := by
  obtain ⟨pending, cutEq, _pathEq, traceEq, haltedEq⟩ :=
    joint_one_pending 3 1 [] jointForceTrace joint_cut_marks.1
  have member : (Sum.inr pending, 1) ∈ contributions jointSource 3 jointInitial := by
    rw [cutEq]
    exact List.mem_cons_self
  obtain ⟨history, indicesEq, productionEq, _valid, _denoted⟩ :=
    trace_account_of_contribution jointSpec jointAssignment jointStart 3 member traceEq
      (by simpa [jointReplay] using joint_prefix_replays_are_the_source_ledgers.1)
  have endpoint : (retained (Sum.inr pending)).state = pending.state := by
    simp [retained]
  have historyTrace : (retained (Sum.inr pending)).trace = earnedTrace history := by
    simpa [earnedTrace, indicesEq] using traceEq
  have ledgerComputed : (issueCut jointForceCut).map SourceCertificate.ledger =
      some ([] : JointLedger) := by rfl
  have cutSome : ∃ cert, issueCut jointForceCut = some cert := by
    cases hcut : issueCut jointForceCut with
    | none => simp [hcut] at ledgerComputed
    | some cert => exact ⟨cert, rfl⟩
  obtain ⟨cert, cutIssued⟩ := cutSome
  have certLedger : cert.ledger = ([] : JointLedger) := by
    have mapped := ledgerComputed
    rw [cutIssued] at mapped
    exact Option.some.inj mapped
  have leafIssued : issueLeaf (Sum.inr pending, 1) = some cert := by
    simpa [issueCut, jointForceCut, cutEq] using cutIssued
  have readEq : (readGraph pending.state.world.receipts.nodes).factors =
      ([] : JointLedger) := by
    obtain ⟨ledger, _rows, ledgerEq, _pay, _rowsEq, certEq⟩ :=
      issueLeaf_exposes_the_earned_leaf leafIssued
    have certLedger' : cert.ledger = ledger := by rw [certEq]
    exact (certLedger'.symm.trans certLedger) ▸ ledgerEq.symm
  have historyLedger : earnedLedger history =
      (readGraph pending.state.world.receipts.nodes).factors := by
    rw [readEq]
    simpa [earnedLedger] using productionEq
  have issuedHistory : issueEarned history = some cert :=
    issueEarned_matches_issueLeaf history endpoint historyTrace historyLedger leafIssued
  have consumed := earned_endpoint_is_consumed history suffix issuedHistory
  have haltedTarget : isHalted (retained (Sum.inr pending, 1).1).state = false := by
    simpa [retained] using haltedEq
  have stateEq : (retained (Sum.inr pending, 1).1).state = pending.state := by
    simp [retained]
  have traceSame : indices (pathMachine jointSpec jointStart) history = pending.trace := by
    simpa [retained] using indicesEq.trans traceEq.symm
  have payLeaf : denote (earnedLedger history) = 1 := by
    simpa [earnedLedger] using
      (congrArg denote productionEq).trans
        joint_prefix_replays_are_the_source_ledgers.2.2.2.2.2.2.1
  have occEq : (⟨(retained (Sum.inr pending, 1).1).state,
      indices (pathMachine jointSpec jointStart) history⟩ : JointOccurrence) =
      pending := by
    cases pending with
    | mk pendingState pendingTrace =>
        simp [stateEq, traceSame]
  have accountCut : (endpointAccount history).cut = jointForceCut := by
    simp only [endpointAccount, haltedTarget, earnedTrace, occEq, payLeaf,
      jointForceCut, cutEq]
    simp only [if_neg Bool.false_ne_true]
  have resumed : (resumeAccepted (endpointAccount history) cert.ledger suffix).resumed =
      contributions jointSource (3 + suffix) jointInitial := by
    simp only [resumeAccepted, accountCut, jointForceCut]
    exact joint_resume_uses_the_recorded_composition 3 suffix
  refine ⟨pending, history, cert, issuedHistory, ?_, ?_, ?_, certLedger, ?_, ?_, ?_, ?_,
      consumed.1, ?_, resumed, ?_, cutIssued⟩
  · exact (earned_history_is_the_passive_issuer issuedHistory).2.2.2.2.2.2.1.trans
      haltedTarget
  · have rightsComputed : (issueCut jointForceCut).map SourceCertificate.rights =
        some {Right.force} := by rfl
    rw [cutIssued] at rightsComputed
    exact Option.some.inj rightsComputed
  · have payComputed : (issueCut jointForceCut).map SourceCertificate.payment = some 1 := by
      simpa [source_budgets_issue_the_reached_slices.2.1] using
        source_budgets_issue_the_reached_slices.2.2.2.2.2.2.1
    rw [cutIssued] at payComputed
    exact Option.some.inj payComputed
  · have traceComputed : (issueCut jointForceCut).map SourceCertificate.trace =
        some jointForceTrace := by rfl
    rw [cutIssued] at traceComputed
    exact Option.some.inj traceComputed
  · have controlComputed : (issueCut jointForceCut).bind (fun issuedCert =>
        some (decide (issuedCert.control = .run .start []))) = some false := by rfl
    rw [cutIssued] at controlComputed
    exact Option.some.inj controlComputed
  · simpa [stateEq] using consumed.2.2.2.2.1
  · simpa [stateEq] using consumed.2.2.2.2.2.1
  · simpa [resumeAccepted] using certLedger
  · rw [certLedger]
    exact joint_prefix_replays_are_the_source_ledgers.2.2.2.2.2.2.1

theorem earned_suspension_resumes_the_halted_run :
    ∃ (pending : JointOccurrence)
      (history : History (pathMachine jointSpec jointStart) jointStart pending.state)
      (cert : SourceCertificate),
      issueEarned history = some cert ∧
        cert.ledger = jointEarnedLedger ∧
        denote cert.ledger = 2 ∧
        cert.halted = false ∧
        resumeEarned history 9 =
          .accept (resumeAccepted (endpointAccount history) cert.ledger 9) ∧
        (resumeAccepted (endpointAccount history) cert.ledger 9).delivered =
          jointEarnedLedger ∧
        (resumeAccepted (endpointAccount history) cert.ledger 9).resumed = jointRun ∧
        (issueCut jointRun).map SourceCertificate.payment = some 4 := by
  obtain ⟨pending, cutEq, _pathEq, traceEq, haltedEq⟩ :=
    joint_one_pending 6 2 [0] jointEarnedTrace joint_cut_marks.2.1
  have member : (Sum.inr pending, 2) ∈ contributions jointSource 6 jointInitial := by
    rw [cutEq]
    exact List.mem_cons_self
  obtain ⟨history, indicesEq, productionEq, _valid, _denoted⟩ :=
    trace_account_of_contribution jointSpec jointAssignment jointStart 6 member traceEq
      (by simpa [jointReplay] using joint_prefix_replays_are_the_source_ledgers.2.1)
  obtain ⟨_b0, _b3, b6, _b11, b15, _p0, _p3, led6, _pay6, _led11, _led15, pay15,
      _ctrl15, split69⟩ := source_budgets_issue_the_reached_slices
  have ledgerComputed : (issueCut jointEarnedCut).map SourceCertificate.ledger =
      some jointEarnedLedger := by simpa [b6] using led6
  have cutSome : ∃ cert, issueCut jointEarnedCut = some cert := by
    cases hcut : issueCut jointEarnedCut with
    | none => simp [hcut] at ledgerComputed
    | some cert => exact ⟨cert, rfl⟩
  obtain ⟨cert, cutIssued⟩ := cutSome
  have certLedger : cert.ledger = jointEarnedLedger := by
    have mapped := ledgerComputed
    rw [cutIssued] at mapped
    exact Option.some.inj mapped
  have leafIssued : issueLeaf (Sum.inr pending, 2) = some cert := by
    simpa [issueCut, jointEarnedCut, cutEq] using cutIssued
  have endpoint : (retained (Sum.inr pending)).state = pending.state := by simp [retained]
  have historyTrace : (retained (Sum.inr pending)).trace = earnedTrace history := by
    simpa [earnedTrace, indicesEq] using traceEq
  have readEq : (readGraph pending.state.world.receipts.nodes).factors = jointEarnedLedger := by
    obtain ⟨ledger, _rows, ledgerEq, _pay, _rowsEq, certEq⟩ :=
      issueLeaf_exposes_the_earned_leaf leafIssued
    have certLedger' : cert.ledger = ledger := by rw [certEq]
    exact (certLedger'.symm.trans certLedger) ▸ ledgerEq.symm
  have historyLedger : earnedLedger history =
      (readGraph pending.state.world.receipts.nodes).factors := by
    rw [readEq]
    simpa [earnedLedger] using productionEq
  have issuedHistory : issueEarned history = some cert :=
    issueEarned_matches_issueLeaf history endpoint historyTrace historyLedger leafIssued
  have consumed := earned_endpoint_is_consumed history 9 issuedHistory
  have haltedTarget : isHalted (retained (Sum.inr pending, 2).1).state = false := by
    simpa [retained] using haltedEq
  have stateEq : (retained (Sum.inr pending, 2).1).state = pending.state := by
    simp [retained]
  have traceSame : indices (pathMachine jointSpec jointStart) history = pending.trace := by
    simpa [retained] using indicesEq.trans traceEq.symm
  have payLeaf : denote (earnedLedger history) = 2 := by
    simpa [earnedLedger] using
      (congrArg denote productionEq).trans
        joint_prefix_replays_are_the_source_ledgers.2.2.2.2.1
  have occEq : (⟨(retained (Sum.inr pending, 2).1).state,
      indices (pathMachine jointSpec jointStart) history⟩ : JointOccurrence) =
      pending := by
    cases pending with
    | mk pendingState pendingTrace =>
        simp [stateEq, traceSame]
  have accountCut : (endpointAccount history).cut = jointEarnedCut := by
    simp only [endpointAccount, haltedTarget, earnedTrace, occEq, payLeaf,
      jointEarnedCut, cutEq]
    simp only [if_neg Bool.false_ne_true]
  have resumed : (resumeAccepted (endpointAccount history) cert.ledger 9).resumed =
      jointRun := by
    simp only [resumeAccepted, accountCut]
    rw [show jointEarnedCut = contributions jointSource 6 jointInitial from rfl]
    exact (joint_resume_uses_the_recorded_composition 6 9).trans split69
  refine ⟨pending, history, cert, issuedHistory, certLedger, ?_, ?_, consumed.1, ?_,
      resumed, ?_⟩
  · rw [certLedger]
    exact joint_prefix_replays_are_the_source_ledgers.2.2.2.2.1
  · exact (earned_history_is_the_passive_issuer issuedHistory).2.2.2.2.2.2.1.trans
      haltedTarget
  · simpa [resumeAccepted] using certLedger
  · have mapped : (issueCut jointRun).map SourceCertificate.payment =
        some (denote jointProductionLedger) := by simpa [b15] using pay15
    simpa [joint_prefix_replays_are_the_source_ledgers.2.2.2.2.2.1] using mapped

/-- A refused admission returns the submitted account. It does not run the
suffix. -/
theorem issued_refusal_does_not_resume
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (presented : PresentedAccount) (suffix : Nat)
    {cert : SourceCertificate} {reason : Refusal}
    (issued : issueEarned history = some cert)
    (refused : admitIssued cert presented = .reject reason presented) :
    consumeAuthenticated history presented suffix =
      .reject reason ⟨presented, presented.ledger, [], presented.cut⟩ := by
  unfold consumeAuthenticated
  simp only [issued, refused]

theorem suspended_history_refuses_a_spoofed_control (suffix : Nat) :
    ∃ (pending : JointOccurrence)
      (history : History (pathMachine jointSpec jointStart) jointStart pending.state)
      (cert : SourceCertificate),
      issueEarned history = some cert ∧
        consumeAuthenticated history
          ⟨spoofedSuspension, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩
          suffix =
          .reject .incoherentResidual
            ⟨⟨spoofedSuspension, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩,
              cert.ledger, [], spoofedSuspension⟩ := by
  obtain ⟨pending, history, cert, issued, _halted, _rights, _pay, _ledger, _trace,
      _control, _cell, _eval, _accepted, _delivered, _resumed, _denote, cutIssued⟩ :=
    suspended_consumer_resumes_the_source suffix
  have raw :
      (issueCut jointForceCut).bind (fun issuedCert =>
        some (admitIssued issuedCert ⟨spoofedSuspension, issuedCert.ledger,
          issuedCert.roots, issuedCert.rights, issuedCert.rights, none⟩)) =
      (issueCut jointForceCut).bind (fun issuedCert =>
        some (.reject .incoherentResidual ⟨spoofedSuspension, issuedCert.ledger,
          issuedCert.roots, issuedCert.rights, issuedCert.rights, none⟩)) := by
    rfl
  rw [cutIssued] at raw
  have refused := Option.some.inj raw
  refine ⟨pending, history, cert, issued, ?_⟩
  exact issued_refusal_does_not_resume history
    ⟨spoofedSuspension, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩
    suffix issued refused

theorem suspended_history_refuses_a_stale_lineage (suffix : Nat) :
    ∃ (pending : JointOccurrence)
      (history : History (pathMachine jointSpec jointStart) jointStart pending.state)
      (cert : SourceCertificate),
      issueEarned history = some cert ∧
        consumeAuthenticated history
          ⟨mapOccurrence (withLineage 0) jointForceCut, cert.ledger, cert.roots,
            cert.rights, cert.rights, none⟩ suffix =
          .reject .staleWorld
            ⟨⟨mapOccurrence (withLineage 0) jointForceCut, cert.ledger, cert.roots,
                cert.rights, cert.rights, none⟩,
              cert.ledger, [], mapOccurrence (withLineage 0) jointForceCut⟩ := by
  obtain ⟨pending, history, cert, issued, _halted, _rights, _pay, _ledger, _trace,
      _control, _cell, _eval, _accepted, _delivered, _resumed, _denote, cutIssued⟩ :=
    suspended_consumer_resumes_the_source suffix
  have raw :
      (issueCut jointForceCut).bind (fun issuedCert =>
        some (admitIssued issuedCert ⟨mapOccurrence (withLineage 0) jointForceCut,
          issuedCert.ledger, issuedCert.roots, issuedCert.rights, issuedCert.rights,
          none⟩)) =
      (issueCut jointForceCut).bind (fun issuedCert =>
        some (.reject .staleWorld ⟨mapOccurrence (withLineage 0) jointForceCut,
          issuedCert.ledger, issuedCert.roots, issuedCert.rights, issuedCert.rights,
          none⟩)) := by
    rfl
  rw [cutIssued] at raw
  have refused := Option.some.inj raw
  refine ⟨pending, history, cert, issued, ?_⟩
  exact issued_refusal_does_not_resume history
    ⟨mapOccurrence (withLineage 0) jointForceCut, cert.ledger, cert.roots,
      cert.rights, cert.rights, none⟩
    suffix issued refused

/-! ### Returned inspection and one retired consumer

A production value is a parameter of a retained system. A consumer ticket
is that consumer's host epoch. `releaseIssued` clears one registry row.
None of these three is either of the others, and cancelling a consumer
does not free the production. Clearing a row does not free native memory,
and this sequential host is not a concurrency or service proof.

`snapshot` and `inspect` add no publication token. `publish` appends the
whole ordered production once. A copied ticket is refused. A later ticket
does not append it again. `shared_world` applies to one publication
action because every token of that action appends the same production.
Two actions that append different ordered ledgers do not commute, even
when the ledgers denote the same number. Identical appends commuting is
not independence for arbitrary source factors.

`authenticateConsumers` calls `consumeAuthenticated`. Only its accept
branch builds `Owned.Host` values, from the accepted delivered ledger,
and it keeps the whole `ResumedAccount`. Its reject branch keeps the
refused account and carries no host. Producer payment stays `denote` of
the one issued ledger. Two publishing hosts may record that ledger twice
as delivery observations; that list is not a second charge. On this
source the issued denotation is 4, so the concatenated ledger denotes
16. A ledger denoting 1 would not separate those two numbers. Fuel 15 is
one reached execution, not the arbitrary-budget equation
`read.factors = productionLedger`.
-/

open Mettapedia.Machines.OwnedPullDriver
open Owned
open Host

inductive ConsumerAct where
  | inspect
  | publish
  | retire

structure ConsumerSeat (Production : Type) where
  inspections : Nat
  published : Option Production
  live : Bool

def freshSeat {Production : Type} : ConsumerSeat Production :=
  ⟨0, none, true⟩

def applySeat {Production : Type} (earned : Production) :
    ConsumerAct → ConsumerSeat Production → ConsumerSeat Production
  | .inspect, seat =>
      if seat.live then { seat with inspections := seat.inspections + 1 } else seat
  | .publish, seat =>
      if seat.live && seat.published.isNone then
        { seat with published := some earned }
      else
        seat
  | .retire, seat => { seat with live := false }

def committedSeat {Production : Type} (seat : ConsumerSeat Production) : List Unit :=
  match seat.published with
  | none => []
  | some _ => [()]

def publishAct {Production : Type} (earned : Production) :
    Unit → List Production → List Production :=
  fun _token world => world ++ [earned]

theorem applySeat_grows {Production : Type} (earned : Production) (op : ConsumerAct)
    (seat : ConsumerSeat Production) :
    (committedSeat seat).IsPrefix (committedSeat (applySeat earned op seat)) := by
  cases op with
  | inspect =>
      cases hlive : seat.live <;>
        exact ⟨[], by simp [applySeat, committedSeat, hlive]⟩
  | retire =>
      exact ⟨[], by simp [applySeat, committedSeat]⟩
  | publish =>
      cases hlive : seat.live with
      | false =>
          exact ⟨[], by simp [applySeat, committedSeat, hlive]⟩
      | true =>
          cases hpub : seat.published with
          | none =>
              exact ⟨[()], by simp [applySeat, committedSeat, hlive, hpub]⟩
          | some _ =>
              exact ⟨[], by simp [applySeat, committedSeat, hlive, hpub]⟩

def consumerSystem {Production : Type} (earned : Production) :
    Retained (ConsumerSeat Production) ConsumerAct Unit where
  apply := applySeat earned
  committed := committedSeat
  grows := applySeat_grows earned

def applyInspection {Production : Type} (count : Nat) (seat : ConsumerSeat Production) :
    ConsumerSeat Production :=
  if seat.live then { seat with inspections := seat.inspections + count } else seat

theorem applyInspection_grows {Production : Type} (count : Nat)
    (seat : ConsumerSeat Production) :
    (committedSeat seat).IsPrefix (committedSeat (applyInspection count seat)) := by
  cases hlive : seat.live <;>
    exact ⟨[], by simp [applyInspection, committedSeat, hlive]⟩

theorem inspection_additive {Production : Type} (first extra : Nat)
    (seat : ConsumerSeat Production) :
    applyInspection (first + extra) seat =
      applyInspection extra (applyInspection first seat) := by
  cases hlive : seat.live <;> simp [applyInspection, hlive, Nat.add_assoc]

def inspectionSystem {Production : Type} :
    Retained (ConsumerSeat Production) Nat Unit where
  apply := applyInspection
  committed := committedSeat
  grows := applyInspection_grows

structure ConsumerTrace (Production : Type) where
  inspector : Host (ConsumerSeat Production) Unit (List Production)
  publisher : Host (ConsumerSeat Production) Unit (List Production)

def consumerTrace {Production : Type} (earned : Production) : ConsumerTrace Production :=
  let system := consumerSystem earned
  let act := publishAct earned
  let inspector0 := begin system act (freshSeat : ConsumerSeat Production) ([] : List Production)
  let inspector1 := submit system act inspector0.epoch .inspect inspector0
  let inspector2 := submit system act inspector1.epoch .inspect inspector1
  let inspector3 := cancel inspector2.epoch inspector2
  let publisher0 := begin system act (freshSeat : ConsumerSeat Production) ([] : List Production)
  let publisher1 := submit system act publisher0.epoch .publish publisher0
  ⟨inspector3, publisher1⟩

theorem halted_inspection_keeps_the_returned_residual
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (suffix : Nat) {cert : SourceCertificate}
    (issued : issueEarned history = some cert)
    (halted : isHalted target = true) :
    let accepted := resumeAccepted (endpointAccount history) cert.ledger suffix
    let repeated := resumeAccepted (endpointAccount history) cert.ledger (suffix + 1)
    resumeEarned history suffix = .accept accepted ∧
      accepted.produced = [] ∧
      accepted.delivered = earnedLedger history ∧
      accepted.account.roots = rootedCells target ∧
      cert.roots = rootedCells target ∧
      cert.halted = true ∧
      accepted.resumed = accepted.account.cut ∧
      repeated.produced = accepted.produced ∧
      repeated.resumed = accepted.resumed ∧
      repeated.delivered = accepted.delivered := by
  intro accepted repeated
  have consumed := earned_endpoint_is_consumed history suffix issued
  have haltedCert : cert.halted = true :=
    (earned_history_is_the_passive_issuer issued).2.2.2.2.2.2.1.trans halted
  have rootsCert : cert.roots = rootedCells target := by
    unfold issueEarned at issued
    split at issued
    · simp at issued
    · rename_i rows _hrows
      cases issued
      rfl
  have account : endpointAccount history =
      ⟨[(Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence),
          denote (earnedLedger history))],
        earnedLedger history, rootedCells target, requiredRights target,
        requiredRights target, none⟩ := by
    simp [endpointAccount, halted]
  have cutEq : (endpointAccount history).cut =
      [(Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence),
        denote (earnedLedger history))] := by
    rw [account]
  have packet (extra : Nat) :
      (resumeAccepted (endpointAccount history) cert.ledger extra).produced = [] ∧
        (resumeAccepted (endpointAccount history) cert.ledger extra).resumed =
          (endpointAccount history).cut ∧
        (resumeAccepted (endpointAccount history) cert.ledger extra).delivered =
          cert.ledger := by
    refine ⟨?_, ?_, rfl⟩
    · simp [resumeAccepted, cutEq]
    · simp [resumeAccepted, weightedResume, cutEq, sequence_cons, sequence_nil, mul_one]
  have deliveredLedger : cert.ledger = earnedLedger history := consumed.2.1
  have rootsAccount : accepted.account.roots = rootedCells target := by
    simp [accepted, resumeAccepted, account]
  refine ⟨consumed.1, ?_, ?_, rootsAccount, rootsCert, haltedCert, ?_, ?_, ?_, ?_⟩
  · exact (packet suffix).1
  · simpa [accepted] using ((packet suffix).2.2).trans deliveredLedger
  · exact (packet suffix).2.1
  · rw [(packet suffix).1]
    exact (packet (suffix + 1)).1
  · rw [(packet suffix).2.1]
    exact (packet (suffix + 1)).2.1
  · rw [(packet suffix).2.2]
    exact (packet (suffix + 1)).2.2

theorem returned_fuel_fifteen_inspection (suffix : Nat) :
    ∃ (target : JointMachine)
      (history : History (pathMachine jointSpec jointStart) jointStart target)
      (cert : SourceCertificate)
      (accepted : ResumedAccount),
      issueCut jointRun = some cert ∧
        issueEarned history = some cert ∧
        isHalted target = true ∧
        target.control = .halted (.value jointValue) ∧
        target.world.heap.lookup jointLeftCell = some (jointValued 3) ∧
        target.world.heap.lookup jointRightCell = some (jointValued 4) ∧
        resumeEarned history suffix = .accept accepted ∧
        accepted.produced = [] ∧
        accepted.delivered = jointProductionLedger ∧
        accepted.resumed = accepted.account.cut ∧
        cert.ledger = jointProductionLedger ∧
        cert.payment = 4 ∧
        cert.roots = [jointLeftCell, jointRightCell] ∧
        denote cert.ledger = 4 ∧
        cert.ledger ≠ jointReversedLedger := by
  rcases joint_returned_source_account with
    ⟨leaf, runEq, _isLeft, payEq, traceLeaf, _path, haltedLeaf, controlLeaf,
      leftLookup, rightLookup, history, indicesEq, productionEq, _valid, denoted, _recorded⟩
  have cutLeaf : issueCut jointRun = issueLeaf leaf := by
    simp [issueCut, runEq]
  have ledgerMapped : (issueCut jointRun).map SourceCertificate.ledger =
      some jointProductionLedger := by
    obtain ⟨_b0, _b3, _b6, _b11, b15, _p0, _p3, _led6, _pay6, _led11, led15,
        _pay15, _ctrl15, _split⟩ := source_budgets_issue_the_reached_slices
    simpa [b15] using led15
  have leafSome : ∃ cert, issueLeaf leaf = some cert := by
    cases hleaf : issueLeaf leaf with
    | none =>
        simp [cutLeaf, hleaf] at ledgerMapped
    | some cert => exact ⟨cert, rfl⟩
  obtain ⟨cert, leafIssued⟩ := leafSome
  have cutIssued : issueCut jointRun = some cert := by
    simpa [cutLeaf] using leafIssued
  obtain ⟨ledger, _rows, ledgerEq, _payLeaf, _rowsEq, certEq⟩ :=
    issueLeaf_exposes_the_earned_leaf leafIssued
  have certLedger : cert.ledger = ledger := by
    rw [certEq]
  have certProduction : cert.ledger = jointProductionLedger := by
    have mapped := ledgerMapped
    rw [cutIssued] at mapped
    exact Option.some.inj mapped
  have earnedEq : earnedLedger history = jointProductionLedger := by
    simpa [earnedLedger] using productionEq
  have historyLedger : earnedLedger history =
      (readGraph (retained leaf.1).state.world.receipts.nodes).factors :=
    earnedEq.trans (certProduction.symm.trans certLedger) |>.trans ledgerEq
  have historyTrace : (retained leaf.1).trace = earnedTrace history := by
    rw [traceLeaf, earnedTrace, indicesEq]
  have targetEq : (retained leaf.1).state = (retained leaf.1).state := rfl
  have issuedHistory : issueEarned history = some cert :=
    issueEarned_matches_issueLeaf history targetEq historyTrace historyLedger leafIssued
  have haltedTarget : isHalted (retained leaf.1).state = true := haltedLeaf
  have inspected :=
    halted_inspection_keeps_the_returned_residual history suffix issuedHistory haltedTarget
  let accepted := resumeAccepted (endpointAccount history) cert.ledger suffix
  have rootsList : cert.roots = [jointLeftCell, jointRightCell] := by
    have rootsTarget : rootedCells (retained leaf.1).state =
        [jointLeftCell, jointRightCell] := by
      simp [rootedCells, outcomeRoots, controlLeaf]
      exact joint_live_roots_keep_both_cells.1
    exact inspected.2.2.2.2.1.trans rootsTarget
  have payFour : cert.payment = 4 := by
    have payDenote : cert.payment = denote cert.ledger :=
      (earned_endpoint_is_consumed history suffix issuedHistory).2.2.1
    rw [payDenote, certProduction, denoted, payEq]
  refine ⟨(retained leaf.1).state, history, cert, accepted, cutIssued, issuedHistory,
    haltedTarget, controlLeaf, leftLookup, rightLookup, inspected.1, inspected.2.1, ?_,
    inspected.2.2.2.2.2.2.1, certProduction, payFour, rootsList, ?_, ?_⟩
  · exact inspected.2.2.1.trans earnedEq
  · rw [certProduction, denoted, payEq]
  · rw [certProduction]
    exact (joint_source_order_is_not_the_reversed_sidecar.2.2.1).symm

theorem inspection_budgets_slice_without_a_factor
    {Production : Type} (earned : Production) (first extra : Nat) :
    let system := inspectionSystem (Production := Production)
    let act := publishAct earned
    let host := begin system act (freshSeat : ConsumerSeat Production) ([] : List Production)
    let sliced := submit system act (host.epoch + 1) extra
      (submit system act host.epoch first host)
    let whole := submit system act host.epoch (first + extra) host
    sliced.retained = whole.retained ∧
      sliced.world = whole.world ∧
      sliced.delivered = whole.delivered ∧
      sliced.epoch = whole.epoch + 1 ∧
      whole.delivered = [] ∧
      whole.world = [] := by
  intro system act host sliced whole
  have additive : ∀ count extraCount state,
      system.apply (count + extraCount) state =
        system.apply extraCount (system.apply count state) :=
    fun count extraCount state => inspection_additive count extraCount state
  have retained : host.retained = some freshSeat := by
    simp [host, begin, freshSeat]
  have added := submit_add system act additive retained first extra
  have startEmpty : system.committed freshSeat = ([] : List Unit) := by
    simp [system, inspectionSystem, committedSeat, freshSeat]
  have nextEmpty : system.committed (system.apply (first + extra) freshSeat) = [] := by
    simp [system, inspectionSystem, applyInspection, committedSeat, freshSeat]
  have wholeEq := submit_current system act (first + extra) retained
  refine ⟨added.1, added.2.1, added.2.2.1, added.2.2.2, ?_, ?_⟩
  · simp [whole, wholeEq, startEmpty, nextEmpty, host, begin, List.length_nil,
      List.append_nil]
  · simp [whole, wholeEq, startEmpty, nextEmpty, host, begin,
      OwnedPullDriver.interpret_nil, List.length_nil]

theorem repeated_snapshot_is_not_publication {Production : Type} (earned : Production) :
    let system := consumerSystem earned
    let act := publishAct earned
    let host := begin system act (freshSeat : ConsumerSeat Production) ([] : List Production)
    host.snapshot = some freshSeat ∧
      host.delivered = [] ∧
      host.epoch = 0 ∧
      cancel (1 : Nat) host = host ∧
      submit system act 1 .publish host = host ∧
      (system.apply .publish freshSeat).published = some earned ∧
      (match host.retained with
        | some seat => seat.published
        | none => some earned) = none := by
  intro system act host
  have retained : host.retained = some freshSeat := by
    simp [host, begin]
  refine ⟨retained, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [host, begin, system, consumerSystem, committedSeat, freshSeat]
  · simp [host, begin]
  · exact cancel_stale (by decide : (1 : Nat) ≠ 0)
  · exact submit_stale system act .publish (by decide : (1 : Nat) ≠ 0)
  · simp [system, consumerSystem, applySeat, freshSeat]
  · simp [retained, freshSeat]

theorem publication_delivers_once {Production : Type} (earned : Production) :
    let system := consumerSystem earned
    let act := publishAct earned
    let host := begin system act (freshSeat : ConsumerSeat Production) ([] : List Production)
    let once := submit system act host.epoch .publish host
    let again := submit system act once.epoch .publish once
    once.delivered = [()] ∧
      once.world = [earned] ∧
      once.retained = some (⟨0, some earned, true⟩ : ConsumerSeat Production) ∧
      submit system act host.epoch .publish once = once ∧
      again.delivered = once.delivered ∧
      again.world = once.world ∧
      again.retained = once.retained := by
  intro system act host once again
  have retained : host.retained = some (freshSeat : ConsumerSeat Production) := by
    simp [host, begin]
  have onceEq := submit_current system act .publish retained
  have applied : system.apply .publish (freshSeat : ConsumerSeat Production) =
      (⟨0, some earned, true⟩ : ConsumerSeat Production) := by
    simp [system, consumerSystem, applySeat, freshSeat]
  have committedStart : system.committed (freshSeat : ConsumerSeat Production) =
      ([] : List Unit) := by
    simp [system, consumerSystem, committedSeat, freshSeat]
  have committedPublished :
      system.committed (⟨0, some earned, true⟩ : ConsumerSeat Production) = [()] := by
    simp [system, consumerSystem, committedSeat]
  have hostEpoch : host.epoch = 0 := by
    simp [host, begin]
  have hostWorld : host.world = ([] : List Production) := by
    simp [host, begin, committedStart, OwnedPullDriver.interpret_nil]
  have hostDelivered : host.delivered = ([] : List Unit) := by
    simp [host, begin, committedStart]
  have onceSimp : once =
      (⟨1, some (⟨0, some earned, true⟩ : ConsumerSeat Production), [earned], [()]⟩ :
        Host (ConsumerSeat Production) Unit (List Production)) := by
    simp only [once]
    rw [onceEq, applied, committedStart, committedPublished, hostEpoch, hostWorld, hostDelivered]
    simp [act, publishAct, OwnedPullDriver.interpret_cons, OwnedPullDriver.interpret_nil,
      List.length_nil, List.nil_append]
  have copied : submit system act host.epoch .publish once = once := by
    have epochOnce : once.epoch = 1 := by
      rw [onceSimp]
    have stale : host.epoch ≠ once.epoch := by
      rw [hostEpoch, epochOnce]
      decide
    exact submit_stale system act .publish stale
  have againRetained : once.retained =
      some (⟨0, some earned, true⟩ : ConsumerSeat Production) := by
    rw [onceSimp]
  have againEq := submit_current system act .publish againRetained
  have appliedAgain :
      system.apply .publish (⟨0, some earned, true⟩ : ConsumerSeat Production) =
        (⟨0, some earned, true⟩ : ConsumerSeat Production) := by
    simp [system, consumerSystem, applySeat]
  have committedAgain :
      system.committed (⟨0, some earned, true⟩ : ConsumerSeat Production) = [()] := by
    simp [system, consumerSystem, committedSeat]
  have againSimp : again =
      (⟨2, some (⟨0, some earned, true⟩ : ConsumerSeat Production), [earned], [()]⟩ :
        Host (ConsumerSeat Production) Unit (List Production)) := by
    simp only [again]
    rw [againEq, appliedAgain, committedAgain, onceSimp]
    simp [OwnedPullDriver.interpret_nil, List.append_nil]
  refine ⟨?_, ?_, ?_, copied, ?_, ?_, ?_⟩
  · simp [onceSimp]
  · simp [onceSimp]
  · simp [onceSimp]
  · simp [againSimp, onceSimp]
  · simp [againSimp, onceSimp]
  · simp [againSimp, onceSimp]

theorem ordered_ledgers_refuse_the_commutative_join :
    ¬ (∀ world : List JointLedger,
        publishAct jointProductionLedger () (publishAct jointReversedLedger () world) =
          publishAct jointReversedLedger () (publishAct jointProductionLedger () world)) ∧
      denote jointProductionLedger = denote jointReversedLedger ∧
      jointProductionLedger ≠ jointReversedLedger := by
  refine ⟨?_, (joint_source_order_is_not_the_reversed_sidecar.2.2.2.1).symm,
    (joint_source_order_is_not_the_reversed_sidecar.2.2.1).symm⟩
  intro commutes
  have same := commutes ([] : List JointLedger)
  simp [publishAct] at same
  exact joint_source_order_is_not_the_reversed_sidecar.2.2.1 same.1

theorem inspector_cancels_and_publisher_uses_once {Production : Type}
    (earned : Production) :
    let trace := consumerTrace earned
    trace.inspector.retained = none ∧
      trace.inspector.delivered = ([] : List Unit) ∧
      trace.inspector.world = ([] : List Production) ∧
      trace.inspector.epoch = 3 ∧
      trace.publisher.delivered = [()] ∧
      trace.publisher.world = [earned] ∧
      trace.publisher.retained =
        some (⟨0, some earned, true⟩ : ConsumerSeat Production) ∧
      submit (consumerSystem earned) (publishAct earned) 0 .publish trace.publisher =
        trace.publisher ∧
      (submit (consumerSystem earned) (publishAct earned) trace.publisher.epoch
        .publish trace.publisher).delivered = trace.publisher.delivered ∧
      (submit (consumerSystem earned) (publishAct earned) trace.publisher.epoch
        .publish trace.publisher).world = trace.publisher.world := by
  intro trace
  have once := publication_delivers_once earned
  let system := consumerSystem earned
  let act := publishAct earned
  let origin : List Production := []
  let start : ConsumerSeat Production := freshSeat
  let inspector0 := begin system act start origin
  let inspector1 := submit system act inspector0.epoch ConsumerAct.inspect inspector0
  let inspector2 := submit system act inspector1.epoch ConsumerAct.inspect inspector1
  let inspector3 := cancel inspector2.epoch inspector2
  let publisher0 := begin system act start origin
  let publisher1 := submit system act publisher0.epoch ConsumerAct.publish publisher0
  have sameInspector : trace.inspector = inspector3 := by
    simp [trace, consumerTrace, inspector3, inspector2, inspector1, inspector0, system, act,
      start, origin]
  have samePublisher : trace.publisher = publisher1 := by
    simp [trace, consumerTrace, publisher1, publisher0, system, act, start, origin]
  have retained0 : inspector0.retained = some start := by
    simp [inspector0, begin]
  have epoch0 : inspector0.epoch = 0 := by
    simp [inspector0, begin]
  have world0 : inspector0.world = origin := by
    simp [inspector0, begin, system, consumerSystem, committedSeat, start, freshSeat,
      OwnedPullDriver.interpret_nil]
  have delivered0 : inspector0.delivered = ([] : List Unit) := by
    simp [inspector0, begin, system, consumerSystem, committedSeat, start, freshSeat]
  have committedStart : system.committed start = ([] : List Unit) := by
    simp [system, consumerSystem, committedSeat, start, freshSeat]
  have appliedFirst : system.apply ConsumerAct.inspect start =
      (⟨1, none, true⟩ : ConsumerSeat Production) := by
    simp [system, consumerSystem, applySeat, start, freshSeat]
  have committedAfter : system.committed (⟨1, none, true⟩ : ConsumerSeat Production) =
      ([] : List Unit) := by
    simp [system, consumerSystem, committedSeat]
  have firstEq := submit_current system act ConsumerAct.inspect retained0
  have firstSimp : inspector1 =
      (⟨1, some (⟨1, none, true⟩ : ConsumerSeat Production), origin, ([] : List Unit)⟩ :
        Host (ConsumerSeat Production) Unit (List Production)) := by
    simp only [inspector1]
    rw [firstEq, appliedFirst, committedStart, committedAfter, epoch0, world0, delivered0]
    simp [OwnedPullDriver.interpret_nil, List.length_nil, List.append_nil]
  have retained1 : inspector1.retained =
      some (⟨1, none, true⟩ : ConsumerSeat Production) := by
    rw [firstSimp]
  have appliedSecond :
      system.apply ConsumerAct.inspect (⟨1, none, true⟩ : ConsumerSeat Production) =
        (⟨2, none, true⟩ : ConsumerSeat Production) := by
    simp [system, consumerSystem, applySeat]
  have committedSecond :
      system.committed (⟨2, none, true⟩ : ConsumerSeat Production) = ([] : List Unit) := by
    simp [system, consumerSystem, committedSeat]
  have secondEq := submit_current system act ConsumerAct.inspect retained1
  have secondSimp : inspector2 =
      (⟨2, some (⟨2, none, true⟩ : ConsumerSeat Production), origin, ([] : List Unit)⟩ :
        Host (ConsumerSeat Production) Unit (List Production)) := by
    simp only [inspector2]
    rw [secondEq, firstSimp, appliedSecond, committedAfter, committedSecond]
    simp [OwnedPullDriver.interpret_nil, List.length_nil, List.append_nil]
  have retained2 : inspector2.retained =
      some (⟨2, none, true⟩ : ConsumerSeat Production) := by
    rw [secondSimp]
  have retiredSimp : inspector3 =
      (⟨3, none, origin, ([] : List Unit)⟩ :
        Host (ConsumerSeat Production) Unit (List Production)) := by
    simp only [inspector3]
    rw [cancel_current retained2, secondSimp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sameInspector, retiredSimp]
  · simp [sameInspector, retiredSimp]
  · simp [sameInspector, retiredSimp, origin]
  · simp [sameInspector, retiredSimp]
  · simpa [samePublisher, publisher1, publisher0, system, act, origin, start] using once.1
  · simpa [samePublisher, publisher1, publisher0, system, act, origin, start] using once.2.1
  · simpa [samePublisher, publisher1, publisher0, system, act, origin, start] using once.2.2.1
  · have epochPub : publisher0.epoch = 0 := by
      simp [publisher0, begin]
    simpa [samePublisher, publisher1, publisher0, system, act, origin, start, epochPub] using
      once.2.2.2.1
  · simpa [samePublisher, publisher1, publisher0, system, act, origin, start] using
      once.2.2.2.2.1
  · simpa [samePublisher, publisher1, publisher0, system, act, origin, start] using
      once.2.2.2.2.2.1

theorem one_publisher_shares_the_ordered_ledger {Production : Type} (earned : Production) :
    let trace := consumerTrace earned
    ∃ (log : List (Unit ⊕ Unit)),
      log.filterMap Sum.getLeft? = trace.inspector.delivered ∧
        log.filterMap Sum.getRight? = trace.publisher.delivered ∧
        interpret (Sum.elim (publishAct earned) (publishAct earned)) log
          ([] : List Production) = [earned] := by
  intro trace
  have spec := inspector_cancels_and_publisher_uses_once earned
  let system := consumerSystem earned
  let act := publishAct earned
  let origin : List Production := []
  let start : ConsumerSeat Production := freshSeat
  let inspector0 := begin system act start origin
  let inspector1 := submit system act inspector0.epoch ConsumerAct.inspect inspector0
  let inspector2 := submit system act inspector1.epoch ConsumerAct.inspect inspector1
  let inspector3 := cancel inspector2.epoch inspector2
  let publisher0 := begin system act start origin
  let publisher1 := submit system act publisher0.epoch ConsumerAct.publish publisher0
  have reachedInspector : Reached system act origin start inspector3 :=
    Reached.cancel inspector2.epoch
      (Reached.submit inspector1.epoch ConsumerAct.inspect
        (Reached.submit inspector0.epoch ConsumerAct.inspect Reached.begin))
  have reachedPublisher : Reached system act origin start publisher1 :=
    Reached.submit publisher0.epoch ConsumerAct.publish Reached.begin
  have sameInspector : trace.inspector = inspector3 := by
    simp [trace, consumerTrace, inspector3, inspector2, inspector1, inspector0, system, act,
      origin, start]
  have samePublisher : trace.publisher = publisher1 := by
    simp [trace, consumerTrace, publisher1, publisher0, system, act, origin, start]
  have leftLog : ([Sum.inr ()] : List (Unit ⊕ Unit)).filterMap Sum.getLeft? =
      trace.inspector.delivered := by
    have empty : trace.inspector.delivered = ([] : List Unit) := spec.2.1
    simp [empty]
  have rightLog : ([Sum.inr ()] : List (Unit ⊕ Unit)).filterMap Sum.getRight? =
      trace.publisher.delivered := by
    have one : trace.publisher.delivered = [()] := spec.2.2.2.2.1
    simp [one]
  have cross : ∀ left right world,
      act left (act right world) = act right (act left world) := by
    intro _left _right world
    rfl
  have shared := shared_world reachedInspector reachedPublisher cross
    ([Sum.inr ()] : List (Unit ⊕ Unit)) leftLog rightLog
  refine ⟨[Sum.inr ()], leftLog, rightLog, ?_⟩
  have deliveredR : publisher1.delivered = [()] := by
    rw [← samePublisher]
    exact spec.2.2.2.2.1
  have worldL : inspector3.world = ([] : List Production) := by
    rw [← sameInspector]
    exact spec.2.2.1
  rw [shared]
  simp [deliveredR, worldL, act, publishAct, OwnedPullDriver.interpret_cons,
    OwnedPullDriver.interpret_nil]

theorem joint_consumers_keep_source_order :
    (consumerTrace jointProductionLedger).publisher.world = [jointProductionLedger] ∧
      (consumerTrace jointProductionLedger).inspector.retained = none ∧
      (consumerTrace jointProductionLedger).inspector.delivered = [] ∧
      (consumerTrace jointReversedLedger).publisher.world = [jointReversedLedger] ∧
      (consumerTrace jointProductionLedger).publisher.world ≠
        (consumerTrace jointReversedLedger).publisher.world ∧
      denote jointProductionLedger = denote jointReversedLedger := by
  have source := inspector_cancels_and_publisher_uses_once jointProductionLedger
  have reversed := inspector_cancels_and_publisher_uses_once jointReversedLedger
  refine ⟨source.2.2.2.2.2.1, source.1, source.2.1, reversed.2.2.2.2.2.1, ?_,
    joint_source_order_is_not_the_reversed_sidecar.2.2.2.1.symm⟩
  rw [source.2.2.2.2.2.1, reversed.2.2.2.2.2.1]
  intro same
  injection same with ledgers
  exact (joint_source_order_is_not_the_reversed_sidecar.2.2.1).symm ledgers

theorem payload_consumers_keep_source_order :
    ∃ (earned reversed : PayloadSemanticLedger),
      earned = leftSemanticLedger ++ rightSemanticLedger ∧
        reversed = rightSemanticLedger ++ leftSemanticLedger ∧
        denote leftSemanticLedger = 2 ∧
        denote rightSemanticLedger = 2 ∧
        denote earned = 4 ∧
        denote reversed = 4 ∧
        earned ≠ reversed ∧
        (consumerTrace earned).publisher.world = [earned] ∧
        (consumerTrace earned).inspector.retained = none ∧
        (consumerTrace earned).inspector.delivered = [] ∧
        (consumerTrace reversed).publisher.world = [reversed] ∧
        (consumerTrace earned).publisher.world ≠
          (consumerTrace reversed).publisher.world := by
  rcases left_semantic_ledger_is_the_production_payment with
    ⟨_leftLeaf, _leftMem, _leftHistory, _leftOccurrence, _leftIndices, _leftProduction,
      _leftValid, denoteLeft, paidLeft, _leftRest⟩
  rcases right_semantic_ledger_is_the_production_payment with
    ⟨_rightLeaf, _rightMem, _rightHistory, _rightOccurrence, _rightIndices, _rightProduction,
      denoteRight, paidRight, _rightFactor, _rightEntry, _rightCoefficient, _rightReceipt,
      _rightTrace, _rightLength, _different⟩
  have leftTwo : denote leftSemanticLedger = 2 := denoteLeft.trans paidLeft
  have rightTwo : denote rightSemanticLedger = 2 := denoteRight.trans paidRight
  let earned := leftSemanticLedger ++ rightSemanticLedger
  let reversed := rightSemanticLedger ++ leftSemanticLedger
  have denoteEarned : denote earned = 4 := by
    simp [earned, denote_append, leftTwo, rightTwo]
  have denoteReversed : denote reversed = 4 := by
    simp [reversed, denote_append, rightTwo, leftTwo]
  have differentLedgers : earned ≠ reversed := by
    simp [earned, reversed, leftSemanticLedger, rightSemanticLedger]
  have source := inspector_cancels_and_publisher_uses_once earned
  have other := inspector_cancels_and_publisher_uses_once reversed
  refine ⟨earned, reversed, rfl, rfl, leftTwo, rightTwo, denoteEarned, denoteReversed,
    differentLedgers, source.2.2.2.2.2.1, source.1, source.2.1, other.2.2.2.2.2.1, ?_⟩
  rw [source.2.2.2.2.2.1, other.2.2.2.2.2.1]
  intro same
  injection same with ledgers
  exact differentLedgers ledgers

theorem returned_inspection_refuses_forged_authority (suffix : Nat) :
    ∃ (target : JointMachine)
      (history : History (pathMachine jointSpec jointStart) jointStart target)
      (cert : SourceCertificate),
      issueEarned history = some cert ∧
        consumeAuthenticated history
          ⟨mapOccurrence (withLineage 0) jointRun, cert.ledger, cert.roots,
            cert.rights, cert.rights, none⟩ suffix =
          .reject .staleWorld
            ⟨⟨mapOccurrence (withLineage 0) jointRun, cert.ledger, cert.roots,
                cert.rights, cert.rights, none⟩,
              cert.ledger, [], mapOccurrence (withLineage 0) jointRun⟩ ∧
        consumeAuthenticated history
          ⟨mapPayment 9 jointRun, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩
          suffix =
          .reject .incoherentResidual
            ⟨⟨mapPayment 9 jointRun, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩,
              cert.ledger, [], mapPayment 9 jointRun⟩ ∧
        consumeAuthenticated history
          ⟨jointRun, cert.ledger, cert.roots, cert.rights, cert.rights,
            some (jointOwnerClaim 1)⟩ suffix =
          .reject .incoherentResidual
            ⟨⟨jointRun, cert.ledger, cert.roots, cert.rights, cert.rights,
                some (jointOwnerClaim 1)⟩,
              cert.ledger, [], jointRun⟩ ∧
        consumeAuthenticated history
          ⟨jointRun, cert.ledger, [], cert.rights, cert.rights, none⟩ suffix =
          .reject .incompleteResidual
            ⟨⟨jointRun, cert.ledger, [], cert.rights, cert.rights, none⟩,
              cert.ledger, [], jointRun⟩ ∧
        consumeAuthenticated history
          ⟨jointRun, jointReversedLedger, cert.roots, cert.rights, cert.rights, none⟩
          suffix =
          .reject .incoherentResidual
            ⟨⟨jointRun, jointReversedLedger, cert.roots, cert.rights, cert.rights, none⟩,
              jointReversedLedger, [], jointRun⟩ ∧
        consumeAuthenticated history
          ⟨jointErasedRun, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩
          suffix =
          .reject .changedDependency
            ⟨⟨jointErasedRun, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩,
              cert.ledger, [], jointErasedRun⟩ := by
  obtain ⟨target, history, cert, _accepted, cutIssued, issuedHistory, _halted, _control,
      _left, _right, _resume, _produced, _delivered, _resumed, _ledger, _payment, _roots,
      _denote, _order⟩ := returned_fuel_fifteen_inspection suffix
  have staleRaw :
      (issueCut jointRun).bind (fun issuedCert =>
        some (admitIssued issuedCert ⟨mapOccurrence (withLineage 0) jointRun,
          issuedCert.ledger, issuedCert.roots, issuedCert.rights, issuedCert.rights,
          none⟩)) =
      (issueCut jointRun).bind (fun issuedCert =>
        some (.reject .staleWorld ⟨mapOccurrence (withLineage 0) jointRun,
          issuedCert.ledger, issuedCert.roots, issuedCert.rights, issuedCert.rights,
          none⟩)) := by
    rfl
  have copiedRaw :
      (issueCut jointRun).bind (fun issuedCert =>
        some (admitIssued issuedCert ⟨mapPayment 9 jointRun, issuedCert.ledger,
          issuedCert.roots, issuedCert.rights, issuedCert.rights, none⟩)) =
      (issueCut jointRun).bind (fun issuedCert =>
        some (.reject .incoherentResidual ⟨mapPayment 9 jointRun, issuedCert.ledger,
          issuedCert.roots, issuedCert.rights, issuedCert.rights, none⟩)) := by
    rfl
  have ownerRaw :
      (issueCut jointRun).bind (fun issuedCert =>
        some (admitIssued issuedCert ⟨jointRun, issuedCert.ledger, issuedCert.roots,
          issuedCert.rights, issuedCert.rights, some (jointOwnerClaim 1)⟩)) =
      (issueCut jointRun).bind (fun issuedCert =>
        some (.reject .incoherentResidual ⟨jointRun, issuedCert.ledger, issuedCert.roots,
          issuedCert.rights, issuedCert.rights, some (jointOwnerClaim 1)⟩)) := by
    rfl
  have rootRaw :
      (issueCut jointRun).bind (fun issuedCert =>
        some (admitIssued issuedCert ⟨jointRun, issuedCert.ledger, [],
          issuedCert.rights, issuedCert.rights, none⟩)) =
      (issueCut jointRun).bind (fun issuedCert =>
        some (.reject .incompleteResidual ⟨jointRun, issuedCert.ledger, [],
          issuedCert.rights, issuedCert.rights, none⟩)) := by
    rfl
  have ledgerRaw :
      (issueCut jointRun).bind (fun issuedCert =>
        some (admitIssued issuedCert ⟨jointRun, jointReversedLedger, issuedCert.roots,
          issuedCert.rights, issuedCert.rights, none⟩)) =
      (issueCut jointRun).bind (fun issuedCert =>
        some (.reject .incoherentResidual ⟨jointRun, jointReversedLedger, issuedCert.roots,
          issuedCert.rights, issuedCert.rights, none⟩)) := by
    rfl
  have erasedRaw :
      (issueCut jointRun).bind (fun issuedCert =>
        some (admitIssued issuedCert ⟨jointErasedRun, issuedCert.ledger, issuedCert.roots,
          issuedCert.rights, issuedCert.rights, none⟩)) =
      (issueCut jointRun).bind (fun issuedCert =>
        some (.reject .changedDependency ⟨jointErasedRun, issuedCert.ledger,
          issuedCert.roots, issuedCert.rights, issuedCert.rights, none⟩)) := by
    rfl
  rw [cutIssued] at staleRaw copiedRaw ownerRaw rootRaw ledgerRaw erasedRaw
  refine ⟨target, history, cert, issuedHistory, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact issued_refusal_does_not_resume history
      ⟨mapOccurrence (withLineage 0) jointRun, cert.ledger, cert.roots, cert.rights,
        cert.rights, none⟩ suffix issuedHistory (Option.some.inj staleRaw)
  · exact issued_refusal_does_not_resume history
      ⟨mapPayment 9 jointRun, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩
      suffix issuedHistory (Option.some.inj copiedRaw)
  · exact issued_refusal_does_not_resume history
      ⟨jointRun, cert.ledger, cert.roots, cert.rights, cert.rights,
        some (jointOwnerClaim 1)⟩ suffix issuedHistory (Option.some.inj ownerRaw)
  · exact issued_refusal_does_not_resume history
      ⟨jointRun, cert.ledger, [], cert.rights, cert.rights, none⟩ suffix issuedHistory
      (Option.some.inj rootRaw)
  · exact issued_refusal_does_not_resume history
      ⟨jointRun, jointReversedLedger, cert.roots, cert.rights, cert.rights, none⟩
      suffix issuedHistory (Option.some.inj ledgerRaw)
  · exact issued_refusal_does_not_resume history
      ⟨jointErasedRun, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩
      suffix issuedHistory (Option.some.inj erasedRaw)

theorem retiring_one_consumer_keeps_shared_production (suffix : Nat) :
    ∃ (target : JointMachine)
      (history : History (pathMachine jointSpec jointStart) jointStart target)
      (cert : SourceCertificate)
      (accepted : ResumedAccount),
      issueCut jointRun = some cert ∧
        issueEarned history = some cert ∧
        resumeEarned history suffix = .accept accepted ∧
        accepted.produced = [] ∧
        accepted.delivered = cert.ledger ∧
        cert.ledger = jointProductionLedger ∧
        cert.payment = denote cert.ledger ∧
        cert.roots = [jointLeftCell, jointRightCell] ∧
        (consumerTrace cert.ledger).publisher.world = [cert.ledger] ∧
        (consumerTrace cert.ledger).publisher.delivered = [()] ∧
        (consumerTrace cert.ledger).inspector.retained = none ∧
        (consumerTrace cert.ledger).inspector.delivered = [] ∧
        submit (consumerSystem cert.ledger) (publishAct cert.ledger) 0 .publish
          (consumerTrace cert.ledger).publisher =
          (consumerTrace cert.ledger).publisher ∧
        unread (cancelConsumer (consumersOf jointValue) 0).log 0 = [] ∧
        unread (cancelConsumer (consumersOf jointValue) 0).log 1 = cert.roots ∧
        (issueCut jointRun).bind (fun issued =>
          match issued.handles with
          | [left, right] =>
              match releaseJoint issued.registry left with
              | (some (next, cleared), visits) =>
                  some (visits, cleared.store, cleared.row.token, next.identity,
                    (lookupJoint next right).1, (lookupJoint next left).1,
                    decide (left.row ∉ next.rows), decide (right.row ∈ next.rows),
                    decide (issued.registry.rows.Nodup), issued.payment,
                    decide (issued.ledger = jointProductionLedger),
                    denote issued.ledger)
              | (none, _) => none
          | _ => none) = some (1, 0, 0, 2, some 0, none, true, true, true, 4, true, 4) ∧
        (issueCut jointRun).bind (fun issued =>
          match issued.handles with
          | [left, right] =>
              some ((releaseJoint issued.registry { right with store := 0 }).1.isNone,
                (releaseJoint issued.registry { right with store := 0 }).2,
                (releaseJoint issued.registry { right with row.token := 0 }).1.isNone,
                (releaseJoint issued.registry { right with row.token := 0 }).2,
                (releaseJoint issued.registry
                  { right with row.provider := left.row.provider }).1.isNone,
                (releaseJoint issued.registry
                  { right with row.provider := left.row.provider }).2,
                (lookupJoint issued.registry left).1,
                (lookupJoint issued.registry right).1)
          | _ => none) = some (true, 0, true, 0, true, 2, some 0, some 1) := by
  obtain ⟨target, history, cert, accepted, cutIssued, issuedHistory, _halted, _control,
      _left, _right, resumed, produced, delivered, _same, ledgerEq, payment, roots,
      denoteEq, _order⟩ := returned_fuel_fifteen_inspection suffix
  have trace := inspector_cancels_and_publisher_uses_once cert.ledger
  have payDenote : cert.payment = denote cert.ledger := by
    rw [payment, denoteEq]
  have release := retiring_one_owner_keeps_the_other
  have body :
      issueCut jointRun = some cert ∧
        issueEarned history = some cert ∧
        resumeEarned history suffix = .accept accepted ∧
        accepted.produced = [] ∧
        accepted.delivered = cert.ledger ∧
        cert.ledger = jointProductionLedger ∧
        cert.payment = denote cert.ledger ∧
        cert.roots = [jointLeftCell, jointRightCell] ∧
        (consumerTrace cert.ledger).publisher.world = [cert.ledger] ∧
        (consumerTrace cert.ledger).publisher.delivered = [()] ∧
        (consumerTrace cert.ledger).inspector.retained = none ∧
        (consumerTrace cert.ledger).inspector.delivered = [] ∧
        submit (consumerSystem cert.ledger) (publishAct cert.ledger) 0 .publish
          (consumerTrace cert.ledger).publisher =
          (consumerTrace cert.ledger).publisher ∧
        unread (cancelConsumer (consumersOf jointValue) 0).log 0 = [] ∧
        unread (cancelConsumer (consumersOf jointValue) 0).log 1 = cert.roots ∧
        (issueCut jointRun).bind (fun issued =>
          match issued.handles with
          | [left, right] =>
              match releaseJoint issued.registry left with
              | (some (next, cleared), visits) =>
                  some (visits, cleared.store, cleared.row.token, next.identity,
                    (lookupJoint next right).1, (lookupJoint next left).1,
                    decide (left.row ∉ next.rows), decide (right.row ∈ next.rows),
                    decide (issued.registry.rows.Nodup), issued.payment,
                    decide (issued.ledger = jointProductionLedger),
                    denote issued.ledger)
              | (none, _) => none
          | _ => none) = some (1, 0, 0, 2, some 0, none, true, true, true, 4, true, 4) ∧
        (issueCut jointRun).bind (fun issued =>
          match issued.handles with
          | [left, right] =>
              some ((releaseJoint issued.registry { right with store := 0 }).1.isNone,
                (releaseJoint issued.registry { right with store := 0 }).2,
                (releaseJoint issued.registry { right with row.token := 0 }).1.isNone,
                (releaseJoint issued.registry { right with row.token := 0 }).2,
                (releaseJoint issued.registry
                  { right with row.provider := left.row.provider }).1.isNone,
                (releaseJoint issued.registry
                  { right with row.provider := left.row.provider }).2,
                (lookupJoint issued.registry left).1,
                (lookupJoint issued.registry right).1)
          | _ => none) = some (true, 0, true, 0, true, 2, some 0, some 1) := by
    refine ⟨cutIssued, issuedHistory, resumed, produced, delivered.trans ledgerEq.symm,
      ledgerEq, payDenote, roots, ?_, ?_, ?_, ?_, ?_, ?_, ?_, release.1, release.2.1⟩
    · simpa [ledgerEq] using trace.2.2.2.2.2.1
    · simpa [ledgerEq] using trace.2.2.2.2.1
    · simpa [ledgerEq] using trace.1
    · simpa [ledgerEq] using trace.2.1
    · simpa [ledgerEq] using trace.2.2.2.2.2.2.2.1
    · exact joint_live_roots_keep_both_cells.2.2.2.2.1
    · rw [roots]
      exact joint_live_roots_keep_both_cells.2.2.2.2.2.1
  exact ⟨target, history, cert, accepted, body⟩

/-- The account `consumeAuthenticated` returned, plus consumer hosts only
when that return was acceptance. The hosts read `resumed.delivered`. -/
structure AuthenticatedConsumers where
  resumed : ResumedAccount
  hosts : Option (ConsumerTrace JointLedger)

def authenticateConsumers {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (presented : PresentedAccount) (suffix : Nat) :
    RetainedAdmit AuthenticatedConsumers :=
  match consumeAuthenticated history presented suffix with
  | .reject reason kept => .reject reason ⟨kept, none⟩
  | .accept resumed => .accept ⟨resumed, some (consumerTrace resumed.delivered)⟩

theorem authenticateConsumers_keeps_a_refused_account
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (presented : PresentedAccount) (suffix : Nat)
    {reason : Refusal} {kept : AuthenticatedConsumers}
    (refused : authenticateConsumers history presented suffix = .reject reason kept) :
    kept.hosts = none ∧
      kept.resumed.account = presented ∧
      kept.resumed.delivered = presented.ledger ∧
      kept.resumed.produced = [] ∧
      kept.resumed.resumed = presented.cut := by
  match hconsume : consumeAuthenticated history presented suffix with
  | .reject _reason' account =>
      unfold authenticateConsumers at refused
      simp [hconsume] at refused
      obtain ⟨rfl, keptEq⟩ := refused
      have hostsNone : kept.hosts = none := by
        rw [← keptEq]
      have resumedEq : kept.resumed = account := by
        rw [← keptEq]
      have facts :=
        consume_refusal_keeps_the_submitted_account history presented suffix hconsume
      rw [← resumedEq] at facts
      exact ⟨hostsNone, facts.1, facts.2.1, facts.2.2.1, facts.2.2.2⟩
  | .accept _resumed =>
      unfold authenticateConsumers at refused
      simp [hconsume] at refused

theorem stale_lineage_enables_no_publication (suffix : Nat) :
    ∃ (target : JointMachine)
      (history : History (pathMachine jointSpec jointStart) jointStart target)
      (cert : SourceCertificate)
      (kept : AuthenticatedConsumers),
      authenticateConsumers history
          ⟨mapOccurrence (withLineage 0) jointRun, cert.ledger, cert.roots,
            cert.rights, cert.rights, none⟩ suffix =
        .reject .staleWorld kept ∧
        kept.hosts = none ∧
        kept.resumed.account =
          ⟨mapOccurrence (withLineage 0) jointRun, cert.ledger, cert.roots,
            cert.rights, cert.rights, none⟩ ∧
        kept.resumed.produced = [] ∧
        kept.resumed.resumed = mapOccurrence (withLineage 0) jointRun := by
  obtain ⟨target, history, cert, _issued, stale, _copied, _owner, _root, _ledger, _erased⟩ :=
    returned_inspection_refuses_forged_authority suffix
  let presented : PresentedAccount :=
    ⟨mapOccurrence (withLineage 0) jointRun, cert.ledger, cert.roots,
      cert.rights, cert.rights, none⟩
  have consumeEq : consumeAuthenticated history presented suffix =
      .reject .staleWorld ⟨presented, cert.ledger, [],
        mapOccurrence (withLineage 0) jointRun⟩ := by
    simpa [presented] using stale
  have refused : authenticateConsumers history presented suffix =
      .reject .staleWorld ⟨⟨presented, cert.ledger, [],
        mapOccurrence (withLineage 0) jointRun⟩, none⟩ := by
    unfold authenticateConsumers
    simp [consumeEq]
  have facts :=
    authenticateConsumers_keeps_a_refused_account history presented suffix refused
  refine ⟨target, history, cert, ⟨⟨presented, cert.ledger, [],
      mapOccurrence (withLineage 0) jointRun⟩, none⟩, refused, facts.1, ?_, facts.2.2.2.1, ?_⟩
  · rfl
  · rfl

theorem halted_boundary_serves_two_consumers (suffix : Nat) :
    ∃ (target : JointMachine)
      (history : History (pathMachine jointSpec jointStart) jointStart target)
      (cert : SourceCertificate)
      (accepted : ResumedAccount)
      (hosts : ConsumerTrace JointLedger),
      authenticateConsumers history (endpointAccount history) suffix =
        .accept ⟨accepted, some hosts⟩ ∧
        hosts = consumerTrace accepted.delivered ∧
        accepted.produced = [] ∧
        accepted.delivered = cert.ledger ∧
        accepted.resumed = accepted.account.cut ∧
        issueCut jointRun = some cert ∧
        issueEarned history = some cert ∧
        cert.ledger = jointProductionLedger ∧
        cert.payment = denote cert.ledger ∧
        hosts.inspector.retained = none ∧
        hosts.inspector.delivered = [] ∧
        hosts.inspector.world = [] ∧
        hosts.publisher.world = [cert.ledger] ∧
        hosts.publisher.delivered = [()] ∧
        submit (consumerSystem cert.ledger) (publishAct cert.ledger) 0 .publish
          hosts.publisher = hosts.publisher ∧
        (∃ (hostL hostR : Host (ConsumerSeat JointLedger) Unit (List JointLedger)),
          Reached (consumerSystem cert.ledger) (publishAct cert.ledger)
            ([] : List JointLedger) (⟨0, none, true⟩ : ConsumerSeat JointLedger) hostL ∧
            Reached (consumerSystem cert.ledger) (publishAct cert.ledger)
              ([] : List JointLedger) (⟨0, none, true⟩ : ConsumerSeat JointLedger) hostR ∧
            hostL.world = [cert.ledger] ∧
            hostR.world = [cert.ledger] ∧
            hostL.delivered = [()] ∧
            hostR.delivered = [()] ∧
            Mettapedia.Machines.OwnedPullDriver.interpret
              (Sum.elim (publishAct cert.ledger) (publishAct cert.ledger))
              [Sum.inl (), Sum.inr ()] ([] : List JointLedger) =
              [cert.ledger, cert.ledger]) ∧
        denote (cert.ledger ++ cert.ledger) =
          denote cert.ledger * denote cert.ledger ∧
        cert.payment ≠ denote (cert.ledger ++ cert.ledger) := by
  obtain ⟨target, history, cert, accepted, cutIssued, issuedHistory, _halted, _control,
      _left, _right, resumedAdmit, produced, delivered, sameCut, ledgerEq, payment, _roots,
      denoteEq, _order⟩ := returned_fuel_fifteen_inspection suffix
  have admitted : consumeAuthenticated history (endpointAccount history) suffix =
      .accept accepted := by
    simpa [resumeEarned] using resumedAdmit
  let hosts := consumerTrace accepted.delivered
  have boundaryEq : authenticateConsumers history (endpointAccount history) suffix =
      .accept ⟨accepted, some hosts⟩ := by
    unfold authenticateConsumers
    simp [admitted, hosts]
  have deliveredCert : accepted.delivered = cert.ledger :=
    delivered.trans ledgerEq.symm
  have trace := inspector_cancels_and_publisher_uses_once cert.ledger
  have payDenote : cert.payment = denote cert.ledger := by
    rw [payment, denoteEq]
  have product : denote (cert.ledger ++ cert.ledger) =
      denote cert.ledger * denote cert.ledger :=
    denote_append _ _
  have notChargedTwice : cert.payment ≠ denote (cert.ledger ++ cert.ledger) := by
    rw [payDenote, product, denoteEq]
    decide
  let system := consumerSystem cert.ledger
  let act := publishAct cert.ledger
  let origin : List JointLedger := []
  let start : ConsumerSeat JointLedger := freshSeat
  let left0 := begin system act start origin
  let left1 := submit system act left0.epoch ConsumerAct.publish left0
  let right0 := begin system act start origin
  let right1 := submit system act right0.epoch ConsumerAct.publish right0
  have reachedL : Reached system act origin start left1 :=
    Reached.submit left0.epoch ConsumerAct.publish Reached.begin
  have reachedR : Reached system act origin start right1 :=
    Reached.submit right0.epoch ConsumerAct.publish Reached.begin
  have published := publication_delivers_once cert.ledger
  have leftWorld : left1.world = [cert.ledger] := by
    simpa [left1, left0, system, act, origin, start] using published.2.1
  have rightWorld : right1.world = [cert.ledger] := by
    simpa [right1, right0, system, act, origin, start] using published.2.1
  have leftDelivered : left1.delivered = [()] := by
    simpa [left1, left0, system, act, origin, start] using published.1
  have rightDelivered : right1.delivered = [()] := by
    simpa [right1, right0, system, act, origin, start] using published.1
  have twoObservations :
      Mettapedia.Machines.OwnedPullDriver.interpret
        (Sum.elim act act) [Sum.inl (), Sum.inr ()] origin = [cert.ledger, cert.ledger] := by
    have leftTokens : ([Sum.inl (), Sum.inr ()] : List (Unit ⊕ Unit)).filterMap Sum.getLeft? =
        left1.delivered := by
      rw [leftDelivered]
      rfl
    have rightTokens : ([Sum.inl (), Sum.inr ()] : List (Unit ⊕ Unit)).filterMap Sum.getRight? =
        right1.delivered := by
      rw [rightDelivered]
      rfl
    have shared := shared_world reachedL reachedR
      (by intro _tokenL _tokenR world; simp [act, publishAct])
      [Sum.inl (), Sum.inr ()] leftTokens rightTokens
    rw [shared, rightDelivered, leftWorld]
    simp [act, publishAct, OwnedPullDriver.interpret_cons, OwnedPullDriver.interpret_nil]
  refine ⟨target, history, cert, accepted, hosts, boundaryEq, rfl, produced, deliveredCert,
    sameCut, cutIssued, issuedHistory, ledgerEq, payDenote, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨left1, right1, ?_, ?_, leftWorld, rightWorld, leftDelivered, rightDelivered,
      by simpa [act, origin] using twoObservations⟩,
    product, notChargedTwice⟩
  · simpa [hosts, deliveredCert] using trace.1
  · simpa [hosts, deliveredCert] using trace.2.1
  · simpa [hosts, deliveredCert] using trace.2.2.1
  · simpa [hosts, deliveredCert] using trace.2.2.2.2.2.1
  · simpa [hosts, deliveredCert] using trace.2.2.2.2.1
  · simpa [hosts, deliveredCert] using trace.2.2.2.2.2.2.2.1
  · simpa [system, act, origin, start, freshSeat, left1] using reachedL
  · simpa [system, act, origin, start, freshSeat, right1] using reachedR


/-!
`inspectPassive` admits an already earned account and reads its leaf before
any call to `resumeAccepted`. A completed return (`Sum.inl`) persists that
account and may begin one shared host. An original pending demand
(`Sum.inr`) persists that account and begins no host. Flattening those
leaves would drop the role. Suffix 0 reproduces the pending cut, and the
empty ledger denotes 1, so neither shows that a resume happened. Suffix 3
advances the fuel-3 cut to the fuel-6 cut.

Payment is `denote` of the one issued ledger. The ordered factor list and
a later delivery observation stay separate. The issued joint assignment
stays grade `2`. `sourceReplay` at grades `0` and `1` is the same source
trace: grade `1` is a real factor, not the empty ledger, and grade `0`
keeps that occurrence. This does not close G4, and beginning a host does
not free native storage.
-/

def configurationOfRoots (roots : List CellId) : Configuration CellId Nat 2 :=
  ⟨⟨0, roots, fun _ => some 0, false, roots.length⟩, ∅⟩

theorem consumersOf_uses_configurationOfRoots (value : Val CellId) :
    consumersOf value = configurationOfRoots (occurrencesOf value) := rfl

def updateAt {α : Type} (values : Fin 2 → α) (client : Fin 2) (value : α) :
    Fin 2 → α :=
  fun index => if index = client then value else values index

structure SharedConsumers (Production : Type) where
  seats : Fin 2 → ConsumerSeat Production
  ownership : Configuration CellId Nat 2
  registry : JointIssuedRegistry
  handles : Fin 2 → JointIssuedHandle
  deliveries : List (Fin 2)

inductive SharedAct where
  | inspect (client : Fin 2)
  | publish (client : Fin 2)
  | retire (client : Fin 2)

def applyShared {Production : Type} (earned : Production) :
    SharedAct → SharedConsumers Production → SharedConsumers Production
  | .inspect client, state =>
      { state with
          seats := updateAt state.seats client
            (applySeat earned ConsumerAct.inspect (state.seats client)) }
  | .publish client, state =>
      let seat := state.seats client
      { state with
          seats := updateAt state.seats client
            (applySeat earned ConsumerAct.publish seat)
          deliveries :=
            if seat.live && seat.published.isNone then state.deliveries ++ [client]
            else state.deliveries }
  | .retire client, state =>
      let seat := state.seats client
      let retired := applySeat earned ConsumerAct.retire seat
      let cancelled := cancelConsumer state.ownership client
      if seat.live then
        match releaseJoint state.registry (state.handles client) with
        | (some (next, cleared), _) =>
            { state with
                seats := updateAt state.seats client retired
                ownership := cancelled
                registry := next
                handles := updateAt state.handles client cleared }
        | (none, _) =>
            { state with
                seats := updateAt state.seats client retired
                ownership := cancelled }
      else
        { state with
            seats := updateAt state.seats client retired
            ownership := cancelled }

def committedShared {Production : Type} (state : SharedConsumers Production) :
    List (Fin 2) :=
  state.deliveries

theorem applyShared_grows {Production : Type} (earned : Production)
    (op : SharedAct) (state : SharedConsumers Production) :
    (committedShared state).IsPrefix (committedShared (applyShared earned op state)) := by
  cases op with
  | inspect _ =>
      exact ⟨[], by simp [applyShared, committedShared]⟩
  | publish client =>
      cases fresh : (state.seats client).live && (state.seats client).published.isNone with
      | true =>
          exact ⟨[client], by simp [applyShared, committedShared, fresh]⟩
      | false =>
          exact ⟨[], by simp [applyShared, committedShared, fresh]⟩
  | retire client =>
      cases hlive : (state.seats client).live with
      | false =>
          exact ⟨[], by simp [applyShared, committedShared, hlive]⟩
      | true =>
          cases hrel : releaseJoint state.registry (state.handles client) with
          | mk reply _visits =>
              cases reply with
              | none =>
                  exact ⟨[], by simp [applyShared, committedShared, hlive, hrel]⟩
              | some pair =>
                  cases pair with
                  | mk _next _cleared =>
                      exact ⟨[], by simp [applyShared, committedShared, hlive, hrel]⟩

def sharedSystem {Production : Type} (earned : Production) :
    Retained (SharedConsumers Production) SharedAct (Fin 2) where
  apply := applyShared earned
  committed := committedShared
  grows := applyShared_grows earned

def deliverAct {Production : Type} (earned : Production) :
    Fin 2 → List Production → List Production :=
  fun _client world => world ++ [earned]

def freshShared {Production : Type} (ownership : Configuration CellId Nat 2)
    (registry : JointIssuedRegistry) (handles : Fin 2 → JointIssuedHandle) :
    SharedConsumers Production where
  seats := fun _ => (freshSeat : ConsumerSeat Production)
  ownership := ownership
  registry := registry
  handles := handles
  deliveries := []


/-!
`SharedLaw` is the transition invariant of one shared host. Delivery
observations are the client list and the world built by appending the one
earned production once per observation. That production is not the paid
account (`denote` of the issued ledger). Retiring a live handle cancels that
seat and may release its issued row; the other live handle stays authenticated
when the start rows differ. Release does not free the earned payload.
-/

abbrev jointAuthenticated (registry : JointIssuedRegistry) (handle : JointIssuedHandle) :
    Prop :=
  Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Authenticated registry handle

structure SharedLaw {Production : Type} (earned : Production)
    (start state : SharedConsumers Production) : Prop where
  nodup : state.deliveries.Nodup
  published : ∀ client,
    (state.seats client).published =
      if client ∈ state.deliveries then some earned else none
  cursor : ∀ client,
    unread state.ownership.log client =
      if (state.seats client).live then unread start.ownership.log client else []
  liveHandle : ∀ client, (state.seats client).live = true →
    state.handles client = start.handles client
  liveAuthority : ∀ client, (state.seats client).live = true →
    (jointAuthenticated state.registry (state.handles client) ↔
      jointAuthenticated start.registry (start.handles client))

private theorem nodup_append_singleton {α : Type} {xs : List α} {x : α}
    (nodup : xs.Nodup) (absent : x ∉ xs) : (xs ++ [x]).Nodup := by
  induction xs with
  | nil => exact List.nodup_singleton x
  | cons head tail ih =>
      rw [List.cons_append]
      rw [List.nodup_cons] at nodup ⊢
      refine ⟨?_, ih nodup.2 (fun member => absent (List.mem_cons_of_mem head member))⟩
      intro member
      rw [List.mem_append, List.mem_singleton] at member
      cases member with
      | inl headInTail => exact nodup.1 headInTail
      | inr headEq =>
          apply absent
          rw [← headEq]
          exact List.mem_cons_self

private theorem inspect_keeps_publication {Production : Type} (earned : Production)
    (seat : ConsumerSeat Production) :
    (applySeat earned ConsumerAct.inspect seat).published = seat.published ∧
      (applySeat earned ConsumerAct.inspect seat).live = seat.live := by
  cases hlive : seat.live <;> simp [applySeat, hlive]

private theorem publish_keeps_live {Production : Type} (earned : Production)
    (seat : ConsumerSeat Production) :
    (applySeat earned ConsumerAct.publish seat).live = seat.live := by
  cases hlive : seat.live <;> cases hpub : seat.published <;>
    simp [applySeat, hlive, hpub]

private theorem publish_sets_publication {Production : Type} (earned : Production)
    (seat : ConsumerSeat Production) :
    (applySeat earned ConsumerAct.publish seat).published =
      if seat.live && seat.published.isNone then some earned else seat.published := by
  cases hlive : seat.live <;> cases hpub : seat.published <;>
    simp [applySeat, hlive, hpub]

private theorem retire_keeps_publication {Production : Type} (earned : Production)
    (seat : ConsumerSeat Production) :
    (applySeat earned ConsumerAct.retire seat).live = false ∧
      (applySeat earned ConsumerAct.retire seat).published = seat.published := by
  simp [applySeat]

private theorem freshShared_satisfies_law {Production : Type} (earned : Production)
    (ownership : Configuration CellId Nat 2) (registry : JointIssuedRegistry)
    (handles : Fin 2 → JointIssuedHandle) :
    SharedLaw earned (freshShared ownership registry handles)
      (freshShared ownership registry handles) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [freshShared]
  · intro client
    simp [freshShared, freshSeat]
  · intro client
    simp [freshShared, freshSeat]
  · intro _client _live
    simp [freshShared]
  · intro _client _live
    simp [freshShared]

private theorem inspect_preserves_law {Production : Type} (earned : Production)
    (start state : SharedConsumers Production) (client : Fin 2)
    (law : SharedLaw earned start state) :
    SharedLaw earned start (applyShared earned (SharedAct.inspect client) state) := by
  have deliveriesEq :
      (applyShared earned (SharedAct.inspect client) state).deliveries = state.deliveries := by
    simp [applyShared]
  have ownershipEq :
      (applyShared earned (SharedAct.inspect client) state).ownership = state.ownership := by
    simp [applyShared]
  have registryEq :
      (applyShared earned (SharedAct.inspect client) state).registry = state.registry := by
    simp [applyShared]
  have handlesEq :
      (applyShared earned (SharedAct.inspect client) state).handles = state.handles := by
    simp [applyShared]
  have seatsEq : ∀ index,
      (applyShared earned (SharedAct.inspect client) state).seats index =
        if index = client then applySeat earned ConsumerAct.inspect (state.seats client)
        else state.seats index := by
    intro index
    simp [applyShared, updateAt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [deliveriesEq] using law.nodup
  · intro index
    by_cases same : index = client
    · subst index
      have publishedEq :
          ((applyShared earned (SharedAct.inspect client) state).seats client).published =
            (state.seats client).published := by
        rw [seatsEq client, if_pos rfl, (inspect_keeps_publication earned (state.seats client)).1]
      rw [publishedEq, law.published client, deliveriesEq]
    · have publishedEq :
          ((applyShared earned (SharedAct.inspect client) state).seats index).published =
            (state.seats index).published := by
        rw [seatsEq index, if_neg same]
      rw [publishedEq, law.published index, deliveriesEq]
  · intro index
    by_cases same : index = client
    · subst index
      have liveEq :
          ((applyShared earned (SharedAct.inspect client) state).seats client).live =
            (state.seats client).live := by
        rw [seatsEq client, if_pos rfl, (inspect_keeps_publication earned (state.seats client)).2]
      rw [ownershipEq, law.cursor client, liveEq]
    · have liveEq :
          ((applyShared earned (SharedAct.inspect client) state).seats index).live =
            (state.seats index).live := by
        rw [seatsEq index, if_neg same]
      rw [ownershipEq, law.cursor index, liveEq]
  · intro index liveNext
    rw [handlesEq]
    apply law.liveHandle index
    by_cases same : index = client
    · subst index
      rw [seatsEq client, if_pos rfl,
        (inspect_keeps_publication earned (state.seats client)).2] at liveNext
      exact liveNext
    · rw [seatsEq index, if_neg same] at liveNext
      exact liveNext
  · intro index liveNext
    rw [handlesEq, registryEq]
    apply law.liveAuthority index
    by_cases same : index = client
    · subst index
      rw [seatsEq client, if_pos rfl,
        (inspect_keeps_publication earned (state.seats client)).2] at liveNext
      exact liveNext
    · rw [seatsEq index, if_neg same] at liveNext
      exact liveNext

private theorem publish_idle_preserves_law {Production : Type} (earned : Production)
    (start state : SharedConsumers Production) (client : Fin 2)
    (idle : ((state.seats client).live && (state.seats client).published.isNone) = false)
    (law : SharedLaw earned start state) :
    SharedLaw earned start (applyShared earned (SharedAct.publish client) state) := by
  have seatSame : applySeat earned ConsumerAct.publish (state.seats client) =
      state.seats client := by
    simp [applySeat, idle]
  have deliveriesEq :
      (applyShared earned (SharedAct.publish client) state).deliveries = state.deliveries := by
    simp [applyShared, idle]
  have ownershipEq :
      (applyShared earned (SharedAct.publish client) state).ownership = state.ownership := by
    simp [applyShared]
  have registryEq :
      (applyShared earned (SharedAct.publish client) state).registry = state.registry := by
    simp [applyShared]
  have handlesEq :
      (applyShared earned (SharedAct.publish client) state).handles = state.handles := by
    simp [applyShared]
  have seatsEq : ∀ index,
      (applyShared earned (SharedAct.publish client) state).seats index = state.seats index := by
    intro index
    by_cases same : index = client
    · subst index
      simp [applyShared, updateAt, seatSame]
    · simp [applyShared, updateAt, same]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [deliveriesEq] using law.nodup
  · intro index
    rw [seatsEq index, law.published index, deliveriesEq]
  · intro index
    rw [ownershipEq, seatsEq index, law.cursor index]
  · intro index liveNext
    rw [handlesEq]
    apply law.liveHandle index
    rw [seatsEq index] at liveNext
    exact liveNext
  · intro index liveNext
    rw [handlesEq, registryEq]
    apply law.liveAuthority index
    rw [seatsEq index] at liveNext
    exact liveNext

private theorem publish_once_preserves_law {Production : Type} (earned : Production)
    (start state : SharedConsumers Production) (client : Fin 2)
    (fresh : ((state.seats client).live && (state.seats client).published.isNone) = true)
    (law : SharedLaw earned start state) :
    SharedLaw earned start (applyShared earned (SharedAct.publish client) state) := by
  have noneOld : (state.seats client).published = none := by
    rw [Bool.and_eq_true] at fresh
    have noneFlag : (state.seats client).published.isNone = true := fresh.2
    cases hpub : (state.seats client).published with
    | none => rfl
    | some _ =>
        rw [hpub] at noneFlag
        cases noneFlag
  have absent : client ∉ state.deliveries := by
    intro member
    have eqPublished := law.published client
    rw [if_pos member, noneOld] at eqPublished
    cases eqPublished
  have deliveriesEq :
      (applyShared earned (SharedAct.publish client) state).deliveries =
        state.deliveries ++ [client] := by
    simp [applyShared, fresh]
  have ownershipEq :
      (applyShared earned (SharedAct.publish client) state).ownership = state.ownership := by
    simp [applyShared]
  have registryEq :
      (applyShared earned (SharedAct.publish client) state).registry = state.registry := by
    simp [applyShared]
  have handlesEq :
      (applyShared earned (SharedAct.publish client) state).handles = state.handles := by
    simp [applyShared]
  have seatsEq : ∀ index,
      (applyShared earned (SharedAct.publish client) state).seats index =
        if index = client then applySeat earned ConsumerAct.publish (state.seats client)
        else state.seats index := by
    intro index
    simp [applyShared, updateAt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [deliveriesEq]
    exact nodup_append_singleton law.nodup absent
  · intro index
    by_cases same : index = client
    · subst index
      have publishedEq :
          ((applyShared earned (SharedAct.publish client) state).seats client).published =
            some earned := by
        rw [seatsEq client, if_pos rfl, publish_sets_publication earned (state.seats client),
          fresh, if_pos rfl]
      have member : client ∈ state.deliveries ++ [client] := by
        simp [List.mem_append]
      rw [publishedEq, deliveriesEq, if_pos member]
    · have publishedEq :
          ((applyShared earned (SharedAct.publish client) state).seats index).published =
            (state.seats index).published := by
        rw [seatsEq index, if_neg same]
      have memberIff : index ∈ state.deliveries ++ [client] ↔ index ∈ state.deliveries := by
        constructor
        · intro member
          rw [List.mem_append, List.mem_singleton] at member
          cases member with
          | inl kept => exact kept
          | inr eqClient => exact (same eqClient).elim
        · exact fun kept => List.mem_append_left _ kept
      rw [publishedEq, law.published index, deliveriesEq]
      by_cases present : index ∈ state.deliveries
      · rw [if_pos present, if_pos (memberIff.mpr present)]
      · rw [if_neg present, if_neg (fun hit => present (memberIff.mp hit))]
  · intro index
    by_cases same : index = client
    · subst index
      have liveEq :
          ((applyShared earned (SharedAct.publish client) state).seats client).live =
            (state.seats client).live := by
        rw [seatsEq client, if_pos rfl, publish_keeps_live earned (state.seats client)]
      rw [ownershipEq, law.cursor client, liveEq]
    · have liveEq :
          ((applyShared earned (SharedAct.publish client) state).seats index).live =
            (state.seats index).live := by
        rw [seatsEq index, if_neg same]
      rw [ownershipEq, law.cursor index, liveEq]
  · intro index liveNext
    rw [handlesEq]
    apply law.liveHandle index
    by_cases same : index = client
    · subst index
      rw [seatsEq client, if_pos rfl, publish_keeps_live earned (state.seats client)] at liveNext
      exact liveNext
    · rw [seatsEq index, if_neg same] at liveNext
      exact liveNext
  · intro index liveNext
    rw [handlesEq, registryEq]
    apply law.liveAuthority index
    by_cases same : index = client
    · subst index
      rw [seatsEq client, if_pos rfl, publish_keeps_live earned (state.seats client)] at liveNext
      exact liveNext
    · rw [seatsEq index, if_neg same] at liveNext
      exact liveNext

private theorem publish_preserves_law {Production : Type} (earned : Production)
    (start state : SharedConsumers Production) (client : Fin 2)
    (law : SharedLaw earned start state) :
    SharedLaw earned start (applyShared earned (SharedAct.publish client) state) := by
  cases fresh : (state.seats client).live && (state.seats client).published.isNone with
  | false => exact publish_idle_preserves_law earned start state client fresh law
  | true => exact publish_once_preserves_law earned start state client fresh law

private theorem retire_shape_preserves_law {Production : Type} (earned : Production)
    (start state next : SharedConsumers Production) (client : Fin 2)
    (law : SharedLaw earned start state)
    (deliveriesEq : next.deliveries = state.deliveries)
    (ownershipEq : next.ownership = cancelConsumer state.ownership client)
    (seatsEq : ∀ index, next.seats index =
      if index = client then applySeat earned ConsumerAct.retire (state.seats client)
      else state.seats index)
    (handlesOther : ∀ index, index ≠ client → next.handles index = state.handles index)
    (registryLive : ∀ index, index ≠ client → (state.seats index).live = true →
      (jointAuthenticated next.registry (next.handles index) ↔
        jointAuthenticated state.registry (state.handles index))) :
    SharedLaw earned start next := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [deliveriesEq] using law.nodup
  · intro index
    by_cases same : index = client
    · subst index
      have publishedEq : (next.seats client).published = (state.seats client).published := by
        rw [seatsEq client, if_pos rfl, (retire_keeps_publication earned (state.seats client)).2]
      rw [publishedEq, law.published client, deliveriesEq]
    · have publishedEq : (next.seats index).published = (state.seats index).published := by
        rw [seatsEq index, if_neg same]
      rw [publishedEq, law.published index, deliveriesEq]
  · intro index
    by_cases same : index = client
    · subst index
      have unreadNil : unread next.ownership.log client = [] := by
        rw [ownershipEq]
        exact unread_cancel_self state.ownership.log client
      have dead : (next.seats client).live = false := by
        rw [seatsEq client, if_pos rfl, (retire_keeps_publication earned (state.seats client)).1]
      rw [unreadNil, dead, if_neg Bool.false_ne_true]
    · have kept : unread next.ownership.log index = unread state.ownership.log index := by
        rw [ownershipEq]
        exact unread_cancel_other state.ownership.log client index same
      have liveEq : (next.seats index).live = (state.seats index).live := by
        rw [seatsEq index, if_neg same]
      rw [kept, law.cursor index, liveEq]
  · intro index liveNext
    by_cases same : index = client
    · subst index
      have dead : (next.seats client).live = false := by
        rw [seatsEq client, if_pos rfl, (retire_keeps_publication earned (state.seats client)).1]
      rw [dead] at liveNext
      cases liveNext
    · rw [handlesOther index same]
      apply law.liveHandle index
      have liveEq : (next.seats index).live = (state.seats index).live := by
        rw [seatsEq index, if_neg same]
      rw [← liveEq]
      exact liveNext
  · intro index liveNext
    by_cases same : index = client
    · subst index
      have dead : (next.seats client).live = false := by
        rw [seatsEq client, if_pos rfl, (retire_keeps_publication earned (state.seats client)).1]
      rw [dead] at liveNext
      cases liveNext
    · have liveOld : (state.seats index).live = true := by
        have liveEq : (next.seats index).live = (state.seats index).live := by
          rw [seatsEq index, if_neg same]
        rw [← liveEq]
        exact liveNext
      exact (registryLive index same liveOld).trans (law.liveAuthority index liveOld)

private theorem distinct_rows_of_live {Production : Type} (earned : Production)
    (start state : SharedConsumers Production)
    (law : SharedLaw earned start state)
    (different : (start.handles 0).row ≠ (start.handles 1).row)
    {client index : Fin 2} (liveClient : (state.seats client).live = true)
    (liveIndex : (state.seats index).live = true) (distinct : index ≠ client) :
    (state.handles index).row ≠ (state.handles client).row := by
  have handleClient := law.liveHandle client liveClient
  have handleIndex := law.liveHandle index liveIndex
  rw [handleClient, handleIndex]
  have clientSplit : client.val = 0 ∨ client.val = 1 := by
    have lt := client.isLt
    omega
  have indexSplit : index.val = 0 ∨ index.val = 1 := by
    have lt := index.isLt
    omega
  rcases clientSplit with client0 | client1 <;> rcases indexSplit with index0 | index1
  · exact (distinct (Fin.eq_of_val_eq (index0.trans client0.symm))).elim
  · have clientZero : client = 0 := Fin.eq_of_val_eq client0
    have indexOne : index = 1 := Fin.eq_of_val_eq index1
    rw [clientZero, indexOne]
    exact different.symm
  · have clientOne : client = 1 := Fin.eq_of_val_eq client1
    have indexZero : index = 0 := Fin.eq_of_val_eq index0
    rw [clientOne, indexZero]
    exact different
  · exact (distinct (Fin.eq_of_val_eq (index1.trans client1.symm))).elim

private theorem retire_preserves_law {Production : Type} (earned : Production)
    (start state : SharedConsumers Production) (client : Fin 2)
    (law : SharedLaw earned start state)
    (different : (start.handles 0).row ≠ (start.handles 1).row) :
    SharedLaw earned start (applyShared earned (SharedAct.retire client) state) := by
  cases hlive : (state.seats client).live with
  | false =>
      have deliveriesEq :
          (applyShared earned (SharedAct.retire client) state).deliveries = state.deliveries := by
        simp [applyShared, hlive]
      have ownershipEq :
          (applyShared earned (SharedAct.retire client) state).ownership =
            cancelConsumer state.ownership client := by
        simp [applyShared, hlive]
      have seatsEq : ∀ index,
          (applyShared earned (SharedAct.retire client) state).seats index =
            if index = client then applySeat earned ConsumerAct.retire (state.seats client)
            else state.seats index := by
        intro index
        simp [applyShared, hlive, updateAt]
      have handlesOther : ∀ index, index ≠ client →
          (applyShared earned (SharedAct.retire client) state).handles index =
            state.handles index := by
        intro _index _distinct
        simp [applyShared, hlive]
      have registryLive : ∀ index, index ≠ client → (state.seats index).live = true →
          (jointAuthenticated
              (applyShared earned (SharedAct.retire client) state).registry
              ((applyShared earned (SharedAct.retire client) state).handles index) ↔
            jointAuthenticated state.registry (state.handles index)) := by
        intro index _distinct _liveIndex
        simp [applyShared, hlive]
      exact retire_shape_preserves_law earned start state
        (applyShared earned (SharedAct.retire client) state) client law deliveriesEq ownershipEq
        seatsEq handlesOther registryLive
  | true =>
      cases hrel : releaseJoint state.registry (state.handles client) with
      | mk reply visits =>
          cases reply with
          | none =>
              have deliveriesEq :
                  (applyShared earned (SharedAct.retire client) state).deliveries =
                    state.deliveries := by
                simp [applyShared, hlive, hrel]
              have ownershipEq :
                  (applyShared earned (SharedAct.retire client) state).ownership =
                    cancelConsumer state.ownership client := by
                simp [applyShared, hlive, hrel]
              have seatsEq : ∀ index,
                  (applyShared earned (SharedAct.retire client) state).seats index =
                    if index = client then
                      applySeat earned ConsumerAct.retire (state.seats client)
                    else state.seats index := by
                intro index
                simp [applyShared, hlive, hrel, updateAt]
              have handlesOther : ∀ index, index ≠ client →
                  (applyShared earned (SharedAct.retire client) state).handles index =
                    state.handles index := by
                intro _index _distinct
                simp [applyShared, hlive, hrel]
              have registryLive : ∀ index, index ≠ client → (state.seats index).live = true →
                  (jointAuthenticated
                      (applyShared earned (SharedAct.retire client) state).registry
                      ((applyShared earned (SharedAct.retire client) state).handles index) ↔
                    jointAuthenticated state.registry (state.handles index)) := by
                intro index _distinct _liveIndex
                simp [applyShared, hlive, hrel]
              exact retire_shape_preserves_law earned start state
                (applyShared earned (SharedAct.retire client) state) client law deliveriesEq
                ownershipEq seatsEq handlesOther registryLive
          | some pair =>
              cases pair with
              | mk nextRegistry cleared =>
                  have deliveriesEq :
                      (applyShared earned (SharedAct.retire client) state).deliveries =
                        state.deliveries := by
                    simp [applyShared, hlive, hrel]
                  have ownershipEq :
                      (applyShared earned (SharedAct.retire client) state).ownership =
                        cancelConsumer state.ownership client := by
                    simp [applyShared, hlive, hrel]
                  have seatsEq : ∀ index,
                      (applyShared earned (SharedAct.retire client) state).seats index =
                        if index = client then
                          applySeat earned ConsumerAct.retire (state.seats client)
                        else state.seats index := by
                    intro index
                    simp [applyShared, hlive, hrel, updateAt]
                  have handlesOther : ∀ index, index ≠ client →
                      (applyShared earned (SharedAct.retire client) state).handles index =
                        state.handles index := by
                    intro index distinct
                    simp only [applyShared, hlive, hrel]
                    rw [if_pos trivial]
                    simp only [updateAt]
                    rw [if_neg distinct]
                  have registryLive : ∀ index, index ≠ client →
                      (state.seats index).live = true →
                      (jointAuthenticated
                          (applyShared earned (SharedAct.retire client) state).registry
                          ((applyShared earned (SharedAct.retire client) state).handles index) ↔
                        jointAuthenticated state.registry (state.handles index)) := by
                    intro index distinct liveIndex
                    have handleEq :
                        (applyShared earned (SharedAct.retire client) state).handles index =
                          state.handles index :=
                      handlesOther index distinct
                    have registryEq :
                        (applyShared earned (SharedAct.retire client) state).registry =
                          nextRegistry := by
                      simp [applyShared, hlive, hrel]
                    rw [handleEq, registryEq]
                    exact Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.releaseIssued_keeps_other
                      state.registry (state.handles client) (state.handles index) nextRegistry
                      cleared visits hrel
                      (distinct_rows_of_live earned start state law different hlive liveIndex
                        distinct)
                  exact retire_shape_preserves_law earned start state
                    (applyShared earned (SharedAct.retire client) state) client law deliveriesEq
                    ownershipEq seatsEq handlesOther registryLive

theorem applyShared_preserves_law {Production : Type} (earned : Production)
    (start state : SharedConsumers Production) (op : SharedAct)
    (law : SharedLaw earned start state)
    (different : (start.handles 0).row ≠ (start.handles 1).row) :
    SharedLaw earned start (applyShared earned op state) := by
  cases op with
  | inspect client => exact inspect_preserves_law earned start state client law
  | publish client => exact publish_preserves_law earned start state client law
  | retire client => exact retire_preserves_law earned start state client law different

private theorem applyShared_deliveries_split {Production : Type} (earned : Production)
    (op : SharedAct) (state : SharedConsumers Production) :
    (applyShared earned op state).deliveries =
      state.deliveries ++
        ((applyShared earned op state).deliveries.drop state.deliveries.length) := by
  obtain ⟨suffix, grown⟩ := applyShared_grows earned op state
  have grownDeliveries : state.deliveries ++ suffix =
      (applyShared earned op state).deliveries := by
    simpa [committedShared] using grown
  have suffixEq : (applyShared earned op state).deliveries.drop state.deliveries.length =
      suffix := by
    rw [← grownDeliveries]
    exact List.drop_append_length
  rw [suffixEq]
  exact grownDeliveries.symm

/-- `cancel` rewrites the epoch and, for the current ticket of a retained host,
drops the seat. The delivered observation list and the world stay. -/
private theorem cancel_keeps_observations
    {State : Type} {Effect : Type} {World : Type}
    (ticket : Nat) (host : Host State Effect World) :
    (cancel ticket host).delivered = host.delivered ∧
      (cancel ticket host).world = host.world := by
  by_cases current : ticket = host.epoch
  · cases retained : host.retained with
    | none =>
        rw [cancel_retired ticket retained]
        exact ⟨rfl, rfl⟩
    | some _state =>
        subst current
        rw [cancel_current retained]
        exact ⟨rfl, rfl⟩
  · rw [cancel_stale current]
    exact ⟨rfl, rfl⟩

/-- One `Reached` induction for a shared host. `project` turns the delivered
client list into the world, and `step` is the action's interpretation of one
fresh suffix. `deliverAct` and `frameAct` are instances. The seat law is the
same for both. This induction does not use `Reached.accounts`. -/
private theorem reachable_action_law
    {Production : Type} {World : Type} (earned : Production)
    (act : Fin 2 → World → World)
    (project : List (Fin 2) → World) (origin : World)
    (originEq : origin = project [])
    (step : ∀ delivered suffix,
      interpret act suffix (project delivered) = project (delivered ++ suffix))
    (ownership : Configuration CellId Nat 2) (registry : JointIssuedRegistry)
    (handles : Fin 2 → JointIssuedHandle)
    (different : (handles 0).row ≠ (handles 1).row)
    {host : Host (SharedConsumers Production) (Fin 2) World}
    (reached : Reached (sharedSystem earned) act origin
      (freshShared ownership registry handles) host) :
    host.world = project host.delivered ∧
      host.delivered.Nodup ∧
      (∀ state, host.retained = some state →
        state.deliveries = host.delivered ∧
          SharedLaw earned (freshShared ownership registry handles) state) ∧
      ∀ ticket,
        (cancel ticket host).delivered = host.delivered ∧
          (cancel ticket host).world = host.world := by
  have differentStart :
      ((freshShared (Production := Production) ownership registry handles).handles 0).row ≠
        ((freshShared (Production := Production) ownership registry handles).handles 1).row := by
    simpa [freshShared] using different
  induction reached with
  | begin =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [begin, sharedSystem, committedShared, freshShared, interpret_nil, originEq]
      · simp [begin, sharedSystem, committedShared, freshShared]
      · intro state retained
        simp only [begin] at retained
        cases retained
        refine ⟨?_, freshShared_satisfies_law earned ownership registry handles⟩
        simp [begin, sharedSystem, committedShared, freshShared]
      · intro ticket
        exact cancel_keeps_observations ticket _
  | @submit host ticket op _ ih =>
      by_cases current : ticket = host.epoch
      · cases retained : host.retained with
        | none =>
            rw [submit_retired (sharedSystem earned) act ticket op retained]
            exact ih
        | some state =>
            subst current
            have preserved := ih.2.2.1 state retained
            have lawNext := applyShared_preserves_law earned
              (freshShared ownership registry handles) state op preserved.2 differentStart
            let freshSuffix :=
              ((sharedSystem earned).committed
                  ((sharedSystem earned).apply op state)).drop
                ((sharedSystem earned).committed state).length
            have worldNext :
                interpret act freshSuffix host.world = project (host.delivered ++ freshSuffix) := by
              rw [ih.1]
              exact step host.delivered freshSuffix
            rw [submit_current (sharedSystem earned) act op retained]
            have deliveredEq : host.delivered ++ freshSuffix =
                (applyShared earned op state).deliveries := by
              rw [← preserved.1]
              exact (applyShared_deliveries_split earned op state).symm
            refine ⟨worldNext, ?_, ?_, ?_⟩
            · rw [deliveredEq]
              exact lawNext.nodup
            · intro nextState sameState
              cases sameState
              exact ⟨deliveredEq.symm, lawNext⟩
            · intro nextTicket
              exact cancel_keeps_observations nextTicket _
      · rw [submit_stale (sharedSystem earned) act op current]
        exact ih
  | @cancel host ticket _ ih =>
      by_cases current : ticket = host.epoch
      · cases retained : host.retained with
        | none =>
            rw [cancel_retired ticket retained]
            exact ih
        | some _state =>
            subst current
            rw [cancel_current retained]
            refine ⟨ih.1, ih.2.1, ?_, ?_⟩
            · intro _nextState absent
              cases absent
            · intro nextTicket
              exact cancel_keeps_observations nextTicket _
      · rw [cancel_stale current]
        exact ih

private theorem reachable_shared_package {Production : Type} (earned : Production)
    (ownership : Configuration CellId Nat 2) (registry : JointIssuedRegistry)
    (handles : Fin 2 → JointIssuedHandle)
    (different : (handles 0).row ≠ (handles 1).row)
    {host : Host (SharedConsumers Production) (Fin 2) (List Production)}
    (reached : Reached (sharedSystem earned) (deliverAct earned) ([] : List Production)
      (freshShared ownership registry handles) host) :
    host.world = host.delivered.map (fun _ => earned) ∧
      host.delivered.Nodup ∧
      (∀ state, host.retained = some state →
        state.deliveries = host.delivered ∧
          SharedLaw earned (freshShared ownership registry handles) state) ∧
      ∀ ticket,
        (cancel ticket host).delivered = host.delivered ∧
          (cancel ticket host).world = host.world :=
  reachable_action_law earned (deliverAct earned)
    (fun delivered => delivered.map (fun _ => earned)) [] rfl
    (by
      intro delivered suffix
      unfold deliverAct
      simp only [interpret_repeat_item, List.map_append])
    ownership registry handles different reached

/-- Every reachable shared host's world is the list of its delivery
observations of `earned`, one observation per delivery. While a seat is
retained, that seat's delivery list is the host's delivered list and the
seat satisfies `SharedLaw`. Cancelling a ticket keeps the observation list
and the world. The paid account is the denotation of the issued ledger.
Retirement drops the retained seat and keeps these observations. -/
theorem reachable_shared_histories {Production : Type} (earned : Production)
    (ownership : Configuration CellId Nat 2) (registry : JointIssuedRegistry)
    (handles : Fin 2 → JointIssuedHandle)
    (different : (handles 0).row ≠ (handles 1).row)
    {host : Host (SharedConsumers Production) (Fin 2) (List Production)}
    (reached : Reached (sharedSystem earned) (deliverAct earned) ([] : List Production)
      (freshShared ownership registry handles) host) :
    host.world = host.delivered.map (fun _ => earned) ∧
      host.delivered.Nodup ∧
      (∀ state, host.retained = some state →
        state.deliveries = host.delivered ∧
          SharedLaw earned (freshShared ownership registry handles) state) ∧
      ∀ ticket,
        (cancel ticket host).delivered = host.delivered ∧
          (cancel ticket host).world = host.world := by
  exact reachable_shared_package earned ownership registry handles different reached

/-- After any ticket cancels a reachable host, the world is still the
delivered observation list. Each observation is `earned`. The paid account
is a separate fact. The retained seat may be gone; the observations stay. -/
theorem reachable_retirement_preserves_observations
    {Production : Type} (earned : Production)
    (ownership : Configuration CellId Nat 2) (registry : JointIssuedRegistry)
    (handles : Fin 2 → JointIssuedHandle)
    (different : (handles 0).row ≠ (handles 1).row)
    {host : Host (SharedConsumers Production) (Fin 2) (List Production)}
    (reached : Reached (sharedSystem earned) (deliverAct earned) ([] : List Production)
      (freshShared ownership registry handles) host)
    (ticket : Nat) :
    (cancel ticket host).delivered = host.delivered ∧
      (cancel ticket host).world = host.world ∧
      (cancel ticket host).world =
        (cancel ticket host).delivered.map (fun _ => earned) := by
  obtain ⟨worldEq, _nodup, _retainedLaw, kept⟩ :=
    reachable_shared_histories earned ownership registry handles different reached
  obtain ⟨deliveredEq, worldKept⟩ := kept ticket
  refine ⟨deliveredEq, worldKept, ?_⟩
  rw [worldKept, deliveredEq]
  exact worldEq

def pairHandles (handles : List JointIssuedHandle) :
    Option (Fin 2 → JointIssuedHandle) :=
  match handles with
  | [left, right] =>
      some (fun client => if client = (0 : Fin 2) then left else right)
  | _ => none

/-- Retiring client `0` keeps client `1` by name: its handle, authentication,
unread rows, and the delivery list. The retired client's unread rows are
empty. Releasing the live handle does not free the earned payload. -/
theorem retire_one_client_preserves_the_named_survivor
    {Production : Type} (earned : Production)
    (start state : SharedConsumers Production)
    (law : SharedLaw earned start state)
    (different : (start.handles 0).row ≠ (start.handles 1).row)
    (live0 : (state.seats 0).live = true)
    (live1 : (state.seats 1).live = true)
    (authenticated : jointAuthenticated start.registry (start.handles 1))
    {next : JointIssuedRegistry} {cleared : JointIssuedHandle} {visits : Nat}
    (released : releaseJoint state.registry (state.handles 0) =
      (some (next, cleared), visits)) :
    ((applyShared earned (SharedAct.retire 0) state).seats 0).live = false ∧
      ((applyShared earned (SharedAct.retire 0) state).seats 1).live = true ∧
      (applyShared earned (SharedAct.retire 0) state).handles 1 = start.handles 1 ∧
      jointAuthenticated
        (applyShared earned (SharedAct.retire 0) state).registry
        ((applyShared earned (SharedAct.retire 0) state).handles 1) ∧
      unread (applyShared earned (SharedAct.retire 0) state).ownership.log 0 = [] ∧
      unread (applyShared earned (SharedAct.retire 0) state).ownership.log 1 =
        unread start.ownership.log 1 ∧
      (applyShared earned (SharedAct.retire 0) state).deliveries = state.deliveries ∧
      (applyShared earned (SharedAct.retire 0) state).registry = next := by
  have shape : applyShared earned (SharedAct.retire 0) state =
      { state with
          seats := updateAt state.seats 0
            (applySeat earned ConsumerAct.retire (state.seats 0))
          ownership := cancelConsumer state.ownership 0
          registry := next
          handles := updateAt state.handles 0 cleared } := by
    simp [applyShared, live0, released]
  have dead : ((applyShared earned (SharedAct.retire 0) state).seats 0).live = false := by
    rw [shape]
    simp [updateAt, applySeat]
  have alive : ((applyShared earned (SharedAct.retire 0) state).seats 1).live = true := by
    rw [shape]
    have distinct : (1 : Fin 2) ≠ 0 := by decide
    simp [updateAt, distinct, live1]
  have handleState : (applyShared earned (SharedAct.retire 0) state).handles 1 =
      state.handles 1 := by
    rw [shape]
    have distinct : (1 : Fin 2) ≠ 0 := by decide
    simp [updateAt, distinct]
  have handleStart : state.handles 1 = start.handles 1 := law.liveHandle 1 live1
  have handleZero : state.handles 0 = start.handles 0 := law.liveHandle 0 live0
  have rowNe : (state.handles 1).row ≠ (state.handles 0).row := by
    rw [handleStart, handleZero]
    intro same
    exact different same.symm
  have authState : jointAuthenticated state.registry (state.handles 1) :=
    (law.liveAuthority 1 live1).mpr authenticated
  have authNext : jointAuthenticated next (state.handles 1) :=
    (Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.releaseIssued_keeps_other
      state.registry (state.handles 0) (state.handles 1) next cleared visits released
      rowNe).mpr authState
  have unreadZero : unread (applyShared earned (SharedAct.retire 0) state).ownership.log 0 =
      [] := by
    rw [shape]
    simp only [cancelConsumer]
    exact unread_cancel_self state.ownership.log 0
  have unreadKept : unread (applyShared earned (SharedAct.retire 0) state).ownership.log 1 =
      unread state.ownership.log 1 := by
    rw [shape]
    simp only [cancelConsumer]
    exact unread_cancel_other state.ownership.log 0 1 (by decide)
  have cursor := law.cursor 1
  rw [live1, if_pos rfl] at cursor
  have deliveriesEq : (applyShared earned (SharedAct.retire 0) state).deliveries =
      state.deliveries := by
    rw [shape]
  have registryEq : (applyShared earned (SharedAct.retire 0) state).registry = next := by
    rw [shape]
  refine ⟨dead, alive, ?_, ?_, unreadZero, ?_, deliveriesEq, registryEq⟩
  · rw [handleState, handleStart]
  · rw [handleState, registryEq]
    exact authNext
  · rw [unreadKept, cursor]

/-- A reachable host that retires client `0` keeps client `1` and adds no
delivery. The proof uses the shared transition induction. It does not assume
the delivered-world correspondence. -/
theorem reachable_retirement_preserves_the_named_client
    {Production : Type} (earned : Production)
    (ownership : Configuration CellId Nat 2) (registry : JointIssuedRegistry)
    (handles : Fin 2 → JointIssuedHandle)
    (different : (handles 0).row ≠ (handles 1).row)
    {host : Host (SharedConsumers Production) (Fin 2) (List Production)}
    (reached : Reached (sharedSystem earned) (deliverAct earned) ([] : List Production)
      (freshShared ownership registry handles) host)
    (ticket : Nat) {state : SharedConsumers Production}
    (retained : host.retained = some state)
    (current : ticket = host.epoch)
    (live0 : (state.seats 0).live = true)
    (live1 : (state.seats 1).live = true)
    (authenticated : jointAuthenticated registry (handles 1))
    {next : JointIssuedRegistry} {cleared : JointIssuedHandle} {visits : Nat}
    (released : releaseJoint state.registry (state.handles 0) =
      (some (next, cleared), visits)) :
    ∃ retired : SharedConsumers Production,
      (submit (sharedSystem earned) (deliverAct earned) ticket (SharedAct.retire 0) host).retained =
        some retired ∧
        (retired.seats 0).live = false ∧
        (retired.seats 1).live = true ∧
        retired.handles 1 = handles 1 ∧
        jointAuthenticated retired.registry (retired.handles 1) ∧
        unread retired.ownership.log 0 = [] ∧
        unread retired.ownership.log 1 = unread ownership.log 1 ∧
        (submit (sharedSystem earned) (deliverAct earned) ticket (SharedAct.retire 0) host).delivered =
          host.delivered ∧
        (submit (sharedSystem earned) (deliverAct earned) ticket (SharedAct.retire 0) host).world =
          host.world := by
  obtain ⟨_worldEq, _nodup, retainedLaw, _cancelKept⟩ :=
    reachable_shared_histories earned ownership registry handles different reached
  obtain ⟨_deliveredState, law⟩ := retainedLaw state retained
  obtain ⟨dead, alive, handleEq, auth, unreadZero, unreadOne, delSame, _registryEq⟩ :=
    retire_one_client_preserves_the_named_survivor earned
      (freshShared ownership registry handles) state law
      (by simpa [freshShared] using different) live0 live1
      (by simpa [freshShared] using authenticated) released
  have freshNil :
      (((sharedSystem earned).committed
          ((sharedSystem earned).apply (SharedAct.retire 0) state)).drop
        ((sharedSystem earned).committed state).length) = [] := by
    simp only [sharedSystem, committedShared, delSame, List.drop_length]
  have submitted := submit_current (sharedSystem earned) (deliverAct earned)
    (SharedAct.retire 0) retained
  rw [← current] at submitted
  simp only [freshNil, interpret_nil, List.append_nil] at submitted
  refine ⟨applyShared earned (SharedAct.retire 0) state, ?_, dead, alive, ?_, auth,
      unreadZero, ?_, ?_, ?_⟩
  · rw [submitted]
    simp [sharedSystem]
  · rw [handleEq]
    simp [freshShared]
  · rw [unreadOne]
    simp [freshShared]
  · simp [submitted]
  · simp [submitted]

def startedHost (cert : SourceCertificate) :
    Option (Host (SharedConsumers JointLedger) (Fin 2) (List JointLedger)) :=
  match pairHandles cert.handles with
  | none => none
  | some handles =>
      some (begin (sharedSystem cert.ledger) (deliverAct cert.ledger)
        (freshShared (configurationOfRoots cert.roots) cert.registry handles)
        ([] : List JointLedger))

def presentedLeaf (account : PresentedAccount) :
    Option ((JointOccurrence ⊕ JointOccurrence) × Nat) :=
  match account.cut with
  | [leaf] => some leaf
  | _ => none

structure PassiveInspection where
  account : PresentedAccount
  returned : Bool
  host : Option (Host (SharedConsumers JointLedger) (Fin 2) (List JointLedger))

def inspectpassive {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (presented : PresentedAccount) : RetainedAdmit PassiveInspection :=
  match issueEarned history with
  | none => .reject .incoherentResidual ⟨presented, false, none⟩
  | some cert =>
      match admitIssued cert presented with
      | .reject reason kept => .reject reason ⟨kept, false, none⟩
      | .accept account =>
          match presentedLeaf account with
          | some (Sum.inl _, _) =>
              .accept ⟨account, true, startedHost cert⟩
          | some (Sum.inr _, _) =>
              .accept ⟨account, false, none⟩
          | none =>
              .reject .incompleteResidual ⟨account, false, none⟩

theorem inspectpassive_keeps_a_refused_account
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (presented : PresentedAccount) {reason : Refusal} {kept : PassiveInspection}
    (refused : inspectpassive history presented = .reject reason kept) :
    kept.host = none ∧ kept.returned = false ∧ kept.account = presented := by
  unfold inspectpassive at refused
  split at refused
  · cases refused
    exact ⟨rfl, rfl, rfl⟩
  · rename_i cert _issued
    split at refused
    · rename_i _reason' keptAccount hadmit
      have keptEq : keptAccount = presented := by
        have same := admitIssued_keeps cert presented
        rw [hadmit] at same
        simpa [RetainedAdmit.kept] using same
      cases refused
      simp [keptEq]
    · rename_i account hadmit
      split at refused
      · simp at refused
      · simp at refused
      · have accountEq : account = presented := by
          have same := admitIssued_keeps cert presented
          rw [hadmit] at same
          simpa [RetainedAdmit.kept] using same
        cases refused
        simp [accountEq]

theorem explicit_resumption_uses_the_admitted_account
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (presented : PresentedAccount) (suffix : Nat) {cert : SourceCertificate}
    (issued : issueEarned history = some cert)
    (admitted : admitIssued cert presented = .accept presented) :
    consumeAuthenticated history presented suffix =
      .accept (resumeAccepted presented cert.ledger suffix) := by
  unfold consumeAuthenticated
  simp [issued, admitted]

theorem inspectpassive_returned_keeps_the_endpoint
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    {cert : SourceCertificate}
    (issued : issueEarned history = some cert)
    (halted : isHalted target = true) :
    inspectpassive history (endpointAccount history) =
      .accept ⟨endpointAccount history, true, startedHost cert⟩ ∧
      cert.payment = denote cert.ledger ∧
      cert.ledger = earnedLedger history := by
  have admitted := earned_endpoint_is_admitted issued
  have consumed := earned_endpoint_is_consumed history 0 issued
  have leaf : presentedLeaf (endpointAccount history) =
      some (Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence),
        denote (earnedLedger history)) := by
    have cutEq : (endpointAccount history).cut =
        [(Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence),
          denote (earnedLedger history))] := by
      simp [endpointAccount, halted]
    unfold presentedLeaf
    rw [cutEq]
  refine ⟨?_, consumed.2.2.1, consumed.2.1⟩
  unfold inspectpassive
  simp only [issued, admitted, leaf]

/-- An accepted pending leaf keeps the admitted account and starts no host.
The pending occurrence and its weight are arbitrary. This inspection does
not resume the account. -/
theorem accepted_pending_inspection_retains_the_account
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (presented : PresentedAccount) {cert : SourceCertificate}
    {account : PresentedAccount}
    (issued : issueEarned history = some cert)
    (admitted : admitIssued cert presented = .accept account)
    {pending : JointOccurrence} {weight : Nat}
    (leaf : presentedLeaf account = some (Sum.inr pending, weight)) :
    inspectpassive history presented = .accept ⟨account, false, none⟩ ∧
      account = presented := by
  have accountEq : account = presented := by
    have same := admitIssued_keeps cert presented
    rw [admitted] at same
    simpa [RetainedAdmit.kept] using same
  refine ⟨?_, accountEq⟩
  unfold inspectpassive
  simp only [issued, admitted, leaf]

private theorem contributions_zero (state : JointOccurrence) :
    contributions jointSource 0 state = [(.inr state, (1 : Nat))] := rfl

private theorem one_weight_preserves_the_leaf
    (items : List ((JointOccurrence ⊕ JointOccurrence) × Nat)) :
    items.map (fun second => (second.1, (1 : Nat) * second.2)) = items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk which weight =>
          calc
            ((which, weight) :: tail).map
                (fun second => (second.1, (1 : Nat) * second.2))
              = (which, (1 : Nat) * weight) ::
                  tail.map (fun second => (second.1, (1 : Nat) * second.2)) := rfl
            _ = (which, weight) ::
                  tail.map (fun second => (second.1, (1 : Nat) * second.2)) := by
                rw [Nat.one_mul]
            _ = (which, weight) :: tail := by rw [ih]

private theorem pending_passive_package :
    ∃ (pending : JointOccurrence)
      (history : History (pathMachine jointSpec jointStart) jointStart pending.state)
      (cert : SourceCertificate)
      (inspection : PassiveInspection),
      inspectpassive history (endpointAccount history) = .accept inspection ∧
        inspection.returned = false ∧
        inspection.host = none ∧
        inspection.account = endpointAccount history ∧
        inspection.account.cut = jointForceCut ∧
        jointForceCut = [(.inr pending, (1 : Nat))] ∧
        cert.ledger = ([] : JointLedger) ∧
        cert.payment = denote cert.ledger ∧
        denote cert.ledger = 1 ∧
        issueEarned history = some cert ∧
        admitIssued cert (endpointAccount history) =
          .accept (endpointAccount history) ∧
        cert.rights = {Right.force} ∧
        cert.halted = false := by
  obtain ⟨pending0, history, cert, issued, haltedCert, forceRights, payment, _ledger,
      traced, _control, _cell, _eval, _resume0, _delivered0, resumed0, denote1,
      _cutIssued⟩ := suspended_consumer_resumes_the_source 0
  have haltedTarget : isHalted pending0.state = false := by
    exact ((earned_history_is_the_passive_issuer issued).2.2.2.2.2.2.1).symm.trans
      haltedCert
  have traceHistory : earnedTrace history = jointForceTrace := by
    exact ((earned_endpoint_is_consumed history 0 issued).2.2.2.1).symm.trans traced
  have payHistory : denote (earnedLedger history) = 1 := by
    rw [← (earned_endpoint_is_consumed history 0 issued).2.1]
    exact denote1
  let pending : JointOccurrence := ⟨pending0.state, jointForceTrace⟩
  have cutShape : (endpointAccount history).cut = [(.inr pending, (1 : Nat))] := by
    simp only [endpointAccount, haltedTarget]
    simp only [if_neg Bool.false_ne_true, traceHistory, payHistory]
    rfl
  have resumedCut : weightedResume jointSource 0 (endpointAccount history).cut =
      jointForceCut := by
    simpa [resumeAccepted, jointForceCut] using resumed0
  have resumeId : weightedResume jointSource 0 (endpointAccount history).cut =
      (endpointAccount history).cut := by
    simp only [weightedResume, cutShape]
    rfl
  have accountCut : (endpointAccount history).cut = jointForceCut :=
    resumeId.symm.trans resumedCut
  have forceShape : jointForceCut = [(.inr pending, (1 : Nat))] :=
    accountCut.symm.trans cutShape
  have admitted := earned_endpoint_is_admitted issued
  have leaf : presentedLeaf (endpointAccount history) =
      some (.inr pending, (1 : Nat)) := by
    unfold presentedLeaf
    rw [cutShape]
  have inspected : inspectpassive history (endpointAccount history) =
      .accept ⟨endpointAccount history, false, none⟩ := by
    unfold inspectpassive
    simp only [issued, admitted, leaf]
  have payDenote : cert.payment = denote cert.ledger := payment.trans denote1.symm
  exact ⟨pending, history, cert, ⟨endpointAccount history, false, none⟩,
    inspected, rfl, rfl, rfl, accountCut, forceShape, _ledger, payDenote, denote1,
    issued, admitted, forceRights, haltedCert⟩

theorem passive_pending_is_inert :
    ∃ (pending : JointOccurrence)
      (history : History (pathMachine jointSpec jointStart) jointStart pending.state)
      (cert : SourceCertificate)
      (inspection : PassiveInspection),
      inspectpassive history (endpointAccount history) = .accept inspection ∧
        inspection.returned = false ∧
        inspection.host = none ∧
        inspection.account = endpointAccount history ∧
        inspection.account.cut = jointForceCut ∧
        jointForceCut = [(.inr pending, (1 : Nat))] ∧
        cert.ledger = ([] : JointLedger) ∧
        cert.payment = denote cert.ledger ∧
        denote cert.ledger = 1 := by
  obtain ⟨pending, history, cert, inspection, inspected, returned, noHost, account,
      cut, forceShape, ledger, payDenote, denoted, _issued, _admitted, _rights, _halted⟩ :=
    pending_passive_package
  exact ⟨pending, history, cert, inspection, inspected, returned, noHost, account,
    cut, forceShape, ledger, payDenote, denoted⟩

theorem positive_suffix_advances_the_pending_cut :
    ∃ (pending : JointOccurrence)
      (history : History (pathMachine jointSpec jointStart) jointStart pending.state)
      (cert : SourceCertificate)
      (inspection : PassiveInspection),
      inspectpassive history (endpointAccount history) = .accept inspection ∧
        inspection.returned = false ∧
        inspection.host = none ∧
        inspection.account = endpointAccount history ∧
        inspection.account.cut = jointForceCut ∧
        cert.ledger = ([] : JointLedger) ∧
        cert.payment = denote cert.ledger ∧
        denote cert.ledger = 1 ∧
        cert.ledger ++ cert.ledger = cert.ledger ∧
        denote (cert.ledger ++ cert.ledger) =
          denote cert.ledger * denote cert.ledger ∧
        (resumeAccepted inspection.account cert.ledger 0).resumed =
          inspection.account.cut ∧
        (resumeAccepted inspection.account cert.ledger 3).resumed =
          contributions jointSource 6 jointInitial ∧
        (resumeAccepted inspection.account cert.ledger 3).produced =
          contributions jointSource 3 pending ∧
        (resumeAccepted inspection.account cert.ledger 3).resumed =
          (resumeAccepted inspection.account cert.ledger 3).produced ∧
        jointCutMark 3 ≠ jointCutMark 6 ∧
        inspection.account.cut ≠
          (resumeAccepted inspection.account cert.ledger 3).resumed ∧
        consumeAuthenticated history (endpointAccount history) 3 =
          .accept (resumeAccepted (endpointAccount history) cert.ledger 3) := by
  obtain ⟨pending, history, cert, inspection, inspected, returned, noHost, account,
      cut, forceShape, ledger, payDenote, denoted, issued, admitted, _rights, _halted⟩ :=
    pending_passive_package
  have hidden : cert.ledger ++ cert.ledger = cert.ledger := by
    simp [ledger]
  have denotedTwice : denote (cert.ledger ++ cert.ledger) =
      denote cert.ledger * denote cert.ledger :=
    denote_append _ _
  have zeroSame : (resumeAccepted inspection.account cert.ledger 0).resumed =
      inspection.account.cut := by
    simp only [resumeAccepted, weightedResume, cut, forceShape]
    rfl
  have threeResumed : (resumeAccepted inspection.account cert.ledger 3).resumed =
      contributions jointSource 6 jointInitial := by
    simp only [resumeAccepted, cut, jointForceCut]
    exact joint_resume_uses_the_recorded_composition 3 3
  have threeProduced : (resumeAccepted inspection.account cert.ledger 3).produced =
      contributions jointSource 3 pending := by
    simp only [resumeAccepted, cut, forceShape]
  have sameWeight : (resumeAccepted inspection.account cert.ledger 3).resumed =
      (resumeAccepted inspection.account cert.ledger 3).produced := by
    rw [threeResumed, threeProduced, ← joint_resume_uses_the_recorded_composition 3 3]
    have shape : contributions jointSource 3 jointInitial =
        [(.inr pending, (1 : Nat))] := by
      show jointForceCut = [(.inr pending, (1 : Nat))]
      exact forceShape
    rw [shape]
    unfold weightedResume
    rw [sequence_cons, sequence_nil, List.append_nil]
    exact one_weight_preserves_the_leaf _
  have marks : jointCutMark 3 ≠ jointCutMark 6 := by
    have mark3 : jointCutMark 3 =
        [(0, 1, ([] : List Nat), jointForceTrace, false)] :=
      joint_cut_marks.1
    have mark6 : jointCutMark 6 =
        [(0, 2, [0], jointEarnedTrace, false)] :=
      joint_cut_marks.2.1
    rw [mark3, mark6]
    decide
  have advanced : inspection.account.cut ≠
      (resumeAccepted inspection.account cert.ledger 3).resumed := by
    intro same
    apply marks
    have eqCuts : contributions jointSource 3 jointInitial =
        contributions jointSource 6 jointInitial := by
      show jointForceCut = contributions jointSource 6 jointInitial
      rw [← cut, same, threeResumed]
    simp only [jointCutMark, eqCuts]
  have resumed : consumeAuthenticated history (endpointAccount history) 3 =
      .accept (resumeAccepted (endpointAccount history) cert.ledger 3) :=
    explicit_resumption_uses_the_admitted_account history
      (endpointAccount history) 3 issued admitted
  exact ⟨pending, history, cert, inspection, inspected, returned, noHost, account,
    cut, ledger, payDenote, denoted, hidden, denotedTwice, zeroSame, threeResumed,
    threeProduced, sameWeight, marks, advanced, resumed⟩

/-- The admitted pending account keeps its cut, the paid empty ledger, the
force obligation, and the halted flag. -/
theorem pending_account_keeps_its_obligations :
    ∃ (pending : JointOccurrence)
      (history : History (pathMachine jointSpec jointStart) jointStart pending.state)
      (cert : SourceCertificate)
      (account : PresentedAccount),
      admitIssued cert account = .accept account ∧
        account = endpointAccount history ∧
        account.cut = jointForceCut ∧
        jointForceCut = [(.inr pending, (1 : Nat))] ∧
        cert.ledger = ([] : JointLedger) ∧
        cert.payment = denote cert.ledger ∧
        denote cert.ledger = 1 ∧
        cert.rights = {Right.force} ∧
        cert.halted = false ∧
        issueEarned history = some cert := by
  obtain ⟨pending, history, cert, inspection, _inspected, _returned, _noHost, accountEq,
      cut, forceShape, ledger, payDenote, denoted, issued, admitted, rights, halted⟩ :=
    pending_passive_package
  have admittedAccount : admitIssued cert inspection.account = .accept inspection.account := by
    rw [accountEq]
    exact admitted
  exact ⟨pending, history, cert, inspection.account, admittedAccount, accountEq, cut,
    forceShape, ledger, payDenote, denoted, rights, halted, issued⟩

/-- The issued joint return, retired through `applyShared`, keeps client `1`.
Client `1` still reads both source cells. The delivery list stays empty.
Payment stays the denotation `4` of `jointProductionLedger`. -/
theorem issued_return_retirement_names_the_surviving_client :
    (issueCut jointRun).bind (fun issued =>
      match pairHandles issued.handles with
      | none => none
      | some handles =>
          let start := freshShared (Production := JointLedger)
            (consumersOf jointValue) issued.registry handles
          let retired := applyShared issued.ledger (SharedAct.retire 0) start
          some (
            (retired.seats 0).live,
            (retired.seats 1).live,
            decide (retired.handles 1 = handles 1),
            (lookupJoint retired.registry (retired.handles 1)).1,
            unread retired.ownership.log 0,
            unread retired.ownership.log 1,
            retired.deliveries,
            denote issued.ledger,
            decide (issued.ledger = jointProductionLedger))) =
      some (false, true, true, some 0, [], [jointLeftCell, jointRightCell], [], 4, true) := by
  rfl

end JointSource

/-! ## Native obligation map

Checked against `src/prime_native_parallel.inc` and `src/prime_need.h` in the
prepared worktree. A row names a function and the obligation it has to meet.
It is not a refinement proof.
-/

structure NativeObligation where
  file : String
  functionName : String
  obligation : String
  deriving DecidableEq, Repr

def nativeObligations : List NativeObligation :=
  [ ⟨"src/prime_native_parallel.inc", "prime_native_need_claim_publish",
      "Publishes only when the cached atom is grounded INT, FLOAT, BOOL, STRING, BIGINT, or RATIONAL. Otherwise the claim becomes PRIME_NATIVE_NEED_CLAIM_FAILED. The scalar carries no pending fields or producer-local authority."⟩,
    ⟨"src/prime_native_parallel.inc", "prime_native_need_share_install",
      "Moves the active snapshot only along one lineage. Incomparable snapshots return false and do not merge."⟩,
    ⟨"src/prime_native_parallel.inc", "prime_native_need_share_barrier",
      "On CLAIM_VALUE, a successful install clears need_pending. If install returns false, the barrier stores claim->published in g_prime_need_share_value and sets g_prime_need_share_value_ready. That value is the published claim, not a distinct refused snapshot."⟩,
    ⟨"src/prime_native_parallel.inc", "prime_native_resume_shared_need_frames",
      "Resumes a waiting frame from a published or failed claim. A failed claim requeues the source demand in the receiver's retained world and is not an empty answer."⟩,
    ⟨"src/prime_need.h", "prime_need_snapshot_resolve_forwarded_value",
      "Records the producer's exact immutable update and does not infer provenance by Atom equality."⟩,
    ⟨"src/prime_need.h", "prime_need_snapshot_copy_with_session",
      "On refusal the source snapshot stays intact."⟩ ]

theorem native_obligations_name_the_scalar_rendezvous :
    nativeObligations.length = 6 ∧
      (nativeObligations[0]?.map NativeObligation.functionName) =
        some "prime_native_need_claim_publish" ∧
      (nativeObligations[2]?.map NativeObligation.functionName) =
        some "prime_native_need_share_barrier" := by
  simp [nativeObligations]

/-! ## Paid-account custody

The admitted account and its source certificate are the first component of a
product world. Delivery observations are the second component. Cancelling
the host before any delivery drops the retained seat and keeps both
components. These names are not compiled-code verification, and retiring a
handle does not free native storage.
-/

open Mettapedia.Machines.OwnedPullDriver
open Owned
open Host

structure PaidCustody where
  account : PresentedAccount
  certificate : SourceCertificate
  obligations : List NativeObligation

def frameAct {Observation : Type} (earned : Observation) :
    Fin 2 → PaidCustody × List Observation → PaidCustody × List Observation :=
  fun _client world => (world.1, world.2 ++ [earned])

/-- Every reachable framed host keeps the custody it was given. Its
observation list is the delivered list, one `earned` per delivery. The
induction follows `begin`, `submit`, and `cancel`. It does not use
`Reached.accounts`. -/
theorem reachable_custody_frame
    {Observation : Type} (earned : Observation) (custody : PaidCustody)
    (ownership : Configuration CellId Nat 2) (registry : JointIssuedRegistry)
    (handles : Fin 2 → JointIssuedHandle)
    {host : Host (SharedConsumers Observation) (Fin 2) (PaidCustody × List Observation)}
    (reached : Reached (sharedSystem earned) (frameAct earned)
      (custody, ([] : List Observation))
      (freshShared ownership registry handles) host) :
    host.world = (custody, host.delivered.map (fun _ => earned)) ∧
      (∀ state, host.retained = some state → state.deliveries = host.delivered) ∧
      ∀ ticket,
        (cancel ticket host).delivered = host.delivered ∧
          (cancel ticket host).world = host.world := by
  induction reached with
  | begin =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [begin, sharedSystem, committedShared, freshShared, interpret_nil,
          List.map_nil]
      · intro state retained
        simp only [begin] at retained
        cases retained
        simp [begin, sharedSystem, committedShared, freshShared]
      · intro ticket
        exact cancel_keeps_observations ticket _
  | @submit host ticket op _ ih =>
      by_cases current : ticket = host.epoch
      · cases retained : host.retained with
        | none =>
            rw [submit_retired (sharedSystem earned) (frameAct earned) ticket op retained]
            exact ih
        | some state =>
            subst current
            have preserved := ih.2.1 state retained
            have worldNext :
                interpret (frameAct earned)
                    (((sharedSystem earned).committed
                        ((sharedSystem earned).apply op state)).drop
                      ((sharedSystem earned).committed state).length)
                    host.world =
                  (custody,
                    (host.delivered ++
                        (((sharedSystem earned).committed
                            ((sharedSystem earned).apply op state)).drop
                          ((sharedSystem earned).committed state).length)).map
                      (fun _ => earned)) := by
              have worldEq : host.world =
                  (custody, host.delivered.map (fun _ => earned)) := ih.1
              unfold frameAct
              rw [worldEq]
              simp only [Mettapedia.Machines.OwnedPullDriver.interpret_pair_appends,
                List.map_append]
            rw [submit_current (sharedSystem earned) (frameAct earned) op retained]
            have deliveredEq : host.delivered ++
                (((sharedSystem earned).committed
                    ((sharedSystem earned).apply op state)).drop
                  ((sharedSystem earned).committed state).length) =
                (applyShared earned op state).deliveries := by
              simp only [sharedSystem, committedShared]
              rw [← preserved]
              exact (applyShared_deliveries_split earned op state).symm
            refine ⟨worldNext, ?_, ?_⟩
            · intro nextState sameState
              cases sameState
              exact deliveredEq.symm
            · intro nextTicket
              exact cancel_keeps_observations nextTicket _
      · rw [submit_stale (sharedSystem earned) (frameAct earned) op current]
        exact ih
  | @cancel host ticket _ ih =>
      by_cases current : ticket = host.epoch
      · cases retained : host.retained with
        | none =>
            rw [cancel_retired ticket retained]
            exact ih
        | some _state =>
            subst current
            rw [cancel_current retained]
            refine ⟨ih.1, ?_, ?_⟩
            · intro _nextState absent
              cases absent
            · intro nextTicket
              exact cancel_keeps_observations nextTicket _
      · rw [cancel_stale current]
        exact ih

/-- Cancellation before any delivery keeps the admitted account, its paid
ledger, its rights, and the obligation list. The observation component and
the delivered list are empty. -/
theorem cancellation_before_delivery_retains_custody
    {Observation : Type} (earned : Observation) (custody : PaidCustody)
    (ownership : Configuration CellId Nat 2) (registry : JointIssuedRegistry)
    (handles : Fin 2 → JointIssuedHandle)
    {host : Host (SharedConsumers Observation) (Fin 2) (PaidCustody × List Observation)}
    (reached : Reached (sharedSystem earned) (frameAct earned)
      (custody, ([] : List Observation))
      (freshShared ownership registry handles) host)
    (empty : host.delivered = []) (ticket : Nat) :
    (cancel ticket host).world.1 = custody ∧
      (cancel ticket host).world.1.account = custody.account ∧
      (cancel ticket host).world.1.account.cut = custody.account.cut ∧
      (cancel ticket host).world.1.certificate.ledger = custody.certificate.ledger ∧
      (cancel ticket host).world.1.certificate.payment = custody.certificate.payment ∧
      (cancel ticket host).world.1.certificate.rights = custody.certificate.rights ∧
      (cancel ticket host).world.1.obligations = custody.obligations ∧
      (cancel ticket host).world.2 = ([] : List Observation) ∧
      (cancel ticket host).delivered = [] := by
  obtain ⟨worldEq, _retainedDeliveries, cancelKeeps⟩ :=
    reachable_custody_frame earned custody ownership registry handles reached
  obtain ⟨deliveredKept, worldKept⟩ := cancelKeeps ticket
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [worldKept, worldEq, empty]
  · rw [worldKept, worldEq, empty]
  · rw [worldKept, worldEq, empty]
  · rw [worldKept, worldEq, empty]
  · rw [worldKept, worldEq, empty]
  · rw [worldKept, worldEq, empty]
  · rw [worldKept, worldEq, empty]
  · rw [worldKept, worldEq, empty]
    simp [List.map_nil]
  · rw [deliveredKept, empty]

/-- The admitted pending certificate is the custody of a framed host.
Cancelling that host before any delivery keeps the empty paid ledger, the
complete pending cut, the force right, and the six native obligation names.
The observation list is empty, and that list is not the grade-`1` factor. -/
theorem pending_cancellation_retains_the_paid_account
    (ownership : Configuration CellId Nat 2) (registry : JointIssuedRegistry)
    (handles : Fin 2 → JointIssuedHandle) :
    ∃ (custody : PaidCustody)
      (host : Host (SharedConsumers JointLedger) (Fin 2) (PaidCustody × List JointLedger)),
      admitIssued custody.certificate custody.account = .accept custody.account ∧
        custody.account.cut = jointForceCut ∧
        custody.certificate.ledger = ([] : JointLedger) ∧
        custody.certificate.payment = denote custody.certificate.ledger ∧
        denote custody.certificate.ledger = 1 ∧
        custody.certificate.rights = {Right.force} ∧
        custody.certificate.halted = false ∧
        custody.obligations = nativeObligations ∧
        custody.obligations.length = 6 ∧
        host.delivered = [] ∧
        host.world = (custody, ([] : List JointLedger)) ∧
        (cancel host.epoch host).retained = none ∧
        (cancel host.epoch host).delivered = [] ∧
        (cancel host.epoch host).world.1.certificate.ledger = custody.certificate.ledger ∧
        (cancel host.epoch host).world.1.account.cut = jointForceCut ∧
        (cancel host.epoch host).world.1.certificate.rights = {Right.force} ∧
        (cancel host.epoch host).world.1.obligations = nativeObligations ∧
        (cancel host.epoch host).world.2 = [] ∧
        custody.certificate.ledger ≠ [jointUnitFactor] := by
  obtain ⟨_pending, _history, cert, account, admitted, _accountEq, cut, _shape, ledger,
      payment, denoted, rights, halted, _issued⟩ := pending_account_keeps_its_obligations
  let custody : PaidCustody := ⟨account, cert, nativeObligations⟩
  let earned := cert.ledger
  let origin : PaidCustody × List JointLedger := (custody, [])
  let start := freshShared (Production := JointLedger) ownership registry handles
  let host := begin (sharedSystem earned) (frameAct earned) start origin
  have reached : Reached (sharedSystem earned) (frameAct earned) origin start host :=
    Reached.begin
  have empty : host.delivered = [] := by
    simp [host, begin, sharedSystem, committedShared, start, freshShared]
  have world0 : host.world = origin := by
    simp [host, begin, sharedSystem, committedShared, start, freshShared, origin, interpret_nil]
  have retained0 : host.retained = some start := by
    simp [host, begin]
  obtain ⟨cust, _account, _sameCut, ledgerKept, _paymentKept, rightsKept, obligationsKept,
      observations, delivered⟩ :=
    cancellation_before_delivery_retains_custody earned custody ownership registry handles
      reached empty host.epoch
  have dropped : (cancel host.epoch host).retained = none := by
    rw [cancel_current retained0]
  refine ⟨custody, host, admitted, cut, ledger, payment, denoted, rights, halted,
      by simp [custody], by simpa [custody] using native_obligations_name_the_scalar_rendezvous.1,
      empty, world0, dropped, delivered, ledgerKept, ?_, ?_, obligationsKept, observations, ?_⟩
  · rw [cust]
    exact cut
  · rw [rightsKept]
    exact rights
  · rw [ledger]
    decide

/-- Retiring client `0` on a reached framed host keeps client `1` authenticated
and leaves the custody component unchanged. Delivery observations stay the
second component. The proof follows `Reached` and `submit`; it does not use
`Reached.accounts`. -/
theorem reachable_framed_retirement_preserves_the_named_client
    {Observation : Type} (earned : Observation) (custody : PaidCustody)
    (ownership : Configuration CellId Nat 2) (registry : JointIssuedRegistry)
    (handles : Fin 2 → JointIssuedHandle)
    (different : (handles 0).row ≠ (handles 1).row)
    {host : Host (SharedConsumers Observation) (Fin 2) (PaidCustody × List Observation)}
    (reached : Reached (sharedSystem earned) (frameAct earned)
      (custody, ([] : List Observation))
      (freshShared ownership registry handles) host)
    (ticket : Nat) {state : SharedConsumers Observation}
    (retained : host.retained = some state)
    (current : ticket = host.epoch)
    (live0 : (state.seats 0).live = true)
    (live1 : (state.seats 1).live = true)
    (authenticated : jointAuthenticated registry (handles 1))
    {next : JointIssuedRegistry} {cleared : JointIssuedHandle} {visits : Nat}
    (released : releaseJoint state.registry (state.handles 0) =
      (some (next, cleared), visits)) :
    ∃ retired : SharedConsumers Observation,
      (submit (sharedSystem earned) (frameAct earned) ticket (SharedAct.retire 0) host).retained =
        some retired ∧
        (retired.seats 0).live = false ∧
        (retired.seats 1).live = true ∧
        retired.handles 1 = handles 1 ∧
        jointAuthenticated retired.registry (retired.handles 1) ∧
        unread retired.ownership.log 0 = [] ∧
        unread retired.ownership.log 1 = unread ownership.log 1 ∧
        (submit (sharedSystem earned) (frameAct earned) ticket (SharedAct.retire 0) host).delivered =
          host.delivered ∧
        (submit (sharedSystem earned) (frameAct earned) ticket (SharedAct.retire 0) host).world =
          host.world ∧
        (submit (sharedSystem earned) (frameAct earned) ticket (SharedAct.retire 0) host).world.1 =
          custody ∧
        (submit (sharedSystem earned) (frameAct earned) ticket
          (SharedAct.retire 0) host).world.1.certificate.ledger =
          custody.certificate.ledger ∧
        (submit (sharedSystem earned) (frameAct earned) ticket
          (SharedAct.retire 0) host).world.1.certificate.payment =
          custody.certificate.payment ∧
        (submit (sharedSystem earned) (frameAct earned) ticket
          (SharedAct.retire 0) host).world.1.certificate.rights =
          custody.certificate.rights ∧
        (submit (sharedSystem earned) (frameAct earned) ticket
          (SharedAct.retire 0) host).world.1.account.cut =
          custody.account.cut ∧
        (submit (sharedSystem earned) (frameAct earned) ticket
          (SharedAct.retire 0) host).world.1.account.ledger =
          custody.account.ledger := by
  obtain ⟨worldEq, _nodup, retainedLaw, _cancelKept⟩ :=
    reachable_action_law earned (frameAct earned)
      (fun delivered => (custody, delivered.map (fun _ => earned)))
      (custody, ([] : List Observation)) rfl
      (by
        intro delivered suffix
        unfold frameAct
        simp only [Mettapedia.Machines.OwnedPullDriver.interpret_pair_appends,
          List.map_append])
      ownership registry handles different reached
  obtain ⟨_stateDelivered, law⟩ := retainedLaw state retained
  obtain ⟨dead, alive, handleEq, auth, unreadZero, unreadOne, delSame, _registryEq⟩ :=
    retire_one_client_preserves_the_named_survivor earned
      (freshShared ownership registry handles) state law
      (by simpa [freshShared] using different) live0 live1
      (by simpa [freshShared] using authenticated) released
  have freshNil :
      (((sharedSystem earned).committed
          ((sharedSystem earned).apply (SharedAct.retire 0) state)).drop
        ((sharedSystem earned).committed state).length) = [] := by
    simp only [sharedSystem, committedShared, delSame, List.drop_length]
  have submitted := submit_current (sharedSystem earned) (frameAct earned)
    (SharedAct.retire 0) retained
  rw [← current] at submitted
  simp only [freshNil, interpret_nil, List.append_nil] at submitted
  have worldKept :
      (submit (sharedSystem earned) (frameAct earned) ticket (SharedAct.retire 0) host).world =
        host.world := by
    simp [submitted]
  have custodyKept : host.world.1 = custody := by
    rw [worldEq]
  refine ⟨applyShared earned (SharedAct.retire 0) state, ?_, dead, alive, ?_, auth,
      unreadZero, ?_, ?_, worldKept, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [submitted]
    simp [sharedSystem]
  · rw [handleEq]
    simp [freshShared]
  · rw [unreadOne]
    simp [freshShared]
  · simp [submitted]
  · rw [worldKept, custodyKept]
  · rw [worldKept, custodyKept]
  · rw [worldKept, custodyKept]
  · rw [worldKept, custodyKept]
  · rw [worldKept, custodyKept]
  · rw [worldKept, custodyKept]

open Mettapedia.GSLT.Causality.OccurrenceMachineHistory
open Mettapedia.Machines.BranchLocalNeed.NeedInferenceControl.Reference

/-- The admitted returned certificate is the custody of a reached shared host
built from that certificate's registry and handles. `Host.submit` of
`SharedAct.retire 0` keeps client `1` authenticated, and the nonempty paid
ledger, returned cut, and inspect right stay in the custody component.
`resumeAccepted` on that same account at `suffix` produces no new cut.
`halted_inspection_keeps_the_returned_residual` gives that empty production
and the same returned cut for every budget. The observation list stays
empty. The obligation field is empty: the six native names are not this
custody evidence. -/
theorem returned_retirement_keeps_the_nonempty_paid_account (suffix : Nat) :
    ∃ (target : JointMachine)
      (history : History (pathMachine jointSpec jointStart) jointStart target)
      (cert : SourceCertificate)
      (account : PresentedAccount)
      (accepted : ResumedAccount)
      (handles : Fin 2 → JointIssuedHandle)
      (host : Host (SharedConsumers JointLedger) (Fin 2) (PaidCustody × List JointLedger))
      (retired : SharedConsumers JointLedger),
      issueCut jointRun = some cert ∧
        issueEarned history = some cert ∧
        account = endpointAccount history ∧
        admitIssued cert account = .accept account ∧
        cert.ledger = jointProductionLedger ∧
        cert.payment = denote cert.ledger ∧
        denote cert.ledger = 4 ∧
        cert.rights = {Right.inspect} ∧
        cert.halted = true ∧
        cert.roots = [jointLeftCell, jointRightCell] ∧
        account.ledger = jointProductionLedger ∧
        account.held = {Right.inspect} ∧
        account.requested = {Right.inspect} ∧
        account.cut =
          [(Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence), 4)] ∧
        pairHandles cert.handles = some handles ∧
        (handles 0).row ≠ (handles 1).row ∧
        accepted = resumeAccepted account cert.ledger suffix ∧
        accepted.produced = [] ∧
        accepted.resumed = account.cut ∧
        accepted.delivered = jointProductionLedger ∧
        host.delivered = [] ∧
        host.world.2 = ([] : List JointLedger) ∧
        (submit (sharedSystem cert.ledger) (frameAct cert.ledger) host.epoch
          (SharedAct.retire 0) host).retained = some retired ∧
        (retired.seats 0).live = false ∧
        (retired.seats 1).live = true ∧
        retired.handles 1 = handles 1 ∧
        jointAuthenticated retired.registry (retired.handles 1) ∧
        unread retired.ownership.log 0 = [] ∧
        unread retired.ownership.log 1 = [jointLeftCell, jointRightCell] ∧
        (submit (sharedSystem cert.ledger) (frameAct cert.ledger) host.epoch
          (SharedAct.retire 0) host).delivered = [] ∧
        (submit (sharedSystem cert.ledger) (frameAct cert.ledger) host.epoch
          (SharedAct.retire 0) host).world.1.certificate.ledger =
          jointProductionLedger ∧
        (submit (sharedSystem cert.ledger) (frameAct cert.ledger) host.epoch
          (SharedAct.retire 0) host).world.1.certificate.payment = 4 ∧
        (submit (sharedSystem cert.ledger) (frameAct cert.ledger) host.epoch
          (SharedAct.retire 0) host).world.1.certificate.rights = {Right.inspect} ∧
        (submit (sharedSystem cert.ledger) (frameAct cert.ledger) host.epoch
          (SharedAct.retire 0) host).world.1.account.cut = account.cut ∧
        (submit (sharedSystem cert.ledger) (frameAct cert.ledger) host.epoch
          (SharedAct.retire 0) host).world.2 = ([] : List JointLedger) ∧
        jointProductionLedger ≠ [] := by
  obtain ⟨target, history, cert, accepted, cutIssued, issuedHistory, halted, control,
      _left, _right, resumedAdmit, _produced, deliveredLedger, _sameCut, ledgerEq, payment4,
      roots, denoted, _reversed⟩ := returned_fuel_fifteen_inspection suffix
  have consumed := earned_endpoint_is_consumed history suffix issuedHistory
  have inspected :=
    halted_inspection_keeps_the_returned_residual history suffix issuedHistory halted
  have acceptedEq : accepted =
      resumeAccepted (endpointAccount history) cert.ledger suffix := by
    have step : RetainedAdmit.accept accepted =
        RetainedAdmit.accept
          (resumeAccepted (endpointAccount history) cert.ledger suffix) := by
      rw [← resumedAdmit]
      exact consumed.1
    injection step with acceptedEq
  let account : PresentedAccount := endpointAccount history
  have admitted : admitIssued cert account = .accept account :=
    earned_endpoint_is_admitted issuedHistory
  have rights : cert.rights = {Right.inspect} := by
    have mapped := source_issue_reads_the_three_cuts.2.2.2.2.2.1
    rw [cutIssued] at mapped
    exact Option.some.inj mapped
  have haltedCert : cert.halted = true := by
    have view := source_issue_reads_the_three_cuts.2.2.1
    rw [cutIssued] at view
    have same := Option.some.inj view
    simp only [cutView] at same
    exact congrArg (fun view => view.2.2.2.2.1) same
  have accountLedger : account.ledger = jointProductionLedger := by
    change earnedLedger history = jointProductionLedger
    rw [← consumed.2.1, ledgerEq]
  have heldRights : account.held = {Right.inspect} := by
    simp [account, endpointAccount, requiredRights, control]
  have requestedRights : account.requested = {Right.inspect} := by
    simp [account, endpointAccount, requiredRights, control]
  have earnedDenote : denote (earnedLedger history) = 4 := by
    rw [← consumed.2.1, denoted]
  have cutFour : account.cut =
      [(Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence), 4)] := by
    simp only [account, endpointAccount, halted, earnedDenote, ite_true]
  have packed :
      (issueCut jointRun).bind (fun issued =>
        match pairHandles issued.handles with
        | none => none
        | some handles =>
            match releaseJoint issued.registry (handles 0) with
            | (some _pair, visits) =>
                some (
                  decide ((handles 0).row ≠ (handles 1).row),
                  (lookupJoint issued.registry (handles 1)).1,
                  visits)
            | (none, _) => none) = some (true, some 1, 1) := by
    rfl
  rw [cutIssued] at packed
  match hpair : pairHandles cert.handles with
  | none => simp [hpair] at packed
  | some handles =>
      match hrel : releaseJoint cert.registry (handles 0) with
      | (none, _) => simp [hpair, hrel] at packed
      | (some pair, visits) =>
          rcases pair with ⟨next, cleared⟩
          simp [hpair, hrel, Option.some.injEq, Prod.mk.injEq] at packed
          obtain ⟨rowsDec, look, _visitsEq⟩ := packed
          have different : (handles 0).row ≠ (handles 1).row := rowsDec
          have authenticated : jointAuthenticated cert.registry (handles 1) :=
            (Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.lookup_authenticates
              cert.registry (handles 1)).mp (by rw [look]; decide)
          let custody : PaidCustody := ⟨account, cert, []⟩
          let earned := cert.ledger
          let ownership := configurationOfRoots cert.roots
          let start := freshShared (Production := JointLedger) ownership cert.registry handles
          let origin : PaidCustody × List JointLedger := (custody, [])
          let host := begin (sharedSystem earned) (frameAct earned) start origin
          have reached : Reached (sharedSystem earned) (frameAct earned) origin start host :=
            Reached.begin
          have empty : host.delivered = [] := by
            simp [host, begin, sharedSystem, committedShared, start, freshShared]
          have world0 : host.world = origin := by
            simp [host, begin, sharedSystem, committedShared, start, freshShared, origin,
              interpret_nil]
          have retained0 : host.retained = some start := by
            simp [host, begin]
          have live0 : (start.seats 0).live = true := by
            simp [start, freshShared, freshSeat]
          have live1 : (start.seats 1).live = true := by
            simp [start, freshShared, freshSeat]
          have released : releaseJoint start.registry (start.handles 0) =
              (some (next, cleared), visits) := by
            simp [start, freshShared, hrel]
          have ownEq : ownership = consumersOf jointValue := by
            simp [ownership, roots, consumersOf_uses_configurationOfRoots, jointValue,
              occurrencesOf, configurationOfRoots]
          obtain ⟨retired, retainedRet, dead, alive, handleKept, auth, unreadZero, unreadOne,
              deliveredKept, worldKept, _custodyKept, ledgerKept, paymentKept, rightsKept,
              cutKept, _accountLedgerKept⟩ :=
            reachable_framed_retirement_preserves_the_named_client earned custody ownership
              cert.registry handles different reached host.epoch retained0 rfl live0 live1
              authenticated released
          have unreadCells : unread ownership.log 1 = [jointLeftCell, jointRightCell] := by
            rw [ownEq]
            exact retiring_one_owner_keeps_the_other.2.2.2
          have observations : host.world.2 = ([] : List JointLedger) := by
            simp [world0, origin]
          have resumedCut : accepted.resumed = account.cut := by
            rw [acceptedEq]
            exact inspected.2.2.2.2.2.2.1
          have producedNil : accepted.produced = [] := by
            rw [acceptedEq]
            exact inspected.2.1
          have deliveredPaid : accepted.delivered = jointProductionLedger := deliveredLedger
          refine ⟨target, history, cert, account, accepted, handles, host, retired,
              cutIssued, issuedHistory, rfl, admitted, ledgerEq, consumed.2.2.1, denoted,
              rights, haltedCert, roots, accountLedger, heldRights, requestedRights, cutFour,
              hpair, different, acceptedEq, producedNil, resumedCut, deliveredPaid, empty,
              observations, retainedRet, dead, alive, handleKept, auth, unreadZero, ?_,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [unreadOne]
            exact unreadCells
          · rw [deliveredKept, empty]
          · rw [ledgerKept, ledgerEq]
          · rw [paymentKept, payment4]
          · rw [rightsKept, rights]
          · rw [cutKept]
          · rw [worldKept, observations]
          · decide

/-! ### Passive ordered factors

`Fold.complete_exact` is the one cursor: its completed accumulator is
`items.foldl consume initial`. `foldl_snoc` is that fold for one-item
appends, so duplicates and occurrence order stay in the list.
`readGraph` is the same cursor at `readReceipt` on the chronological
receipt nodes. An issued certificate's factor list is `earnedLedger`,
the production ledger of the history, not the denotation of that ledger.
-/

theorem passive_reader_is_the_completed_fold (nodes : List JointReceiptNode) :
    Mettapedia.Machines.Cursor.advance
        (Mettapedia.Machines.Cursor.Sequence.tails JointReceiptNode)
        (Mettapedia.Machines.Cursor.Fold.client readReceipt) (fun _ _ => 1)
        (nodes.reverse.length + 2)
        (Mettapedia.Machines.Cursor.Fold.start
          (Mettapedia.Machines.Cursor.Sequence.tails JointReceiptNode)
          readReceipt nodes.reverse (⟨[], [], []⟩ : GraphAccount)) =
      (nodes.reverse.length + 1,
        .done ⟨(), readGraph nodes, []⟩) := by
  simpa [readGraph] using
    Mettapedia.Machines.Cursor.Fold.complete_exact readReceipt nodes.reverse
      (⟨[], [], []⟩ : GraphAccount)

theorem issued_passive_factors_are_the_earned_ledger
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    {cert : SourceCertificate}
    (issued : issueEarned history = some cert) :
    (readGraph cert.receipts.nodes).factors = earnedLedger history ∧
      cert.ledger = earnedLedger history := by
  unfold issueEarned at issued
  split at issued
  · simp at issued
  · rename_i rows hrows
    cases issued
    have gate := retainedRows_success hrows
    exact ⟨gate.2.2.2.2.1, rfl⟩

theorem nonempty_duplicate_factors_stay_in_order :
    Mettapedia.Machines.Cursor.advance
        (Mettapedia.Machines.Cursor.Sequence.tails
          (Factor (CellId × ReceiptId)
            (Produced (Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Val CellId)
              Unit Unit) Nat))
        (Mettapedia.Machines.Cursor.Fold.client
          (fun state factor => state ++ [factor])) (fun _ _ => 1) 4
        (Mettapedia.Machines.Cursor.Fold.start
          (Mettapedia.Machines.Cursor.Sequence.tails
            (Factor (CellId × ReceiptId)
              (Produced (Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Val CellId)
                Unit Unit) Nat))
          (fun state factor => state ++ [factor])
          [jointLeftFactor, jointLeftFactor] ([] : JointLedger)) =
      (3, .done ⟨(), [jointLeftFactor, jointLeftFactor], []⟩) ∧
    ([jointLeftFactor, jointLeftFactor] : JointLedger) ≠ [] ∧
    ([jointLeftFactor, jointLeftFactor] : JointLedger) ≠ [jointLeftFactor] ∧
    denote ([jointLeftFactor, jointLeftFactor] : JointLedger) =
      denote jointProductionLedger ∧
    ([jointLeftFactor, jointLeftFactor] : JointLedger) ≠ jointProductionLedger ∧
    jointLeftFactor.coefficient = jointRightFactor.coefficient ∧
    denote ([jointLeftFactor] : JointLedger) = denote [jointRightFactor] ∧
    denote jointReversedLedger = denote jointProductionLedger ∧
    denote jointDeduplicatedLedger = denote jointProductionLedger ∧
    ([jointLeftFactor, jointRightFactor] : JointLedger).foldl
        (fun state factor => state ++ [factor]) [] = jointProductionLedger ∧
    ([jointRightFactor, jointLeftFactor] : JointLedger).foldl
        (fun state factor => state ++ [factor]) [] = jointReversedLedger := by
  refine ⟨?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact Mettapedia.Machines.Cursor.PermutationInvariantFold.completed_snoc_is_concatenation
      [jointLeftFactor, jointLeftFactor] ([] : JointLedger)
  · decide
  · decide
  · decide
  · rw [Mettapedia.Machines.Cursor.PermutationInvariantFold.foldl_snoc]
    rfl
  · rw [Mettapedia.Machines.Cursor.PermutationInvariantFold.foldl_snoc]
    rfl

theorem reversed_and_deduplicated_ledgers_are_refused :
    (issueCut jointRun).bind (fun issued =>
        some (issued.ledger,
          admitTag issued jointRun jointReversedLedger issued.roots
            {Right.inspect} {Right.inspect} none,
          admitTag issued jointRun jointDeduplicatedLedger issued.roots
            {Right.inspect} {Right.inspect} none,
          (admitIssued issued ⟨jointRun, jointReversedLedger, issued.roots,
            {Right.inspect}, {Right.inspect}, none⟩).kept.ledger,
          (admitIssued issued ⟨jointRun, jointDeduplicatedLedger, issued.roots,
            {Right.inspect}, {Right.inspect}, none⟩).kept.ledger)) =
      some (jointProductionLedger, 5, 5, jointReversedLedger,
        jointDeduplicatedLedger) := by
  rfl

/-- Inspection of the returned cut adds no production at any suffix budget.
The passive reader is the completed `Fold` cursor on that certificate's
receipt nodes, started from the empty graph account. Its factors are the
earned ledger in occurrence order. The framed observation list stays empty
and is not that ledger. -/
theorem returned_inspection_adds_no_production (suffix : Nat) :
    ∃ (target : JointMachine)
      (history : History (pathMachine jointSpec jointStart) jointStart target)
      (cert : SourceCertificate)
      (account : PresentedAccount)
      (accepted : ResumedAccount)
      (host : Host (SharedConsumers JointLedger) (Fin 2)
        (PaidCustody × List JointLedger)),
      issueCut jointRun = some cert ∧
        issueEarned history = some cert ∧
        Mettapedia.Machines.Cursor.advance
            (Mettapedia.Machines.Cursor.Sequence.tails JointReceiptNode)
            (Mettapedia.Machines.Cursor.Fold.client readReceipt) (fun _ _ => 1)
            (cert.receipts.nodes.reverse.length + 2)
            (Mettapedia.Machines.Cursor.Fold.start
              (Mettapedia.Machines.Cursor.Sequence.tails JointReceiptNode)
              readReceipt cert.receipts.nodes.reverse
              (⟨[], [], []⟩ : GraphAccount)) =
          (cert.receipts.nodes.reverse.length + 1,
            .done ⟨(), readGraph cert.receipts.nodes, []⟩) ∧
        (readGraph cert.receipts.nodes).factors = earnedLedger history ∧
        earnedLedger history = jointProductionLedger ∧
        cert.ledger = [jointLeftFactor, jointRightFactor] ∧
        jointLeftFactor.coefficient = jointRightFactor.coefficient ∧
        (readGraph cert.receipts.nodes).factors ≠ jointReversedLedger ∧
        (readGraph cert.receipts.nodes).factors ≠ jointDeduplicatedLedger ∧
        denote jointReversedLedger =
          denote (readGraph cert.receipts.nodes).factors ∧
        denote jointDeduplicatedLedger =
          denote (readGraph cert.receipts.nodes).factors ∧
        account = endpointAccount history ∧
        accepted = resumeAccepted account cert.ledger suffix ∧
        accepted.produced = [] ∧
        accepted.resumed = account.cut ∧
        accepted.delivered = jointProductionLedger ∧
        account.cut =
          [(Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence), 4)] ∧
        host.delivered = [] ∧
        host.world.2 = ([] : List JointLedger) ∧
        (submit (sharedSystem cert.ledger) (frameAct cert.ledger) host.epoch
            (SharedAct.retire 0) host).world.1.certificate.ledger =
          jointProductionLedger ∧
        (submit (sharedSystem cert.ledger) (frameAct cert.ledger) host.epoch
            (SharedAct.retire 0) host).world.2 = ([] : List JointLedger) ∧
        jointProductionLedger ≠ [] := by
  obtain ⟨target, history, cert, account, accepted, _handles, host, _retired,
      cutIssued, issuedHistory, accountEq, _admitted, ledgerEq, _payment, _denoted,
      _rights, _haltedCert, _roots, _accountLedger, _held, _requested, cutFour,
      _paired, _different, acceptedEq, producedNil, resumedCut, deliveredPaid,
      emptyDelivered, observations, _retainedRet, _dead, _alive, _handleKept,
      _auth, _unreadZero, _unreadOne, _submitDelivered, custodyLedger, _paymentKept,
      _rightsKept, _cutKept, submitObservations, nonempty⟩ :=
    returned_retirement_keeps_the_nonempty_paid_account suffix
  have read := issued_passive_factors_are_the_earned_ledger history issuedHistory
  refine ⟨target, history, cert, account, accepted, host, cutIssued, issuedHistory,
      passive_reader_is_the_completed_fold cert.receipts.nodes,
      read.1, read.2.symm.trans ledgerEq, ?_, rfl, ?_, ?_, ?_, ?_, accountEq, acceptedEq,
      producedNil, resumedCut, deliveredPaid, cutFour, emptyDelivered, observations,
      custodyLedger, submitObservations, nonempty⟩
  · rw [ledgerEq, jointProductionLedger]
  · rw [read.1, ← read.2, ledgerEq]
    exact joint_prefix_replays_are_the_source_ledgers.2.2.2.2.2.2.2.2.1
  · rw [read.1, ← read.2, ledgerEq]
    decide
  · rw [read.1, ← read.2, ledgerEq]
    exact nonempty_duplicate_factors_stay_in_order.2.2.2.2.2.2.2.1
  · rw [read.1, ← read.2, ledgerEq]
    exact nonempty_duplicate_factors_stay_in_order.2.2.2.2.2.2.2.2.1

/-! ### Recording erasure and reader work

The authored computation is `occurrenceSystem jointSpec`, started at
`jointStart`. Its accepted request schedule is the fixed breadth-first
controller. Recording off and recording on are the existing
`Recording.controller` at that same schedule. `run_erasure` is the comparison:
erasing the recorder returns the unrecorded run, including its answers and
retained frontier. `disabled_record` is the off mode, and it stores no prefix.
A recorder enabled only after that disabled cut has a fresh prefix, so its
complete history is the suffix. Those recording facts stay on the source
runs above. `framedReaderInspection` is a separate transition on a host and
an arbitrary cost prefix: it reads that host's certificate receipts with the
completed reader, appends one declared `costRead` through
`NativeCostLedger.inspect`, and submits `SharedAct.inspect` through
`frameAct`. The prefix is not reset. A second inspection keeps the first
charge and the same certificate and cut. The inspection writes no production
occurrence and allocates no recording prefix. One `costRead` is a logical
observation charge, not a measured traversal bound and not a compiled-code
proof. `NativeCostLedger.inspect` is given its event identity. The unit
counts `+ 1` and `+ 2` do not make that identity fresh, and they are not
unique or authentic physical issuance. Freshness is
`unique_append_event` under `Unique` and a fresh identity, not this fee.
`NeedInferenceControl.Erasure.demanded_breadthFirst_run_erases` is the separate
receipt-erased realization of this spec. It is not compiled-code verification.
-/

open Mettapedia.GSLT.Core.InferenceControl.Recording

def jointAuthoredSchedule :
    Controller JointOccurrence
      (Produced (Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Val CellId)
        Unit Unit × List Nat) Unit :=
  Controller.fixed Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst

def jointNodeObserve :
    Unit → JointOccurrence →
      Option (Produced (Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Val CellId)
        Unit Unit × List Nat) →
      List JointOccurrence → JointOccurrence :=
  fun _ node _ _ => node

def jointAuthoredSnapshot :
    Snapshot JointOccurrence
      (Produced (Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Val CellId)
        Unit Unit × List Nat) Unit :=
  Snapshot.initial jointAuthoredSchedule [WorkOccurrence.root jointStart]

def jointPlainRun (fuel : Nat) :=
  Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule fuel
    jointAuthoredSnapshot

def jointRecordedRun (capacity : Option Nat) (fuel : Nat) :=
  Snapshot.run (occurrenceSystem jointSpec)
    (controller jointAuthoredSchedule jointNodeObserve capacity) fuel
    (start jointAuthoredSnapshot capacity)

/-- Recording turned on at the erased one-step disabled cut. Its prefix does
not contain the request already selected while recording was off. -/
def jointLateRecordedRun :=
  Snapshot.run (occurrenceSystem jointSpec)
    (controller jointAuthoredSchedule jointNodeObserve (some 2)) 1
    (start (erase (jointRecordedRun none 1)) (some 2))

theorem joint_recording_successors_are_the_source_successors :
    (successors jointSpec jointCoefficient jointInitial).map Prod.fst =
      (occurrenceSystem jointSpec).successors jointInitial :=
  successors_erasure jointSpec jointCoefficient jointInitial

theorem joint_recorded_run_erases (capacity : Option Nat) (fuel : Nat) :
    erase (jointRecordedRun capacity fuel) = jointPlainRun fuel := by
  unfold jointRecordedRun jointPlainRun
  rw [run_erasure]
  rfl

theorem joint_recording_off_builds_no_prefix (fuel : Nat) :
    (jointRecordedRun none fuel).memory.2 = none := by
  unfold jointRecordedRun
  exact disabled_record (occurrenceSystem jointSpec) jointAuthoredSchedule
    jointNodeObserve fuel jointAuthoredSnapshot

theorem joint_disabled_recording_skips_materialization :
    accept (none : Option (Prefix JointOccurrence)) (fun _ => jointInitial) =
      accept none (fun _ => (⟨jointStart, [9]⟩ : JointOccurrence)) :=
  disabled_ignores_payload _ _

theorem joint_recording_stream_is_bounded (fuel : Nat)
    (snapshot : Snapshot JointOccurrence
      (Produced (Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Val CellId)
        Unit Unit × List Nat) Unit) :
    (stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve
      fuel snapshot).length ≤ fuel := by
  induction fuel generalizing snapshot with
  | zero => simp [stream]
  | succ fuel ih =>
      rw [stream, List.length_append]
      exact Nat.add_le_add (ih snapshot)
        (by cases next (occurrenceSystem jointSpec) jointAuthoredSchedule
              jointNodeObserve
              (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule
                fuel snapshot) <;> simp)

theorem joint_first_recording_request_is_the_root :
    stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve 1
        jointAuthoredSnapshot =
      [WorkOccurrence.root jointStart] := by
  rw [stream, Snapshot.run, stream, List.nil_append, next]
  simp only [jointAuthoredSnapshot, Snapshot.initial, jointAuthoredSchedule,
    Controller.fixed, Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst,
    Mettapedia.GSLT.Core.BranchingTemporal.initial, List.head?_cons, Option.map_some,
    jointNodeObserve, Option.toList_some]

/-- A recorder enabled after the disabled first request completes only the
suffix. The from-start record completes `[root] ++ suffix`. -/
theorem late_recording_cannot_complete_the_earlier_source_history :
    ((jointRecordedRun (some 2) 2).memory.2).bind Prefix.complete? =
      some (stream (occurrenceSystem jointSpec) jointAuthoredSchedule
        jointNodeObserve 2 jointAuthoredSnapshot) ∧
    (jointLateRecordedRun.memory.2).bind Prefix.complete? =
      some (stream (occurrenceSystem jointSpec) jointAuthoredSchedule
        jointNodeObserve 1 (jointPlainRun 1)) ∧
    stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve 2
        jointAuthoredSnapshot =
      [WorkOccurrence.root jointStart] ++
        stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve 1
          (jointPlainRun 1) ∧
    ((jointRecordedRun (some 2) 2).memory.2).bind Prefix.complete? ≠
      (jointLateRecordedRun.memory.2).bind Prefix.complete? := by
  let system := occurrenceSystem jointSpec
  have fullBound := joint_recording_stream_is_bounded 2 jointAuthoredSnapshot
  have fullComplete :=
    (complete_record_iff system jointAuthoredSchedule jointNodeObserve 2 2
      jointAuthoredSnapshot).mpr fullBound
  have lateBound : (stream system jointAuthoredSchedule jointNodeObserve 1
      (jointPlainRun 1)).length ≤ 2 :=
    Nat.le_trans (joint_recording_stream_is_bounded 1 (jointPlainRun 1))
      (Nat.le_succ 1)
  have lateAtPlain :=
    (complete_record_iff system jointAuthoredSchedule jointNodeObserve 2 1
      (jointPlainRun 1)).mpr lateBound
  have lateComplete :
      (jointLateRecordedRun.memory.2).bind Prefix.complete? =
        some (stream system jointAuthoredSchedule jointNodeObserve 1
          (jointPlainRun 1)) := by
    simpa [jointLateRecordedRun, joint_recorded_run_erases none 1] using lateAtPlain
  have split := stream_add system jointAuthoredSchedule jointNodeObserve 1 1
    jointAuthoredSnapshot
  have joined : stream system jointAuthoredSchedule jointNodeObserve 2
      jointAuthoredSnapshot =
      [WorkOccurrence.root jointStart] ++
        stream system jointAuthoredSchedule jointNodeObserve 1 (jointPlainRun 1) := by
    rw [split, joint_first_recording_request_is_the_root]
    rfl
  refine ⟨fullComplete, lateComplete, joined, ?_⟩
  unfold jointRecordedRun
  rw [fullComplete, lateComplete, joined]
  intro same
  injection same with streams
  have lengths := congrArg List.length streams
  simp only [List.length_append, List.length_singleton] at lengths
  omega

/-- `SharedAct.inspect` commits no delivery. The framed world and the delivered
list stay the ones the host already held, for every earned payload. -/
theorem submit_inspect_keeps_the_paid_frame (earned : JointLedger)
    (host : Host (SharedConsumers JointLedger) (Fin 2)
      (PaidCustody × List JointLedger)) :
    (submit (sharedSystem earned) (frameAct earned) host.epoch
        (SharedAct.inspect 0) host).world = host.world ∧
      (submit (sharedSystem earned) (frameAct earned) host.epoch
        (SharedAct.inspect 0) host).delivered = host.delivered := by
  cases retained : host.retained with
  | none =>
      rw [submit_retired (sharedSystem earned) (frameAct earned) host.epoch
        (SharedAct.inspect 0) retained]
      exact ⟨rfl, rfl⟩
  | some state =>
      have fresh :
          ((sharedSystem earned).committed
              ((sharedSystem earned).apply (SharedAct.inspect 0) state)).drop
            ((sharedSystem earned).committed state).length = [] := by
        simp only [sharedSystem, committedShared, applyShared, List.drop_length]
      rw [submit_current (sharedSystem earned) (frameAct earned)
        (SharedAct.inspect 0) retained]
      rw [fresh, interpret_nil, List.append_nil]
      exact ⟨rfl, rfl⟩

/-- Retire commits no delivery, so a reached host's world is the world named
by its retire submission. -/
private theorem submit_retire_keeps_the_paid_frame (earned : JointLedger)
    (host : Host (SharedConsumers JointLedger) (Fin 2)
      (PaidCustody × List JointLedger)) :
    (submit (sharedSystem earned) (frameAct earned) host.epoch
        (SharedAct.retire 0) host).world = host.world ∧
      (submit (sharedSystem earned) (frameAct earned) host.epoch
        (SharedAct.retire 0) host).delivered = host.delivered := by
  cases retained : host.retained with
  | none =>
      rw [submit_retired (sharedSystem earned) (frameAct earned) host.epoch
        (SharedAct.retire 0) retained]
      exact ⟨rfl, rfl⟩
  | some state =>
      have same :
          (applyShared earned (SharedAct.retire 0) state).deliveries = state.deliveries := by
        cases hlive : (state.seats 0).live with
        | false => simp [applyShared, hlive]
        | true =>
            cases hrel : releaseJoint state.registry (state.handles 0) with
            | mk reply _visits =>
                cases reply with
                | none => simp [applyShared, hlive, hrel]
                | some pair =>
                    cases pair with
                    | mk _next _cleared => simp [applyShared, hlive, hrel]
      have fresh :
          ((sharedSystem earned).committed
              ((sharedSystem earned).apply (SharedAct.retire 0) state)).drop
            ((sharedSystem earned).committed state).length = [] := by
        simp only [sharedSystem, committedShared, same, List.drop_length]
      rw [submit_current (sharedSystem earned) (frameAct earned)
        (SharedAct.retire 0) retained]
      rw [fresh, interpret_nil, List.append_nil]
      exact ⟨rfl, rfl⟩

structure FramedReaderInspection where
  observation : GraphAccount
  costs : Mettapedia.Machines.NativeCostLedger.Ledger
  framed : Host (SharedConsumers JointLedger) (Fin 2) (PaidCustody × List JointLedger)

/-- Read `host.world.1.certificate.receipts` and append `NativeCostLedger.inspect`
of `prior`. The certificate is the one in the host. `prior` is not replaced
by `[]`. No recorder is allocated. -/
def framedReaderInspection (maximum identity origin occurrence : Nat)
    (prior : Mettapedia.Machines.NativeCostLedger.Ledger)
    (host : Host (SharedConsumers JointLedger) (Fin 2)
      (PaidCustody × List JointLedger)) : FramedReaderInspection where
  observation := readGraph host.world.1.certificate.receipts.nodes
  costs :=
    (Mettapedia.Machines.NativeCostLedger.inspect maximum prior identity origin occurrence).2
  framed :=
    submit (sharedSystem host.world.1.certificate.ledger)
      (frameAct host.world.1.certificate.ledger) host.epoch (SharedAct.inspect 0) host

/-- One inspection of a host against an arbitrary cost prefix. `step` is that
`framedReaderInspection`; callers do not supply the construction. The reader
is the completed fold of the host certificate's receipts. The charge is
`NativeCostLedger.inspect` of `prior`: one declared `costRead`, and the
framed certificate and cut stay, so no production occurrence is written.
The `+ 1` is that declared unit. It does not make `identity` a fresh physical
event. `identity` is an argument of `inspect`. An arbitrary `prior` need not
exclude it. This is not a traversal bound or a compiled-code proof. -/
theorem framed_reader_inspection_charges_the_prior
    (maximum identity origin occurrence : Nat)
    (prior : Mettapedia.Machines.NativeCostLedger.Ledger)
    (host : Host (SharedConsumers JointLedger) (Fin 2)
      (PaidCustody × List JointLedger)) :
    let nodes := host.world.1.certificate.receipts.nodes
    let step := framedReaderInspection maximum identity origin occurrence prior host
    step.observation = readGraph nodes ∧
      Mettapedia.Machines.Cursor.advance
          (Mettapedia.Machines.Cursor.Sequence.tails JointReceiptNode)
          (Mettapedia.Machines.Cursor.Fold.client readReceipt) (fun _ _ => 1)
          (nodes.reverse.length + 2)
          (Mettapedia.Machines.Cursor.Fold.start
            (Mettapedia.Machines.Cursor.Sequence.tails JointReceiptNode)
            readReceipt nodes.reverse (⟨[], [], []⟩ : GraphAccount)) =
        (nodes.reverse.length + 1, .done ⟨(), readGraph nodes, []⟩) ∧
      step.costs =
        (Mettapedia.Machines.NativeCostLedger.inspect maximum prior
          identity origin occurrence).2 ∧
      (Mettapedia.Machines.NativeCostLedger.inspect maximum prior
          identity origin occurrence).1 =
        Mettapedia.Machines.NativeCostLedger.snapshot prior ∧
      (Mettapedia.Machines.NativeCostLedger.snapshot step.costs).2 =
        (Mettapedia.Machines.NativeCostLedger.snapshot prior).2 + 1 ∧
      (Mettapedia.Machines.NativeCostLedger.readEvent identity origin occurrence).2.kind =
        Mettapedia.Machines.NativeCostLedger.Kind.costRead ∧
      (Mettapedia.Machines.NativeCostLedger.readEvent identity origin occurrence).2.units = 1 ∧
      step.framed.world = host.world ∧
      step.framed.delivered = host.delivered ∧
      step.framed.world.1.certificate = host.world.1.certificate ∧
      step.framed.world.1.account.cut = host.world.1.account.cut := by
  have kept :=
    submit_inspect_keeps_the_paid_frame host.world.1.certificate.ledger host
  refine ⟨rfl,
      passive_reader_is_the_completed_fold host.world.1.certificate.receipts.nodes, rfl,
      Mettapedia.Machines.NativeCostLedger.inspect_preceding maximum prior
        identity origin occurrence,
      Mettapedia.Machines.NativeCostLedger.inspect_work maximum prior
        identity origin occurrence,
      rfl, rfl, kept.1, kept.2,
      congrArg (fun world => world.1.certificate) kept.1,
      congrArg (fun world => world.1.account.cut) kept.1⟩

/-- One-charge-per-identity is the existing `unique_append_event` law.
`Unique prior` and a fresh `identity` are premises, not consequences of the
unit count. -/
theorem framed_reader_inspection_keeps_unique_when_the_identity_is_fresh
    (maximum identity origin occurrence : Nat)
    (prior : Mettapedia.Machines.NativeCostLedger.Ledger)
    (host : Host (SharedConsumers JointLedger) (Fin 2)
      (PaidCustody × List JointLedger))
    (unique : Mettapedia.Machines.NativeCostLedger.Unique prior)
    (fresh : identity ∉ Mettapedia.Machines.NativeCostLedger.identities prior) :
    Mettapedia.Machines.NativeCostLedger.Unique
      (framedReaderInspection maximum identity origin occurrence prior host).costs :=
  Mettapedia.Machines.NativeCostLedger.unique_append_event maximum prior
    (Mettapedia.Machines.NativeCostLedger.readEvent identity origin occurrence)
    unique fresh

/-- A second inspection adds one declared unit to the first snapshot and
keeps the same certificate and cut. The first unit remains the base of that
sum. Repeating `identity` is not a second fresh physical event: freshness
for `unique_append_event` is not discharged here. -/
theorem successive_framed_inspections_retain_the_first_charge
    (maximum identity origin occurrence : Nat)
    (prior : Mettapedia.Machines.NativeCostLedger.Ledger)
    (host : Host (SharedConsumers JointLedger) (Fin 2)
      (PaidCustody × List JointLedger)) :
    let first := framedReaderInspection maximum identity origin occurrence prior host
    let second :=
      framedReaderInspection maximum identity origin occurrence first.costs first.framed
    Mettapedia.Machines.NativeCostLedger.snapshot first.costs =
        Mettapedia.Machines.NativeCostLedger.snapshot prior +
          Mettapedia.Machines.NativeCostLedger.eventGrade
            (Mettapedia.Machines.NativeCostLedger.readEvent identity origin occurrence) ∧
      Mettapedia.Machines.NativeCostLedger.snapshot second.costs =
        Mettapedia.Machines.NativeCostLedger.snapshot first.costs +
          Mettapedia.Machines.NativeCostLedger.eventGrade
            (Mettapedia.Machines.NativeCostLedger.readEvent identity origin occurrence) ∧
      (Mettapedia.Machines.NativeCostLedger.snapshot first.costs).2 =
        (Mettapedia.Machines.NativeCostLedger.snapshot prior).2 + 1 ∧
      (Mettapedia.Machines.NativeCostLedger.snapshot second.costs).2 =
        (Mettapedia.Machines.NativeCostLedger.snapshot first.costs).2 + 1 ∧
      second.framed.world.1.certificate = host.world.1.certificate ∧
      second.framed.world.1.account.cut = host.world.1.account.cut ∧
      second.framed.delivered = host.delivered := by
  have firstKept :=
    submit_inspect_keeps_the_paid_frame host.world.1.certificate.ledger host
  have secondKept :=
    submit_inspect_keeps_the_paid_frame
      (framedReaderInspection maximum identity origin occurrence prior host).framed.world.1.certificate.ledger
      (framedReaderInspection maximum identity origin occurrence prior host).framed
  refine ⟨
      Mettapedia.Machines.NativeCostLedger.inspect_charged maximum prior
        identity origin occurrence,
      Mettapedia.Machines.NativeCostLedger.inspect_charged maximum
        (framedReaderInspection maximum identity origin occurrence prior host).costs
        identity origin occurrence,
      Mettapedia.Machines.NativeCostLedger.inspect_work maximum prior
        identity origin occurrence,
      Mettapedia.Machines.NativeCostLedger.inspect_work maximum
        (framedReaderInspection maximum identity origin occurrence prior host).costs
        identity origin occurrence,
      congrArg (fun world => world.1.certificate) (secondKept.1.trans firstKept.1),
      congrArg (fun world => world.1.account.cut) (secondKept.1.trans firstKept.1),
      secondKept.2.trans firstKept.2⟩

/-- The reached paid host, not a separately built certificate, is inspected
against `prior`. The observation is that host's completed receipt read.
One declared `costRead` is appended to `prior`, and a second inspection
keeps that first snapshot and the same paid ledger, cut, and rights.
Neither step writes a production occurrence. Coordinates `1` and `2` are
the arguments passed to `NativeCostLedger.inspect`. This instance does not
assume they are fresh in `prior`, so the unit counts are not unique or
authentic physical issuance. `costRead` is not a traversal bound or a
compiled-code proof. Recording erasure and late enable stay the separate
source-run endpoints above. -/
theorem enabled_reader_work_keeps_the_paid_source_ledger
    (suffix : Nat) (prior : Mettapedia.Machines.NativeCostLedger.Ledger) :
    ∃ (target : JointMachine)
      (history : History (pathMachine jointSpec jointStart) jointStart target)
      (cert : SourceCertificate) (account : PresentedAccount)
      (host : Host (SharedConsumers JointLedger) (Fin 2)
        (PaidCustody × List JointLedger)),
      issueEarned history = some cert ∧
        cert.ledger = jointProductionLedger ∧
        denote jointProductionLedger = 4 ∧
        jointLeftFactor.coefficient = 2 ∧
        cert.rights = {Right.inspect} ∧
        account.cut =
          [(Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence), 4)] ∧
        host.delivered = [] ∧
        host.world.2 = ([] : List JointLedger) ∧
        host.world.1.certificate.ledger = jointProductionLedger ∧
        host.world.1.certificate.rights = {Right.inspect} ∧
        host.world.1.account.cut = account.cut ∧
        let step := framedReaderInspection 255 1 2 0 prior host
        let next := framedReaderInspection 255 1 2 0 step.costs step.framed
        step.observation = readGraph host.world.1.certificate.receipts.nodes ∧
          (Mettapedia.Machines.NativeCostLedger.snapshot step.costs).2 =
            (Mettapedia.Machines.NativeCostLedger.snapshot prior).2 + 1 ∧
          (Mettapedia.Machines.NativeCostLedger.readEvent 1 2 0).2.kind =
            Mettapedia.Machines.NativeCostLedger.Kind.costRead ∧
          (Mettapedia.Machines.NativeCostLedger.readEvent 1 2 0).2.units = 1 ∧
          step.framed.world.1.certificate.ledger = jointProductionLedger ∧
          step.framed.world.1.certificate.rights = {Right.inspect} ∧
          step.framed.world.1.account.cut = account.cut ∧
          step.framed.delivered = [] ∧
          Mettapedia.Machines.NativeCostLedger.snapshot next.costs =
            Mettapedia.Machines.NativeCostLedger.snapshot step.costs +
              Mettapedia.Machines.NativeCostLedger.eventGrade
                (Mettapedia.Machines.NativeCostLedger.readEvent 1 2 0) ∧
          (Mettapedia.Machines.NativeCostLedger.snapshot next.costs).2 =
            (Mettapedia.Machines.NativeCostLedger.snapshot step.costs).2 + 1 ∧
          next.framed.world.1.certificate.ledger = jointProductionLedger ∧
          next.framed.world.1.certificate.rights = {Right.inspect} ∧
          next.framed.world.1.account.cut = account.cut ∧
          next.framed.delivered = [] := by
  obtain ⟨target, history, cert, account, _accepted, _handles, host, _retired,
      _cutIssued, issuedHistory, _accountEndpoint, _admitted, ledgerEq, _paymentDenote,
      denoted, rights, _halted, _roots, _accountLedger, _held, _requested, cutFour,
      _paired, _different, _acceptedEq, _producedNil, _resumedCut, _deliveredPaid,
      emptyDelivered, emptyObs, _retainedRet, _dead, _alive, _handleKept, _auth,
      _unreadZero, _unreadOne, _submitDelivered, submitLedger, _submitPayment,
      submitRights, submitCut, _submitObs, _nonempty⟩ :=
    returned_retirement_keeps_the_nonempty_paid_account suffix
  have retireFrame := submit_retire_keeps_the_paid_frame cert.ledger host
  have hostLedger : host.world.1.certificate.ledger = jointProductionLedger := by
    rw [← retireFrame.1]
    exact submitLedger
  have hostRights : host.world.1.certificate.rights = {Right.inspect} := by
    rw [← retireFrame.1]
    exact submitRights
  have hostCut : host.world.1.account.cut = account.cut := by
    rw [← retireFrame.1]
    exact submitCut
  have productionDenote : denote jointProductionLedger = 4 := by
    rw [← ledgerEq]
    exact denoted
  have charge := framed_reader_inspection_charges_the_prior 255 1 2 0 prior host
  dsimp only at charge
  obtain ⟨observationEq, _cursor, _costsEq, _preceding, work, kind, units, _worldEq,
      deliveredEq, certEq, cutEq⟩ := charge
  have again := successive_framed_inspections_retain_the_first_charge 255 1 2 0 prior host
  dsimp only at again
  obtain ⟨_firstGrade, retainedGrade, _firstWork, secondWork, nextCert, nextCut,
      nextDelivered⟩ := again
  refine ⟨target, history, cert, account, host, issuedHistory, ledgerEq, productionDenote,
      rfl, rights, cutFour, emptyDelivered, emptyObs, hostLedger, hostRights, hostCut,
      observationEq, work, kind, units, ?_, ?_, ?_, ?_, retainedGrade, secondWork,
      ?_, ?_, ?_, ?_⟩
  · rw [certEq, hostLedger]
  · rw [certEq, hostRights]
  · rw [cutEq, hostCut]
  · rw [deliveredEq, emptyDelivered]
  · rw [nextCert, hostLedger]
  · rw [nextCert, hostRights]
  · rw [nextCut, hostCut]
  · rw [nextDelivered, emptyDelivered]


/-- Receipt erasure preserves this spec's breadth-first demand run, including
answer order and the residual frontier. This is the existing realization
boundary. It does not verify a C executor, and it is not the recorder
erasure above. -/
theorem joint_receipt_erasure_preserves_the_breadth_first_run
    (goal : List (Produced (Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Val CellId)
      Unit Unit × List Nat) → Bool) (fuel : Nat) :
    (Mettapedia.GSLT.Core.DemandExecution.run (occurrenceSystem jointSpec)
        (Controller.fixed
          Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst)
        goal fuel jointAuthoredSnapshot).mapNodes
      Mettapedia.Machines.BranchLocalNeed.NeedInferenceControl.Erasure.eraseOccurrence =
      Mettapedia.GSLT.Core.DemandExecution.run
        (Mettapedia.Machines.BranchLocalNeed.NeedInferenceControl.Erasure.coreOccurrenceSystem
          jointSpec)
        (Controller.fixed
          Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst)
        goal fuel
        (jointAuthoredSnapshot.mapNodes
          Mettapedia.Machines.BranchLocalNeed.NeedInferenceControl.Erasure.eraseOccurrence) :=
  Mettapedia.Machines.BranchLocalNeed.NeedInferenceControl.Erasure.demanded_breadthFirst_run_erases
    jointSpec goal fuel jointAuthoredSnapshot

open Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption renaming retained → sourceRetained

/-! ### Pure replay of a retained request

`acceptOwnedReplay` replays the submitted leaf trace through `replayAccount`.
The accepted account is built from the replayed machine: its occurrence is
that state and the submitted trace, its tag is `inl` when `isHalted` and
`inr` otherwise, its payment is `denote` of the replayed ledger, and its
roots and rights are `rootedCells` and `requiredRights`. `admitIssued` must
accept that account. Refusal keeps the submitted account and its paid ledger.

The submitted machine, tag, rights, and roots are not copied into an
acceptance. A same-trace wrong state and a wrong `Sum` tag are canonicalized
to the replayed cut. This is not complete cut validation. State agreement is
the replay construction. It does not decide equality of heap functions.

`each_retained_request_follows_the_source` uses `retained_occurrence_replays`:
the retained trace follows to the retained state, and `traceReplay` returns
that state with the ordered factors.

This is not `PhaseReplay`. It does not read scoped charge receipts, compare a
`Preparation.Capture`, or treat a suffix trace as an earlier unrecorded
prefix. A controller frontier is not identified with `jointRun` in general.
The `+1`/`+2` fee is not physical uniqueness. Nothing here verifies C.
-/

/-- One alternative at each `jointSpec` origin. The successor bound is
`NeedReference.step_length_le_one`. -/
private theorem joint_step_at_most_one (machine : JointMachine) :
    (step jointSpec machine).length ≤ 1 :=
  step_length_le_one jointSpec (by
    intro origin
    cases origin; simp [jointSpec]) machine

private theorem step_singleton_of_zero (state next : JointMachine)
    (lengthOne : (step jointSpec state).length = 1)
    (head : (step jointSpec state)[0]? = some next) :
    step jointSpec state = [next] := by
  obtain ⟨only, onlyEq⟩ := (List.length_eq_one_iff).mp lengthOne
  have onlyHead : only = next := by
    have onlyLookup : (step jointSpec state)[0]? = some only := by
      rw [onlyEq]
      exact List.getElem?_cons_zero
    exact Option.some.inj (onlyLookup.symm.trans head)
  rw [onlyEq, onlyHead]

private theorem occurrence_system_is_the_path_machine :
    occurrenceSystem jointSpec =
      WorkOccurrence.system (pathMachine jointSpec jointStart) := rfl

private theorem breadth_reorder (frontier : List JointOccurrence) :
    (jointAuthoredSchedule.scheduler ()).reorder frontier = frontier := rfl

private theorem breadth_integrate
    (pending generated : List JointOccurrence) :
    (jointAuthoredSchedule.scheduler ()).integrate pending generated =
      pending ++ generated := rfl

private def indexedOccurrence (k : Nat) : Option JointOccurrence :=
  ((pathMachine jointSpec jointStart).follow jointStart (List.replicate k 0)).map
    fun state => ⟨state, List.replicate k 0⟩

private theorem one_indexed_successor (occurrence : JointOccurrence) (next : JointMachine)
    (stepEq : step jointSpec occurrence.state = [next]) :
    (occurrenceSystem jointSpec).successors occurrence =
      [⟨next, occurrence.trace ++ [0]⟩] := by
  simp only [occurrenceSystem, branchingSystem, WorkOccurrence.lift, stepEq,
    List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil]

/-- A zero-index spine stays one breadth-first request. The chain is an
assumption about successor length; this theorem does not execute fuel `15`. -/
private theorem authored_linear_prefix (n : Nat)
    (chain : ∀ k, k < n →
      ∃ state next,
        (pathMachine jointSpec jointStart).follow jointStart (List.replicate k 0) =
            some state ∧
          (step jointSpec state).length = 1 ∧
          (step jointSpec state)[0]? = some next ∧
          (pathMachine jointSpec jointStart).follow jointStart
              (List.replicate (k + 1) 0) = some next) :
    (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule n
        jointAuthoredSnapshot).memory = () ∧
      (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule n
          jointAuthoredSnapshot).search.frontier = (indexedOccurrence n).toList ∧
        stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve n
            jointAuthoredSnapshot =
          (List.range n).filterMap indexedOccurrence ∧
          (stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve n
              jointAuthoredSnapshot).length = n := by
  induction n with
  | zero =>
      simp [Snapshot.run, stream, jointAuthoredSnapshot, indexedOccurrence,
        OccurrenceMachineCore.follow, List.replicate, Option.map, Option.toList,
        WorkOccurrence.root, Snapshot.initial,
        Mettapedia.GSLT.Core.BranchingTemporal.initial]
  | succ n ih =>
      obtain ⟨memoryN, frontierN, streamN, lengthN⟩ :=
        ih (fun k hk => chain k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      obtain ⟨state, successor, followN, lengthOne, head, followSucc⟩ :=
        chain n (Nat.lt_succ_self n)
      have stepEq : step jointSpec state = [successor] :=
        step_singleton_of_zero state successor lengthOne head
      have nodeSome : indexedOccurrence n = some ⟨state, List.replicate n 0⟩ := by
        simp [indexedOccurrence, followN]
      have frontierNode :
          (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule n
              jointAuthoredSnapshot).search.frontier =
            [⟨state, List.replicate n 0⟩] := by
        rw [frontierN, nodeSome]
        rfl
      have successorsEq :=
        one_indexed_successor ⟨state, List.replicate n 0⟩ successor stepEq
      have memorySucc :
          (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule (n + 1)
              jointAuthoredSnapshot).memory = () := by
        change (Snapshot.tick (occurrenceSystem jointSpec) jointAuthoredSchedule
          (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule n
            jointAuthoredSnapshot)).memory = ()
        simp only [Snapshot.tick, memoryN, breadth_reorder, frontierNode]
      have frontierSucc :
          (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule (n + 1)
              jointAuthoredSnapshot).search.frontier =
            [⟨successor, List.replicate n 0 ++ [0]⟩] := by
        change (Snapshot.tick (occurrenceSystem jointSpec) jointAuthoredSchedule
          (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule n
            jointAuthoredSnapshot)).search.frontier = _
        simp only [Snapshot.tick, Mettapedia.GSLT.Core.BranchingTemporal.tick, memoryN,
          breadth_reorder, frontierNode, breadth_integrate, successorsEq,
          List.nil_append]
      have traceSucc : List.replicate n 0 ++ [0] = List.replicate (n + 1) 0 :=
        (List.replicate_succ').symm
      have nodeSucc :
          indexedOccurrence (n + 1) = some ⟨successor, List.replicate (n + 1) 0⟩ := by
        simp [indexedOccurrence, followSucc]
      refine ⟨memorySucc, ?_, ?_, ?_⟩
      · rw [frontierSucc, traceSucc, nodeSucc]
        rfl
      · have streamStep :
            stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve (n + 1)
                jointAuthoredSnapshot =
              stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve n
                  jointAuthoredSnapshot ++
                [⟨state, List.replicate n 0⟩] := by
          change stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve n
              jointAuthoredSnapshot ++
            (next (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve
              (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule n
                jointAuthoredSnapshot)).toList = _
          simp only [next, memoryN, breadth_reorder, frontierNode, jointNodeObserve,
            List.head?_cons, Option.map_some, Option.toList_some]
        rw [streamStep, streamN, List.range_succ, List.filterMap_append,
          List.filterMap_cons_some nodeSome, List.filterMap_nil]
      · have streamStep :
            stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve (n + 1)
                jointAuthoredSnapshot =
              stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve n
                  jointAuthoredSnapshot ++
                [⟨state, List.replicate n 0⟩] := by
          change stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve n
              jointAuthoredSnapshot ++
            (next (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve
              (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule n
                jointAuthoredSnapshot)).toList = _
          simp only [next, memoryN, breadth_reorder, frontierNode, jointNodeObserve,
            List.head?_cons, Option.map_some, Option.toList_some]
        rw [streamStep, List.length_append, List.length_singleton, lengthN]

/-- Every zero index of a retained history is the unique successor there.
The length bound is `joint_step_at_most_one`; the index comes from the path.
The path endpoints are variables so `induction` can see them. -/
private theorem zero_index_spine_from
    {source target : Mettapedia.OSLF.Binding.RewriteEventHistory.State
      (system (pathMachine jointSpec jointStart))}
    (history : Mettapedia.OSLF.Binding.RewriteEventHistory.History
      (system (pathMachine jointSpec jointStart)) source target)
    (sourceEq : source.term = jointStart)
    (indexed : indices (pathMachine jointSpec jointStart) history =
      List.replicate (indices (pathMachine jointSpec jointStart) history).length 0) :
    ∀ k, k < (indices (pathMachine jointSpec jointStart) history).length →
      ∃ state next,
        (pathMachine jointSpec jointStart).follow jointStart (List.replicate k 0) =
            some state ∧
          (step jointSpec state).length = 1 ∧
          (step jointSpec state)[0]? = some next ∧
          (pathMachine jointSpec jointStart).follow jointStart
              (List.replicate (k + 1) 0) = some next := by
  induction history with
  | nil =>
      intro k hk
      simp [indices] at hk
  | @cons middle after past event ih =>
      intro k hk
      have appended :
          indices (pathMachine jointSpec jointStart) past ++ [event.val] =
            List.replicate
              ((indices (pathMachine jointSpec jointStart) past).length + 1) 0 := by
        simpa [indices, List.length_append, List.length_singleton] using indexed
      rw [List.replicate_succ'] at appended
      obtain ⟨pastEq, eventEq⟩ := List.append_inj appended (by simp [List.length_replicate])
      have eventZero : event.val = 0 := (List.cons.inj eventEq).1
      have pastIndexed :
          indices (pathMachine jointSpec jointStart) past =
            List.replicate (indices (pathMachine jointSpec jointStart) past).length 0 :=
        pastEq
      by_cases earlier : k < (indices (pathMachine jointSpec jointStart) past).length
      · exact ih pastIndexed k earlier
      · have kEq : k = (indices (pathMachine jointSpec jointStart) past).length := by
          have shorter : k < (indices (pathMachine jointSpec jointStart) past).length + 1 := by
            simpa [indices, List.length_append, List.length_singleton] using hk
          omega
        have followed := follow_indices (pathMachine jointSpec jointStart) past
        rw [sourceEq, pastIndexed] at followed
        have looked : (step jointSpec middle.term)[0]? = some after.term := by
          simpa [pathMachine, eventZero] using event.property
        have lengthOne : (step jointSpec middle.term).length = 1 := by
          have atMost := joint_step_at_most_one middle.term
          have positive : 0 < (step jointSpec middle.term).length :=
            (List.getElem?_eq_some_iff.mp looked).1
          omega
        have followNext :
            (pathMachine jointSpec jointStart).follow jointStart
                (List.replicate (k + 1) 0) = some after.term := by
          rw [kEq, List.replicate_succ', WorkOccurrence.follow_append, followed]
          simp [pathMachine, OccurrenceMachineCore.follow, looked]
        refine ⟨middle.term, after.term, ?_, lengthOne, ?_, followNext⟩
        · rw [kEq]
          exact followed
        · exact looked

private theorem zero_index_spine
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (indexed : indices (pathMachine jointSpec jointStart) history =
      List.replicate (indices (pathMachine jointSpec jointStart) history).length 0) :
    ∀ k, k < (indices (pathMachine jointSpec jointStart) history).length →
      ∃ state next,
        (pathMachine jointSpec jointStart).follow jointStart (List.replicate k 0) =
            some state ∧
          (step jointSpec state).length = 1 ∧
          (step jointSpec state)[0]? = some next ∧
          (pathMachine jointSpec jointStart).follow jointStart
              (List.replicate (k + 1) 0) = some next :=
  zero_index_spine_from history rfl indexed

private theorem returned_request_is_issued :
    ∃ (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat)
      (history : History (pathMachine jointSpec jointStart) jointStart
        (retained leaf.1).state)
      (cert : SourceCertificate),
      jointRun = [leaf] ∧
        leaf.1.isLeft = true ∧
        leaf.2 = 4 ∧
        (retained leaf.1).trace = jointReturnTrace ∧
        isHalted (retained leaf.1).state = true ∧
        indices (pathMachine jointSpec jointStart) history = jointReturnTrace ∧
        earnedLedger history = jointProductionLedger ∧
          denote jointProductionLedger = leaf.2 ∧
          issueEarned history = some cert ∧
          cert.ledger = jointProductionLedger ∧
          cert.trace = jointReturnTrace ∧
          cert.payment = denote jointProductionLedger := by
  rcases joint_returned_source_account with
    ⟨leaf, runEq, leafLeft, payEq, traceLeaf, _path, haltedLeaf, _controlLeaf,
      _leftLookup, _rightLookup, history, indicesEq, productionEq, _valid, denoted, _recorded⟩
  have cutLeaf : issueCut jointRun = issueLeaf leaf := by
    simp [issueCut, runEq]
  have ledgerMapped : (issueCut jointRun).map SourceCertificate.ledger =
      some jointProductionLedger := by
    obtain ⟨_b0, _b3, _b6, _b11, b15, _p0, _p3, _led6, _pay6, _led11, led15,
        _pay15, _ctrl15, _split⟩ := source_budgets_issue_the_reached_slices
    simpa [b15] using led15
  have leafSome : ∃ cert, issueLeaf leaf = some cert := by
    cases hleaf : issueLeaf leaf with
    | none => simp [cutLeaf, hleaf] at ledgerMapped
    | some cert => exact ⟨cert, rfl⟩
  obtain ⟨cert, leafIssued⟩ := leafSome
  obtain ⟨ledger, _rows, ledgerEq, _payLeaf, _rowsEq, certEq⟩ :=
    issueLeaf_exposes_the_earned_leaf leafIssued
  have certLedger : cert.ledger = ledger := by
    rw [certEq]
  have certProduction : cert.ledger = jointProductionLedger := by
    have mapped := ledgerMapped
    rw [cutLeaf, leafIssued] at mapped
    exact Option.some.inj mapped
  have earnedEq : earnedLedger history = jointProductionLedger := productionEq
  have historyLedger : earnedLedger history =
      (readGraph (retained leaf.1).state.world.receipts.nodes).factors :=
    earnedEq.trans ((certProduction.symm.trans certLedger).trans ledgerEq)
  have historyTrace : (retained leaf.1).trace = earnedTrace history := by
    rw [traceLeaf, earnedTrace, indicesEq]
  have issuedHistory : issueEarned history = some cert :=
    issueEarned_matches_issueLeaf history rfl historyTrace historyLedger leafIssued
  have traceCert : cert.trace = jointReturnTrace := by
    rw [(earned_history_is_the_passive_issuer issuedHistory).1, earnedTrace, indicesEq]
  have paymentCert : cert.payment = denote jointProductionLedger := by
    rw [(earned_history_is_the_passive_issuer issuedHistory).2.2.1, certProduction]
  exact ⟨leaf, history, cert, runEq, leafLeft, payEq, traceLeaf, haltedLeaf, indicesEq,
    earnedEq, denoted, issuedHistory, certProduction, traceCert, paymentCert⟩

/-- The account submitted to replay. Refusal returns this value, including its
paid ledger. Acceptance does not. -/
private def accountWithCut (cert : SourceCertificate) (cut : JointCut) : PresentedAccount :=
  ⟨cut, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩

/-- Account built from a replayed machine. The tag is `isHalted` of that
machine. Roots and rights are `rootedCells` and `requiredRights`. -/
def replayedAccount (state : JointMachine) (trace : List Nat) (ledger : JointLedger) :
    PresentedAccount :=
  let occurrence : JointOccurrence := ⟨state, trace⟩
  ⟨[(if isHalted state then Sum.inl occurrence else Sum.inr occurrence, denote ledger)],
    ledger, rootedCells state, requiredRights state, requiredRights state, none⟩

/-- Replay gate. The submitted trace is walked. The replayed machine supplies
the cut, ledger, and roots. The submitted held rights, request, and rival
stay on that account. `admitIssued` checks that held set with `restrict?`
and the rival with `Scoped.merge?`. Required rights are not possession, and
trace reconstruction grants no authority. Refusal returns the submitted
account. The submitted machine is not the accepted cut. -/
def acceptOwnedReplay
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (account : PresentedAccount) : RetainedAdmit PresentedAccount :=
  match issueEarned history, account.cut with
  | some issued, [leaf] =>
      match replayAccount (retained leaf.1).trace with
      | none => .reject .incoherentResidual account
      | some (state, replayed) =>
          let canonical :=
            { replayedAccount state (retained leaf.1).trace replayed with
                held := account.held
                requested := account.requested
                rival := account.rival }
          if decide (replayed ≠ issued.ledger) ||
              decide (account.ledger ≠ issued.ledger) ||
              decide ((retained leaf.1).trace ≠ issued.trace) ||
              decide (denote replayed ≠ issued.payment) then
            .reject .incoherentResidual account
          else
            match admitIssued issued canonical with
            | .accept _ => .accept canonical
            | .reject reason _ => .reject reason account
  | some _, _ => .reject .incompleteResidual account
  | none, _ => .reject .incoherentResidual account

/-- Successful replay preserves held authority and the request and claim.
The checked request is contained in that supplied authority. -/
theorem replay_keeps_the_supplied_authority
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (account accepted : PresentedAccount)
    (granted : acceptOwnedReplay history account = .accept accepted) :
    accepted.held = account.held ∧
      accepted.requested = account.requested ∧
      accepted.rival = account.rival ∧
      account.requested ⊆ account.held := by
  unfold acceptOwnedReplay at granted
  split at granted
  · split at granted
    · cases granted
    · split at granted
      · cases granted
      · dsimp at granted
        split at granted
        · rename_i checked hadmit
          have permitted := issuedChecksHeld _ _ checked hadmit
          cases granted
          exact ⟨rfl, rfl, rfl, permitted.2⟩
        · cases granted
  · cases granted
  · cases granted

theorem replay_acceptance_checks_the_issued_rights
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (account accepted : PresentedAccount)
    (granted : acceptOwnedReplay history account = .accept accepted) :
    ∃ cert, issueEarned history = some cert ∧ cert.rights ⊆ account.held ∧
      account.requested ⊆ account.held := by
  unfold acceptOwnedReplay at granted
  split at granted
  · rename_i cert leaf issued cut
    refine ⟨cert, issued, ?_⟩
    split at granted
    · cases granted
    · split at granted
      · cases granted
      · dsimp at granted
        split at granted
        · rename_i checked hadmit
          have permitted := issuedChecksHeld _ _ checked hadmit
          exact permitted
        · cases granted
  · cases granted
  · cases granted


theorem earned_certificate_rights
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    {cert : SourceCertificate} (issued : issueEarned history = some cert) :
    cert.rights = requiredRights target := by
  unfold issueEarned at issued
  split at issued
  · cases issued
  · cases issued
    rfl

/-- Neither a pending nor a completed source endpoint can authorize an empty
holder merely by being reconstructed from a trace. -/
theorem replay_empty_held_is_never_accepted
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (account : PresentedAccount) (empty : account.held = ∅) :
    ∀ accepted : PresentedAccount,
      acceptOwnedReplay history account ≠ .accept accepted := by
  intro accepted granted
  obtain ⟨cert, issued, required, _requested⟩ :=
    replay_acceptance_checks_the_issued_rights history account accepted granted
  have rights := earned_certificate_rights history issued
  rw [rights, empty] at required
  cases control : target.control <;> simp [requiredRights, control] at required


/-- Each retained recording request follows the source machine that produced
it. `replayAccount` returns that same state and the ordered production
factors. This does not issue a certificate and does not accept a cut. -/
theorem each_retained_request_follows_the_source
    (capacity fuel : Nat) (record : Prefix JointOccurrence)
    (kept : (jointRecordedRun (some capacity) fuel).memory.2 = some record)
    {occurrence : JointOccurrence} (member : occurrence ∈ record.items) :
    (pathMachine jointSpec jointStart).follow jointStart occurrence.trace =
        some occurrence.state ∧
      ∃ ledger,
        replayAccount occurrence.trace = some (occurrence.state, ledger) := by
  have keptSystem :
      (Snapshot.run (WorkOccurrence.system (pathMachine jointSpec jointStart))
        (controller jointAuthoredSchedule (fun _ selected _ _ => selected) (some capacity)) fuel
        (start (Snapshot.initial jointAuthoredSchedule [WorkOccurrence.root jointStart])
          (some capacity))).memory.2 = some record := by
    unfold jointRecordedRun jointAuthoredSnapshot jointNodeObserve at kept
    exact kept
  have followed :=
    retained_occurrence_replays (pathMachine jointSpec jointStart) jointAuthoredSchedule
      jointStart capacity fuel record keptSystem member
  refine ⟨followed, ?_⟩
  have replayMap := trace_replay_follows jointSpec jointAssignment jointStart
    jointStart occurrence.trace
  rw [followed] at replayMap
  cases walked : replayAccount occurrence.trace with
  | none =>
      rw [replayAccount] at walked
      rw [walked] at replayMap
      cases replayMap
  | some result =>
      obtain ⟨state, ledger⟩ := result
      rw [replayAccount] at walked
      have stateEq : state = occurrence.state := by
        have mapped :
            (some (state, ledger)).map Prod.fst = some occurrence.state := by
          rw [← walked]
          exact replayMap
        simp only [Option.map_some] at mapped
        exact Option.some.inj mapped
      subst stateEq
      exact ⟨ledger, rfl⟩

private theorem returned_occurrence_is_retained
    (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat)
    (history : History (pathMachine jointSpec jointStart) jointStart (retained leaf.1).state)
    (traceLeaf : (retained leaf.1).trace = jointReturnTrace)
    (indexed : indices (pathMachine jointSpec jointStart) history = jointReturnTrace) :
    ∃ record : Prefix JointOccurrence,
      (jointRecordedRun (some 15) 15).memory.2 = some record ∧
        retained leaf.1 ∈ record.items := by
  have indexedReplicate :
      indices (pathMachine jointSpec jointStart) history =
        List.replicate (indices (pathMachine jointSpec jointStart) history).length 0 := by
    simp [indexed, jointReturnTrace]
  have chain := zero_index_spine history indexedReplicate
  have lengthTrace : (indices (pathMachine jointSpec jointStart) history).length = 14 := by
    simp [indexed, jointReturnTrace]
  have walked14 := authored_linear_prefix 14 (fun k hk => chain k (by
    rw [lengthTrace]
    exact hk))
  obtain ⟨memory14, frontier14, _stream14, length14⟩ := walked14
  have followed14 := follow_indices (pathMachine jointSpec jointStart) history
  rw [indexed] at followed14
  have node14 : indexedOccurrence 14 =
      some (sourceRetained leaf.1) := by
    rw [jointReturnTrace] at followed14
    simp only [indexedOccurrence, followed14, Option.map_some]
    rw [← jointReturnTrace, ← traceLeaf]
  have frontierNode :
      (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule 14
          jointAuthoredSnapshot).search.frontier = [retained leaf.1] := by
    rw [frontier14, node14]
    rfl
  have stream15 :
      stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve 15
          jointAuthoredSnapshot =
        stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve 14
            jointAuthoredSnapshot ++ [retained leaf.1] := by
    change stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve 14
        jointAuthoredSnapshot ++
      (next (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve
        (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule 14
          jointAuthoredSnapshot)).toList = _
    simp only [next, memory14, breadth_reorder, frontierNode, jointNodeObserve,
      List.head?_cons, Option.map_some, Option.toList_some]
  have length15 :
      (stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve 15
          jointAuthoredSnapshot).length = 15 := by
    rw [stream15, List.length_append, List.length_singleton, length14]
  have memberStream : retained leaf.1 ∈
      stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve 15
        jointAuthoredSnapshot := by
    rw [stream15]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have prefixEq := retained_prefix (occurrenceSystem jointSpec) jointAuthoredSchedule
    jointNodeObserve 15 15 jointAuthoredSnapshot
  rw [List.take_of_length_le (by rw [length15])] at prefixEq
  have someRecord : ∃ record : Prefix JointOccurrence,
      (jointRecordedRun (some 15) 15).memory.2 = some record := by
    cases recorded : (jointRecordedRun (some 15) 15).memory.2 with
    | none =>
        unfold jointRecordedRun at recorded
        rw [recorded] at prefixEq
        cases prefixEq
    | some record => exact ⟨record, rfl⟩
  obtain ⟨record, kept⟩ := someRecord
  have itemsEq : record.items =
      stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve 15
        jointAuthoredSnapshot := by
    unfold jointRecordedRun at kept
    rw [kept, Option.map_some, Option.some.injEq] at prefixEq
    exact prefixEq
  exact ⟨record, kept, by rwa [itemsEq]⟩

/-- The fuel-15 returned request is a retained recording entry. Its trace
follows to the returned machine, `replayAccount` returns `jointProductionLedger`,
and the accepted account is `replayedAccount` of that state. For this
submission that account is `endpointAccount`, whose cut is `jointRun`. -/
theorem owned_return_replays_the_retained_request :
    ∃ (record : Prefix JointOccurrence)
      (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat)
      (history : History (pathMachine jointSpec jointStart) jointStart (retained leaf.1).state)
      (cert : SourceCertificate),
      (jointRecordedRun (some 15) 15).memory.2 = some record ∧
        retained leaf.1 ∈ record.items ∧
        jointRun = [leaf] ∧
        (pathMachine jointSpec jointStart).follow jointStart (retained leaf.1).trace =
          some (retained leaf.1).state ∧
        replayAccount (retained leaf.1).trace =
          some ((retained leaf.1).state, cert.ledger) ∧
        issueEarned history = some cert ∧
        cert.ledger = jointProductionLedger ∧
        denote cert.ledger = leaf.2 ∧
        cert.trace = (retained leaf.1).trace ∧
        replayedAccount (retained leaf.1).state (retained leaf.1).trace cert.ledger =
          endpointAccount history ∧
        acceptOwnedReplay history (endpointAccount history) =
          .accept (endpointAccount history) ∧
        (endpointAccount history).cut = jointRun ∧
        (endpointAccount history).ledger = cert.ledger := by
  obtain ⟨leaf, history, cert, runEq, leafLeft, _payEq, traceLeaf, haltedLeaf, indicesEq,
      productionEq, denoted, issued, certLedger, certTrace, certPayment⟩ :=
    returned_request_is_issued
  obtain ⟨record, kept, member⟩ :=
    returned_occurrence_is_retained leaf history traceLeaf indicesEq
  obtain ⟨followEq, ledger, replayEq⟩ :=
    each_retained_request_follows_the_source 15 15 record kept member
  have verified := (replay_verifies_the_earned_history history).1
  have earnedEq : earnedLedger history = cert.ledger := by
    rw [certLedger]
    exact productionEq
  have replayLedger : ledger = cert.ledger := by
    have sameWalk :
        replayAccount (earnedTrace history) =
          some ((sourceRetained leaf.1).state, ledger) := by
      rw [earnedTrace, indicesEq, ← traceLeaf]
      exact replayEq
    rw [verified] at sameWalk
    exact ((Prod.ext_iff.mp (Option.some.inj sameWalk)).2).symm.trans earnedEq
  have accountLedger : (endpointAccount history).ledger = cert.ledger := by
    simp [endpointAccount, earnedEq]
  have accountCut : (endpointAccount history).cut = jointRun := by
    have payDenote : denote (earnedLedger history) = leaf.2 := by
      rw [earnedEq, certLedger, denoted]
    have tagEq :
        leaf.1 =
          Sum.inl (⟨(retained leaf.1).state, (retained leaf.1).trace⟩ : JointOccurrence) := by
      generalize htag : leaf.1 = tag at leafLeft
      cases tag with
      | inl occurrence =>
          unfold Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption.retained
          rw [Sum.elim_inl, id_eq]
      | inr _ =>
          simp only [Sum.isLeft] at leafLeft
          cases leafLeft
    unfold endpointAccount
    rw [haltedLeaf]
    dsimp
    rw [earnedTrace, indicesEq, ← traceLeaf, payDenote, runEq, ← tagEq]
  have replayCut :
      replayedAccount (retained leaf.1).state
          (retained leaf.1).trace cert.ledger =
        endpointAccount history := by
    unfold replayedAccount endpointAccount
    rw [haltedLeaf, earnedTrace, indicesEq, traceLeaf, earnedEq]
  have accepted : acceptOwnedReplay history (endpointAccount history) =
      .accept (endpointAccount history) := by
    have cutShape : (endpointAccount history).cut = [leaf] := accountCut.trans runEq
    have traceSame : (retained leaf.1).trace = cert.trace :=
      traceLeaf.trans certTrace.symm
    have paySame : denote ledger = cert.payment := by
      rw [replayLedger, certLedger, ← certPayment]
    unfold acceptOwnedReplay
    rw [issued, cutShape]
    dsimp
    rw [replayEq]
    dsimp
    simp only [decide_eq_false (fun h : ledger ≠ cert.ledger => h replayLedger),
      decide_eq_false (fun h : (endpointAccount history).ledger ≠ cert.ledger => h accountLedger),
      decide_eq_false (fun h : (retained leaf.1).trace ≠ cert.trace => h traceSame),
      decide_eq_false (fun h : denote ledger ≠ cert.payment => h paySame),
      Bool.or_false]
    rw [if_neg Bool.false_ne_true]
    rw [replayLedger, replayCut, earned_endpoint_is_admitted issued]
  exact ⟨record, leaf, history, cert, kept, member, runEq, followEq,
    by rw [← replayLedger]; exact replayEq, issued, certLedger,
    by rw [certLedger, denoted],
    certTrace.trans traceLeaf.symm, replayCut, accepted, accountCut, accountLedger⟩

/-- Missing index `[9]` and the earned prefix, both presented on the complete
paid account, are refused and that account is kept. A same-trace `jointStart`
leaf and an `inr` tag on the halted occurrence, each holding only `force`
while requesting `inspect`, are `missingRights`. The submitted account is
kept. Trace reconstruction does not grant the inspect right. The endpoint
control and tag still differ from those submissions. Heap functions are not
decided. -/
theorem owned_replay_refuses_missing_or_corrupted_evidence :
    ∃ (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat)
      (history : History (pathMachine jointSpec jointStart) jointStart
        (retained leaf.1).state)
      (cert : SourceCertificate),
      issueEarned history = some cert ∧
        cert.ledger = jointProductionLedger ∧
        denote jointEarnedLedger = 2 ∧
        denote jointProductionLedger = 4 ∧
        acceptOwnedReplay history (accountWithCut cert
            [(Sum.inr ⟨jointStart, [9]⟩, denote cert.ledger)]) =
          .reject .incoherentResidual (accountWithCut cert
            [(Sum.inr ⟨jointStart, [9]⟩, denote cert.ledger)]) ∧
          (acceptOwnedReplay history (accountWithCut cert
              [(Sum.inr ⟨jointStart, [9]⟩, denote cert.ledger)])).kept.ledger =
            jointProductionLedger ∧
          acceptOwnedReplay history (accountWithCut cert
              [(Sum.inr ⟨jointStart, jointEarnedTrace⟩, denote cert.ledger)]) =
            .reject .incoherentResidual (accountWithCut cert
              [(Sum.inr ⟨jointStart, jointEarnedTrace⟩, denote cert.ledger)]) ∧
            (acceptOwnedReplay history (accountWithCut cert
                [(Sum.inr ⟨jointStart, jointEarnedTrace⟩, denote cert.ledger)])).kept.ledger =
              jointProductionLedger ∧
          acceptOwnedReplay history
              ⟨[(Sum.inr ⟨jointStart, jointReturnTrace⟩, denote cert.ledger)],
                cert.ledger, [], {Right.force}, {Right.inspect}, none⟩ =
            .reject .missingRights
              ⟨[(Sum.inr ⟨jointStart, jointReturnTrace⟩, denote cert.ledger)],
                cert.ledger, [], {Right.force}, {Right.inspect}, none⟩ ∧
          ((endpointAccount history).cut.map fun item =>
              (sourceRetained item.1).state.control) =
            [.halted (.value jointValue)] ∧
          ((([(Sum.inr (⟨jointStart, jointReturnTrace⟩ : JointOccurrence),
                denote cert.ledger)] : JointCut).map fun item =>
              (sourceRetained item.1).state.control)) =
            [.run .start []] ∧
          (endpointAccount history).held = {Right.inspect} ∧
          (endpointAccount history).roots = [jointLeftCell, jointRightCell] ∧
          acceptOwnedReplay history
              (⟨[(Sum.inr ((⟨(sourceRetained leaf.1).state, jointReturnTrace⟩ : JointOccurrence)),
                  denote cert.ledger)],
                cert.ledger, [], {Right.force}, {Right.inspect}, none⟩ : PresentedAccount) =
            .reject .missingRights
              (⟨[(Sum.inr ((⟨(sourceRetained leaf.1).state, jointReturnTrace⟩ : JointOccurrence)),
                  denote cert.ledger)],
                cert.ledger, [], {Right.force}, {Right.inspect}, none⟩ : PresentedAccount) ∧
          ((endpointAccount history).cut.map fun item => item.1.isLeft) = [true] ∧
          ((([(Sum.inr ((⟨(sourceRetained leaf.1).state, jointReturnTrace⟩ : JointOccurrence)),
              denote cert.ledger)] : JointCut).map fun item => item.1.isLeft)) = [false] ∧
          ((endpointAccount history).cut.map fun item => (sourceRetained item.1).state) =
            [(sourceRetained leaf.1).state] ∧
          ((([(Sum.inr ((⟨(sourceRetained leaf.1).state, jointReturnTrace⟩ : JointOccurrence)),
              denote cert.ledger)] : JointCut).map fun item =>
                (sourceRetained item.1).state)) =
            [(sourceRetained leaf.1).state] := by
  obtain ⟨leaf, history, cert, runEq, _leafLeft, _payEq, _traceLeaf, haltedLeaf, indicesEq,
      productionEq, _denoted, issued, certLedger, certTrace, certPayment⟩ :=
    returned_request_is_issued
  obtain ⟨_force, earnedReplay, _both, _returnReplay, earnedTwo, productionFour, _rest⟩ :=
    joint_prefix_replays_are_the_source_ledgers
  have controlLeaf : (retained leaf.1).state.control = .halted (.value jointValue) := by
    rcases joint_returned_source_account with
      ⟨leaf', runEq', _left', _pay', _trace', _path', _halt', control',
        _lookupL, _lookupR, _history', _indices', _production', _valid', _denoted', _recorded'⟩
    obtain ⟨leafEq, _tailEq⟩ := List.cons.inj (runEq.symm.trans runEq')
    rw [leafEq]
    exact control'
  have returnWalk :
      replayAccount jointReturnTrace =
        some ((sourceRetained leaf.1).state, cert.ledger) := by
    have verified := (replay_verifies_the_earned_history history).1
    simp only [earnedTrace, earnedLedger, indicesEq, productionEq] at verified
    rw [← certLedger] at verified
    exact verified
  have replayCut :
      replayedAccount (sourceRetained leaf.1).state jointReturnTrace
          cert.ledger =
        endpointAccount history := by
    unfold replayedAccount endpointAccount
    simp only [haltedLeaf, earnedTrace, earnedLedger, indicesEq, productionEq, certLedger]
  have missingIndex : replayAccount [9] = none := forged_leaf_issues_itself.2.2.1
  have missingRefused :
      acceptOwnedReplay history (accountWithCut cert
          [(Sum.inr ⟨jointStart, [9]⟩, denote cert.ledger)]) =
        .reject .incoherentResidual (accountWithCut cert
          [(Sum.inr ⟨jointStart, [9]⟩, denote cert.ledger)]) := by
    unfold acceptOwnedReplay
    rw [issued]
    dsimp [accountWithCut, sourceRetained]
    rw [missingIndex]
  have missingKept :
      (acceptOwnedReplay history (accountWithCut cert
          [(Sum.inr ⟨jointStart, [9]⟩, denote cert.ledger)])).kept.ledger =
        jointProductionLedger := by
    rw [missingRefused]
    simp [RetainedAdmit.kept, accountWithCut, certLedger]
  have prefixWalk :
      ∃ state, replayAccount jointEarnedTrace = some (state, jointEarnedLedger) := by
    cases walked : replayAccount jointEarnedTrace with
    | none =>
        simp only [jointReplay, walked] at earnedReplay
        cases earnedReplay
    | some result =>
        cases result with
        | mk state ledger =>
            simp only [jointReplay, walked, Option.map_some] at earnedReplay
            cases Option.some.inj earnedReplay
            exact ⟨state, rfl⟩
  obtain ⟨_prefixState, prefixEq⟩ := prefixWalk
  have prefixNe : jointEarnedLedger ≠ cert.ledger := by
    rw [certLedger]
    intro eq
    have denoted := congrArg denote eq
    rw [earnedTwo, productionFour] at denoted
    omega
  have prefixRefused :
      acceptOwnedReplay history (accountWithCut cert
          [(Sum.inr ⟨jointStart, jointEarnedTrace⟩, denote cert.ledger)]) =
        .reject .incoherentResidual (accountWithCut cert
          [(Sum.inr ⟨jointStart, jointEarnedTrace⟩, denote cert.ledger)]) := by
    unfold acceptOwnedReplay
    rw [issued]
    dsimp [accountWithCut, sourceRetained]
    rw [prefixEq]
    simp only [decide_eq_true prefixNe, Bool.true_or]
    rfl
  have prefixKept :
      (acceptOwnedReplay history (accountWithCut cert
          [(Sum.inr ⟨jointStart, jointEarnedTrace⟩, denote cert.ledger)])).kept.ledger =
        jointProductionLedger := by
    rw [prefixRefused]
    simp [RetainedAdmit.kept, accountWithCut, certLedger]
  have retainInl (occurrence : JointOccurrence) :
      retained (Sum.inl occurrence) = occurrence := by
    unfold Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption.retained
    rw [Sum.elim_inl, id_eq]
  have retainInr (occurrence : JointOccurrence) :
      retained (Sum.inr occurrence) = occurrence := by
    unfold Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption.retained
    rw [Sum.elim_inr, id_eq]
  have notLedger : ¬ cert.ledger ≠ cert.ledger := fun h => h rfl
  have notTrace : ¬ jointReturnTrace ≠ cert.trace := fun h => h certTrace.symm
  have notPay : ¬ denote cert.ledger ≠ cert.payment := by
    rw [certLedger, ← certPayment]
    intro h
    exact h rfl
  have rightsInspect : cert.rights = {Right.inspect} := by
    unfold issueEarned at issued
    split at issued
    · simp at issued
    · cases issued
      simp [requiredRights, controlLeaf]
  have exposed := endpoint_admission_exposes_the_checked_views issued
  have refusesForceInspect (submitted : PresentedAccount)
      (cutShape : submitted.cut =
        [(Sum.inr ⟨jointStart, jointReturnTrace⟩, denote cert.ledger)] ∨
        submitted.cut =
          [(Sum.inr ⟨(sourceRetained leaf.1).state, jointReturnTrace⟩,
            denote cert.ledger)])
      (ledgerShape : submitted.ledger = cert.ledger)
      (heldShape : submitted.held = {Right.force})
      (requestShape : submitted.requested = {Right.inspect})
      (rivalShape : submitted.rival = none) :
      acceptOwnedReplay history submitted = .reject .missingRights submitted := by
    unfold acceptOwnedReplay
    rw [issued]
    cases cutShape with
    | inl shape | inr shape =>
        have notSubmitted : ¬ submitted.ledger ≠ cert.ledger := by
          rw [ledgerShape]
          exact notLedger
        rw [shape]
        simp only [retainInr]
        rw [returnWalk]
        simp only [decide_eq_false notLedger, decide_eq_false notSubmitted,
          decide_eq_false notTrace, decide_eq_false notPay, Bool.or_false]
        rw [if_neg Bool.false_ne_true]
        rw [replayCut]
        let presented : PresentedAccount :=
          { endpointAccount history with
              held := {Right.force}
              requested := {Right.inspect} }
        have presentedEq :
            { endpointAccount history with
                held := submitted.held
                requested := submitted.requested
                rival := submitted.rival } = presented := by
          rw [heldShape, requestShape, rivalShape]
          rfl
        rw [presentedEq]
        have missing :
            (!decide (cert.rights ⊆ presented.held) ||
                (restrict? presented.held presented.requested).isNone) = true := by
          have notSubset : ¬ ({Right.inspect} : Rights) ⊆ {Right.force} := by decide
          simp [presented, rightsInspect, restrict?, notSubset]
        have rejectedViews :=
          admitViews_missing_submitted_held cert (endpointAccount history) presented
            rfl rfl rfl exposed.1 missing
        have rejected :
            admitIssued cert presented = .reject .missingRights presented := by
          unfold admitIssued
          rw [show presented.rival = none by simp [presented, endpointAccount]]
          dsimp
          unfold admitComparable
          rw [rejectedViews]
        rw [rejected]
  have wrongState := refusesForceInspect
      ⟨[(Sum.inr ⟨jointStart, jointReturnTrace⟩, denote cert.ledger)],
        cert.ledger, [], {Right.force}, {Right.inspect}, none⟩
      (Or.inl rfl) rfl rfl rfl rfl
  have wrongTag := refusesForceInspect
      ⟨[(Sum.inr ⟨(sourceRetained leaf.1).state, jointReturnTrace⟩,
          denote cert.ledger)],
        cert.ledger, [], {Right.force}, {Right.inspect}, none⟩
      (Or.inr rfl) rfl rfl rfl rfl
  have acceptedControl :
      ((endpointAccount history).cut.map fun item =>
          (sourceRetained item.1).state.control) =
        [.halted (.value jointValue)] := by
    simp only [endpointAccount, haltedLeaf, if_true, retainInl, controlLeaf,
      List.map_cons, List.map_nil]
  have forgedControl :
      ((([(Sum.inr (⟨jointStart, jointReturnTrace⟩ : JointOccurrence),
            denote cert.ledger)] : JointCut).map fun item =>
          (sourceRetained item.1).state.control)) =
        [.run .start []] := by
    simp only [Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption.retained,
      Sum.elim_inr, jointStart, List.map_cons, List.map_nil]
    rfl
  have acceptedHeld : (endpointAccount history).held = {Right.inspect} := by
    simp only [endpointAccount, requiredRights, controlLeaf]
  have acceptedRoots : (endpointAccount history).roots = [jointLeftCell, jointRightCell] := by
    simp only [endpointAccount, rootedCells, controlLeaf, outcomeRoots, jointValue, occurrencesOf]
    rfl
  have acceptedTag :
      ((endpointAccount history).cut.map fun item => item.1.isLeft) = [true] := by
    simp only [endpointAccount, haltedLeaf, if_true, List.map_cons, List.map_nil, Sum.isLeft]
  have forgedTag :
      ((([(Sum.inr (⟨(sourceRetained leaf.1).state, jointReturnTrace⟩ : JointOccurrence),
          denote cert.ledger)] : JointCut).map
          fun item => item.1.isLeft)) = [false] := by
    simp only [List.map_cons, List.map_nil, Sum.isLeft]
  have acceptedState :
      ((endpointAccount history).cut.map fun item =>
          (sourceRetained item.1).state) =
        [(sourceRetained leaf.1).state] := by
    simp only [endpointAccount, haltedLeaf, if_true, retainInl, List.map_cons, List.map_nil]
  have forgedState :
      ((([(Sum.inr (⟨(sourceRetained leaf.1).state, jointReturnTrace⟩ : JointOccurrence),
          denote cert.ledger)] : JointCut).map
          fun item => (sourceRetained item.1).state)) =
        [(sourceRetained leaf.1).state] := by
    simp only [retainInr, List.map_cons, List.map_nil]
  exact ⟨leaf, history, cert, issued, certLedger, earnedTwo, productionFour,
    missingRefused, missingKept, prefixRefused, prefixKept, wrongState,
    acceptedControl, forgedControl, acceptedHeld, acceptedRoots, wrongTag,
    acceptedTag, forgedTag, acceptedState, forgedState⟩

private theorem retain_inl_occurrence (occurrence : JointOccurrence) :
    retained (Sum.inl occurrence) = occurrence := by
  unfold Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption.retained
  rw [Sum.elim_inl, id_eq]

private theorem retain_inr_occurrence (occurrence : JointOccurrence) :
    retained (Sum.inr occurrence) = occurrence := by
  unfold Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption.retained
  rw [Sum.elim_inr, id_eq]

/-- For any earned history, the account built from the issued trace and
ledger is the history endpoint. The role is `cert.halted`. Roots and rights
are `rootedCells` and `requiredRights` of that endpoint. `replayAccount`
returns the same state and ledger; it is not the issuer. -/
theorem replayed_account_is_the_earned_endpoint
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    {cert : SourceCertificate}
    (issued : issueEarned history = some cert) :
    replayAccount cert.trace = some (target, cert.ledger) ∧
      replayedAccount target cert.trace cert.ledger = endpointAccount history ∧
      cert.halted = isHalted target ∧
      cert.ledger = earnedLedger history ∧
      cert.trace = earnedTrace history ∧
      cert.payment = denote cert.ledger ∧
      (replayedAccount target cert.trace cert.ledger).roots = rootedCells target ∧
      (replayedAccount target cert.trace cert.ledger).held = requiredRights target ∧
      (replayedAccount target cert.trace cert.ledger).requested =
        requiredRights target ∧
      (endpointAccount history).ledger = cert.ledger := by
  obtain ⟨traceEq, ledgerEq, payEq, _, _, _, haltedEq, _, _, _, replayEq, _⟩ :=
    earned_history_is_the_passive_issuer issued
  have same :
      replayedAccount target cert.trace cert.ledger = endpointAccount history := by
    cases hhalt : isHalted target with
    | true =>
        simp [replayedAccount, endpointAccount, traceEq, ledgerEq, hhalt]
    | false =>
        simp [replayedAccount, endpointAccount, traceEq, ledgerEq, hhalt]
  refine ⟨replayEq, same, haltedEq, ledgerEq, traceEq, payEq, ?_, ?_, ?_, ?_⟩
  · simp [replayedAccount]
  · simp [replayedAccount]
  · simp [replayedAccount]
  · simp [endpointAccount, ledgerEq]

theorem accept_owned_replay_accepts_the_earned_endpoint
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    {cert : SourceCertificate}
    (issued : issueEarned history = some cert) :
    acceptOwnedReplay history (endpointAccount history) =
      .accept (endpointAccount history) := by
  obtain ⟨traceEq, ledgerEq, payEq, _, _, _, _, _, _, _, replayEq, _⟩ :=
    earned_history_is_the_passive_issuer issued
  have walk : replayAccount (earnedTrace history) = some (target, cert.ledger) := by
    simpa [traceEq] using replayEq
  have accountLedger : (endpointAccount history).ledger = cert.ledger := by
    simp [endpointAccount, ledgerEq]
  have replayCut :
      replayedAccount target (earnedTrace history) cert.ledger =
        endpointAccount history := by
    simpa [traceEq] using
      (replayed_account_is_the_earned_endpoint history issued).2.1
  have notAccount : ¬ (endpointAccount history).ledger ≠ cert.ledger :=
    fun h => h accountLedger
  have notTrace : ¬ earnedTrace history ≠ cert.trace := fun h => h traceEq.symm
  have notPay : ¬ denote cert.ledger ≠ cert.payment := fun h => h payEq.symm
  cases hhalt : isHalted target with
  | false =>
      have cutShape : (endpointAccount history).cut =
          [(Sum.inr (⟨target, earnedTrace history⟩ : JointOccurrence),
            denote (earnedLedger history))] := by
        simp [endpointAccount, hhalt]
      unfold acceptOwnedReplay
      rw [issued, cutShape]
      dsimp
      rw [retain_inr_occurrence]
      dsimp
      rw [walk]
      simp only [decide_eq_false notAccount, decide_eq_false notTrace,
        decide_eq_false notPay, Bool.or_false, not_true_eq_false, decide_false]
      rw [if_neg Bool.false_ne_true]
      rw [replayCut, earned_endpoint_is_admitted issued]
  | true =>
      have cutShape : (endpointAccount history).cut =
          [(Sum.inl (⟨target, earnedTrace history⟩ : JointOccurrence),
            denote (earnedLedger history))] := by
        simp [endpointAccount, hhalt]
      unfold acceptOwnedReplay
      rw [issued, cutShape]
      dsimp
      rw [retain_inl_occurrence]
      dsimp
      rw [walk]
      simp only [decide_eq_false notAccount, decide_eq_false notTrace,
        decide_eq_false notPay, Bool.or_false, not_true_eq_false, decide_false]
      rw [if_neg Bool.false_ne_true]
      rw [replayCut, earned_endpoint_is_admitted issued]

/-- Replay validates the submitted account. Acceptance runs `resumeAccepted`
on the canonical replayed account and the issued ledger. Refusal keeps the
submitted account, produces no suffix, and does not resume the rejected cut.
This is not `PhaseReplay.request?`: a logical trace does not authenticate a
metered frame list or replay a native effect. -/
def resumeReplayed
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (account : PresentedAccount) (suffix : Nat) : RetainedAdmit ResumedAccount :=
  match acceptOwnedReplay history account with
  | .reject reason kept =>
      .reject reason ⟨kept, kept.ledger, [], kept.cut⟩
  | .accept canonical =>
      match issueEarned history with
      | none =>
          .reject .incoherentResidual
            ⟨canonical, canonical.ledger, [], canonical.cut⟩
      | some cert =>
          .accept (resumeAccepted canonical cert.ledger suffix)

private theorem decide_or_false_eq
    {a b c d : Prop} [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    (guards : ¬ ((decide a || decide b || decide c || decide d) = true)) :
    ((¬ a ∧ ¬ b) ∧ ¬ c) ∧ ¬ d := by
  have condFalse :
      (decide a || decide b || decide c || decide d) = false :=
    Bool.eq_false_iff.mpr guards
  simpa [Bool.or_eq_false_iff, decide_eq_false_iff_not] using condFalse

/-- Acceptance on this joint source returns the earned endpoint overlaid with
the submitted held rights, request, and rival. `jointSpec` is one concrete
program. The replayed machine is the history target, so the functional heap
is that target's heap. Trace reconstruction grants no authority. A conflicting
claim or a request outside the supplied held set remains a refusal of the
submitted account. -/
theorem accepted_replay_is_the_earned_endpoint
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (account accepted : PresentedAccount)
    (granted : acceptOwnedReplay history account = .accept accepted) :
    ∃ cert : SourceCertificate,
      issueEarned history = some cert ∧
        replayAccount cert.trace = some (target, cert.ledger) ∧
        accepted = { endpointAccount history with
          held := account.held
          requested := account.requested
          rival := account.rival } ∧
        admitIssued cert accepted = .accept accepted ∧
        accepted.held = account.held ∧
        accepted.requested = account.requested ∧
        accepted.rival = account.rival ∧
        cert.rights ⊆ account.held ∧
        account.requested ⊆ account.held ∧
        cert.rights = requiredRights target ∧
        accepted.ledger = cert.ledger ∧
        accepted.roots = rootedCells target ∧
        ∀ item ∈ accepted.cut,
          (retained item.1).state = target ∧
            (retained item.1).state.world.heap = target.world.heap ∧
            (retained item.1).trace = cert.trace ∧
            item.2 = cert.payment := by
  obtain ⟨cert, issued, rightsSub, requestSub⟩ :=
    replay_acceptance_checks_the_issued_rights history account accepted granted
  have kept := replay_keeps_the_supplied_authority history account accepted granted
  have rightsTarget := earned_certificate_rights history issued
  have issuer := earned_history_is_the_passive_issuer issued
  unfold acceptOwnedReplay at granted
  split at granted
  · rename_i matchedCert leaf issuedMatch _cutShape
    have sameCert : matchedCert = cert :=
      Option.some.inj (issuedMatch.symm.trans issued)
    cases sameCert
    split at granted
    · cases granted
    · rename_i state replayedLedger replayWalk
      have separated := by
        split at granted
        · cases granted
        · rename_i guards
          exact decide_or_false_eq guards
      have replayLedger : replayedLedger = cert.ledger := by
        by_cases hEq : replayedLedger = cert.ledger
        · exact hEq
        · exact (separated.1.1.1 hEq).elim
      have traceSame : (retained leaf.1).trace = cert.trace := by
        by_cases hEq : (retained leaf.1).trace = cert.trace
        · exact hEq
        · exact (separated.1.2 hEq).elim
      have walked :
          traceReplay jointSpec jointAssignment jointStart
            (indices (pathMachine jointSpec jointStart) history) =
            some (state, replayedLedger) := by
        have replayAtTrace :
            replayAccount cert.trace = some (state, replayedLedger) := by
          simpa [traceSame] using replayWalk
        simpa [replayAccount, earnedTrace, issuer.1] using replayAtTrace
      have named :=
        replayed_endpoint_of_history jointSpec jointAssignment jointStart
          history walked
      cases named.1
      have replayImage :
          replayedAccount target (retained leaf.1).trace replayedLedger =
            endpointAccount history := by
        rw [traceSame, replayLedger]
        exact (replayed_account_is_the_earned_endpoint history issued).2.1
      dsimp at granted
      simp only [decide_eq_false separated.1.1.1, decide_eq_false separated.1.1.2,
        decide_eq_false separated.1.2, decide_eq_false separated.2,
        Bool.or_false] at granted
      rw [if_neg Bool.false_ne_true] at granted
      split at granted
      · rename_i checked hadmit
        injection granted with acceptedEq
        have checkedEq : checked = accepted := by
          have keeps := admitIssued_keeps cert accepted
          rw [acceptedEq] at hadmit
          rw [hadmit] at keeps
          simpa [RetainedAdmit.kept] using keeps
        cases checkedEq
        rw [acceptedEq] at hadmit
        have accountEq :
            accepted = { endpointAccount history with
              held := account.held
              requested := account.requested
              rival := account.rival } := by
          rw [← acceptedEq, replayImage]
        obtain ⟨_replayed, _image, _halted, _ledger, _trace, _payment, _roots,
            _held, _requested, endpointLedger⟩ :=
          replayed_account_is_the_earned_endpoint history issued
        have ledgerEq : accepted.ledger = cert.ledger := by
          rw [accountEq]
          exact endpointLedger
        have rootsEq : accepted.roots = rootedCells target := by
          rw [accountEq]
          simp [endpointAccount]
        refine ⟨cert, issued,
          (replayed_account_is_the_earned_endpoint history issued).1,
          accountEq, hadmit, kept.1, kept.2.1, kept.2.2.1, rightsSub, requestSub,
          rightsTarget, ledgerEq, rootsEq, ?_⟩
        intro item member
        rw [accountEq] at member
        cases hhalt : isHalted target with
        | true =>
            simp [endpointAccount, hhalt] at member
            cases member
            exact ⟨rfl, rfl, issuer.1.symm,
              (congrArg denote issuer.2.1.symm).trans issuer.2.2.1.symm⟩
        | false =>
            simp [endpointAccount, hhalt] at member
            cases member
            exact ⟨rfl, rfl, issuer.1.symm,
              (congrArg denote issuer.2.1.symm).trans issuer.2.2.1.symm⟩
      · cases granted
  · cases granted
  · cases granted

/-- An accepted replay resumes the canonical account and the issued ledger.
The submitted held rights, request, and rival stay. The resumed cut is the
earned endpoint cut. Refusal is the earlier retained-account law. -/
theorem accepted_replay_resumes_from_the_source
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (account accepted : PresentedAccount) (suffix : Nat)
    (granted : acceptOwnedReplay history account = .accept accepted) :
    ∃ cert : SourceCertificate,
      issueEarned history = some cert ∧
        resumeReplayed history account suffix =
          .accept (resumeAccepted accepted cert.ledger suffix) ∧
        (resumeAccepted accepted cert.ledger suffix).account = accepted ∧
        (resumeAccepted accepted cert.ledger suffix).delivered = cert.ledger ∧
        (resumeAccepted accepted cert.ledger suffix).account.held = account.held ∧
        (resumeAccepted accepted cert.ledger suffix).account.requested =
          account.requested ∧
        (resumeAccepted accepted cert.ledger suffix).account.rival =
          account.rival ∧
        (resumeAccepted accepted cert.ledger suffix).resumed =
          weightedResume jointSource suffix (endpointAccount history).cut := by
  obtain ⟨cert, issued, _replayed, accountEq, _admitted, heldSame, requestedSame,
      rivalSame, _rightsSub, _requestSub, _rightsTarget, _ledgerEq, _rootsEq,
      _machine⟩ :=
    accepted_replay_is_the_earned_endpoint history account accepted granted
  have cutEq : accepted.cut = (endpointAccount history).cut := by
    rw [accountEq]
  refine ⟨cert, issued, ?_, rfl, rfl, heldSame, requestedSame, rivalSame, ?_⟩
  · unfold resumeReplayed
    rw [granted, issued]
  · simp [resumeAccepted, cutEq]

private theorem present_ignores_an_off_spine_cell
    (cells : List CellId) (current : CellId → Option JointCellRecord)
    (cell : CellId) (value : Option JointCellRecord)
    (miss : cell ∉ cells) :
    cells.map (fun listed => (listed, Function.update current cell value listed)) =
      cells.map (fun listed => (listed, current listed)) := by
  induction cells with
  | nil => rfl
  | cons head tail ih =>
      have headNe : head ≠ cell := by
        intro eq
        exact miss (List.mem_cons.mpr (Or.inl eq.symm))
      have tailMiss : cell ∉ tail :=
        fun member => miss (List.mem_cons_of_mem head member)
      simp [Function.update_of_ne headNe, ih tailMiss]

/-- A cell outside the returned census can be written into `current` while the
spine and the census lookups stay unchanged. `Recorded` fails. Acceptance
installs the history target from `replayed_endpoint_of_history`, so the planted
entry is not the accepted machine. Finite census agreement is not that heap. -/
theorem unobserved_heap_entry_is_not_the_accepted_machine :
    ∃ (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat)
      (history : History (pathMachine jointSpec jointStart) jointStart
        (retained leaf.1).state)
      (cert : SourceCertificate) (submitted canonical : PresentedAccount)
      (cell : CellId) (planted source : JointHeap),
      jointRun = [leaf] ∧
        issueEarned history = some cert ∧
        cert.ledger = jointProductionLedger ∧
        denote cert.ledger = 4 ∧
        acceptOwnedReplay history submitted = .accept canonical ∧
        canonical = { endpointAccount history with
          held := submitted.held
          requested := submitted.requested
          rival := submitted.rival } ∧
        planted.spine = source.spine ∧
        (censusCells planted.spine).map
            (fun listed => (listed, planted.lookup listed)) =
          (censusCells source.spine).map
            (fun listed => (listed, source.lookup listed)) ∧
        planted.lookup cell = some (jointValued 9) ∧
        source.lookup cell = none ∧
        planted ≠ source ∧
        ¬ planted.Recorded ∧
        source.Recorded ∧
        (∀ item ∈ submitted.cut, (retained item.1).state.world.heap = planted) ∧
        (∀ item ∈ canonical.cut,
          (retained item.1).state = (retained leaf.1).state ∧
            (retained item.1).state.world.heap = source ∧
            (retained item.1).state.world.heap.lookup cell = none) := by
  obtain ⟨_record, leaf, history, cert, _kept, _member, runEq, _follow, replayWalk,
      issued, certLedger, _leafPay, certTrace, replayCut, _endpointAccepted, _cutEq,
      _endpointLedger⟩ := owned_return_replays_the_retained_request
  obtain ⟨leafR, runR, _leftR, _payR, _traceR, _pathR, _haltR, _controlR, _leftLookup,
      _rightLookup, _historyR, _indicesR, _productionR, _validR, _denotedR,
      recordedR⟩ := joint_returned_source_account
  have leafEq : leaf = leafR := by
    exact (List.cons.inj (runEq.symm.trans runR)).1
  have denoted : denote cert.ledger = 4 := by
    rw [certLedger]
    exact joint_prefix_replays_are_the_source_ledgers.2.2.2.2.2.1
  have issuer := earned_history_is_the_passive_issuer issued
  let source : JointHeap := (retained leaf.1).state.world.heap
  have recordedSource : source.Recorded := by
    simpa [source, leafEq] using recordedR
  let cell : CellId := ⟨0, [], 0, 1⟩
  have runLookup : (retained leaf.1).state.world.heap.lookup cell = none := by
    have mapped :
        (jointRun.map fun item =>
          (retained item.1).state.world.heap.lookup cell) = [none] := by
      rfl
    have consEq :
        (retained leaf.1).state.world.heap.lookup cell :: [] = none :: [] := by
      simpa [runEq, List.map_cons, List.map_nil] using mapped
    exact (List.cons_eq_cons.mp consEq).1
  have sourceMiss : source.lookup cell = none := by
    simpa [source] using runLookup
  have spineNone :
      Heap.lookupSpine source.spine cell = none :=
    (recordedSource cell).symm.trans sourceMiss
  have miss : cell ∉ censusCells source.spine := by
    have mapped :
        (jointRun.map fun item =>
          decide (cell ∈ censusCells (retained item.1).state.world.heap.spine)) =
          [false] := by
      rfl
    have consEq :
        decide (cell ∈ censusCells (retained leaf.1).state.world.heap.spine) :: [] =
          false :: [] := by
      simpa [runEq, List.map_cons, List.map_nil] using mapped
    exact of_decide_eq_false (by simpa [source] using (List.cons_eq_cons.mp consEq).1)
  let planted : JointHeap :=
    { source with current := Function.update source.current cell (some (jointValued 9)) }
  let plantedState : JointMachine :=
    { (retained leaf.1).state with
        world := { (retained leaf.1).state.world with heap := planted } }
  let submitted : PresentedAccount :=
    { endpointAccount history with
        cut := [(Sum.inl (⟨plantedState, (retained leaf.1).trace⟩ : JointOccurrence),
          denote cert.ledger)] }
  have spineSame : planted.spine = source.spine := rfl
  have presentSame :
      (censusCells planted.spine).map (fun listed => (listed, planted.lookup listed)) =
        (censusCells source.spine).map (fun listed => (listed, source.lookup listed)) := by
    rw [spineSame]
    unfold Mettapedia.Machines.BranchLocalNeed.NeedReference.Heap.lookup
    simp only [planted]
    exact present_ignores_an_off_spine_cell (censusCells source.spine) source.current cell
      (some (jointValued 9)) miss
  have plantedHit : planted.lookup cell = some (jointValued 9) := by
    unfold Mettapedia.Machines.BranchLocalNeed.NeedReference.Heap.lookup
    simp [planted, Function.update_self]
  have plantedDiff : planted ≠ source := by
    intro same
    have looks := congrArg (fun heap => heap.lookup cell) same
    simp [plantedHit, sourceMiss] at looks
  have notRecorded : ¬ planted.Recorded := by
    intro recorded
    have looks := recorded cell
    rw [plantedHit, spineSame, spineNone] at looks
    cases looks
  have notAccount : ¬ submitted.ledger ≠ cert.ledger := by
    intro bad
    apply bad
    simp [submitted, endpointAccount, issuer.2.1]
  have notTrace : ¬ (retained leaf.1).trace ≠ cert.trace := fun bad => bad certTrace.symm
  have notPay : ¬ denote cert.ledger ≠ cert.payment := fun bad => bad issuer.2.2.1.symm
  have cutPlanted : submitted.cut =
      [(Sum.inl (⟨plantedState, (retained leaf.1).trace⟩ : JointOccurrence),
        denote cert.ledger)] := rfl
  have acceptedPlanted :
      acceptOwnedReplay history submitted = .accept (endpointAccount history) := by
    unfold acceptOwnedReplay
    rw [issued, cutPlanted]
    dsimp
    rw [retain_inl_occurrence]
    dsimp
    rw [replayWalk]
    simp only [submitted, decide_eq_false notAccount, decide_eq_false notTrace,
      decide_eq_false notPay, Bool.or_false, not_true_eq_false, decide_false]
    rw [if_neg Bool.false_ne_true]
    rw [replayCut]
    have overlay :
        { endpointAccount history with
            held := submitted.held
            requested := submitted.requested
            rival := submitted.rival } = endpointAccount history := by
      simp [submitted]
    rw [overlay, earned_endpoint_is_admitted issued]
  obtain ⟨_certS, _issuedS, _replayS, canonicalEq, _admittedS, _heldS, _requestS,
      _rivalS, _rightsS, _requestSubset, _rightsTarget, _ledgerEqS, _rootsEqS,
      machine⟩ :=
    accepted_replay_is_the_earned_endpoint history submitted
      (endpointAccount history) acceptedPlanted
  have submittedHeap :
      ∀ item ∈ submitted.cut, (retained item.1).state.world.heap = planted := by
    intro item member
    simp [cutPlanted] at member
    cases member
    rfl
  have acceptedHeap :
      ∀ item ∈ (endpointAccount history).cut,
        (retained item.1).state = (retained leaf.1).state ∧
          (retained item.1).state.world.heap = source ∧
          (retained item.1).state.world.heap.lookup cell = none := by
    intro item member
    have itemFacts := machine item member
    refine ⟨?_, ?_, ?_⟩
    · rw [itemFacts.1]
    · rw [itemFacts.2.1]
    · rw [itemFacts.2.1, sourceMiss]
  exact ⟨leaf, history, cert, submitted, endpointAccount history, cell, planted, source,
    runEq, issued, certLedger, denoted, acceptedPlanted, canonicalEq, spineSame,
    presentSame, plantedHit, sourceMiss, plantedDiff, notRecorded, recordedSource,
    submittedHeap, acceptedHeap⟩

theorem acceptOwnedReplay_keeps_a_refused_account
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (account : PresentedAccount) {reason : Refusal} {kept : PresentedAccount}
    (refused : acceptOwnedReplay history account = .reject reason kept) :
    kept = account := by
  unfold acceptOwnedReplay at refused
  split at refused
  · split at refused
    · cases refused
      rfl
    · split at refused
      · cases refused
        rfl
      · dsimp at refused
        split at refused
        · simp at refused
        · cases refused
          rfl
  · cases refused
    rfl
  · cases refused
    rfl

theorem refused_replay_does_not_resume
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (account : PresentedAccount) (suffix : Nat) {reason : Refusal}
    {kept : PresentedAccount}
    (refused : acceptOwnedReplay history account = .reject reason kept) :
    resumeReplayed history account suffix =
      .reject reason ⟨kept, kept.ledger, [], kept.cut⟩ := by
  unfold resumeReplayed
  rw [refused]

theorem replayed_endpoint_resumes_as_the_earned_consumer
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (suffix : Nat) {cert : SourceCertificate}
    (issued : issueEarned history = some cert) :
    resumeReplayed history (endpointAccount history) suffix =
      resumeEarned history suffix ∧
      resumeEarned history suffix =
        .accept (resumeAccepted (endpointAccount history) cert.ledger suffix) ∧
      (resumeAccepted (endpointAccount history) cert.ledger suffix).delivered =
        cert.ledger ∧
      (resumeAccepted (endpointAccount history) cert.ledger suffix).resumed =
        weightedResume jointSource suffix (endpointAccount history).cut := by
  have accepted := accept_owned_replay_accepts_the_earned_endpoint history issued
  have consumed := earned_endpoint_is_consumed history suffix issued
  refine ⟨?_, consumed.1, ?_, ?_⟩
  · unfold resumeReplayed
    rw [accepted, issued]
    exact consumed.1.symm
  · simp [resumeAccepted]
  · simp [resumeAccepted]

theorem halted_replay_resumes_without_a_new_factor
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (suffix : Nat) {cert : SourceCertificate}
    (issued : issueEarned history = some cert)
    (halted : isHalted target = true) :
    resumeReplayed history (endpointAccount history) suffix =
      .accept (resumeAccepted (endpointAccount history) cert.ledger suffix) ∧
      (resumeAccepted (endpointAccount history) cert.ledger suffix).produced = [] ∧
      (resumeAccepted (endpointAccount history) cert.ledger suffix).resumed =
        (endpointAccount history).cut ∧
      (resumeAccepted (endpointAccount history) cert.ledger suffix).delivered =
        earnedLedger history ∧
      (resumeAccepted (endpointAccount history) cert.ledger suffix).account.roots =
        rootedCells target ∧
      cert.roots = rootedCells target := by
  have replayed :=
    replayed_endpoint_resumes_as_the_earned_consumer history suffix issued
  have inspected :=
    halted_inspection_keeps_the_returned_residual history suffix issued halted
  exact ⟨replayed.1.trans replayed.2.1, inspected.2.1, inspected.2.2.2.2.2.2.1,
    inspected.2.2.1, inspected.2.2.2.1, inspected.2.2.2.2.1⟩

theorem pending_replay_produces_the_suffix
    {target : JointMachine}
    (history : History (pathMachine jointSpec jointStart) jointStart target)
    (suffix : Nat) {cert : SourceCertificate}
    (issued : issueEarned history = some cert)
    (pending : isHalted target = false) :
    (resumeAccepted (endpointAccount history) cert.ledger suffix).produced =
      contributions jointSource suffix
        (⟨target, earnedTrace history⟩ : JointOccurrence) ∧
      (resumeAccepted (endpointAccount history) cert.ledger suffix).delivered =
        cert.ledger ∧
      (resumeAccepted (endpointAccount history) cert.ledger suffix).resumed =
        weightedResume jointSource suffix (endpointAccount history).cut ∧
      resumeReplayed history (endpointAccount history) suffix =
        .accept (resumeAccepted (endpointAccount history) cert.ledger suffix) := by
  have replayed :=
    replayed_endpoint_resumes_as_the_earned_consumer history suffix issued
  have cutShape : (endpointAccount history).cut =
      [(Sum.inr (⟨target, earnedTrace history⟩ : JointOccurrence),
        denote (earnedLedger history))] := by
    simp [endpointAccount, pending]
  refine ⟨?_, ?_, ?_, replayed.1.trans replayed.2.1⟩
  · simp [resumeAccepted, cutShape]
  · simp [resumeAccepted]
  · simp [resumeAccepted]

/-- The replayed pending consumer resumes to `jointRun`. That cut is also
`weightedResume` of the fuel-6 earned cut, so the suffix is the independent
whole run. The delivered ledger stays the incoming earned ledger. Duplicate
left factors stay duplicated, and swapping left with right is the reversed
ledger. `request?_split_sound` is the metered frame split; it is not applied
to this occurrence cut. -/
theorem replay_then_resume_is_the_independent_split :
    ∃ (pending : JointOccurrence)
      (history : History (pathMachine jointSpec jointStart) jointStart pending.state)
      (cert : SourceCertificate),
      issueEarned history = some cert ∧
        cert.halted = false ∧
        cert.ledger = jointEarnedLedger ∧
        denote cert.ledger = 2 ∧
        resumeReplayed history (endpointAccount history) 9 =
          .accept (resumeAccepted (endpointAccount history) cert.ledger 9) ∧
        (resumeAccepted (endpointAccount history) cert.ledger 9).delivered =
          jointEarnedLedger ∧
        (resumeAccepted (endpointAccount history) cert.ledger 9).resumed = jointRun ∧
        weightedResume jointSource 9 jointEarnedCut = jointRun ∧
        ([jointLeftFactor, jointLeftFactor] : JointLedger) ≠ [jointLeftFactor] ∧
        ([jointLeftFactor, jointRightFactor] : JointLedger).foldl
            (fun state factor => state ++ [factor]) [] =
          jointProductionLedger ∧
        ([jointRightFactor, jointLeftFactor] : JointLedger).foldl
            (fun state factor => state ++ [factor]) [] =
          jointReversedLedger ∧
        ∃ earnedPending suffix,
          jointEarnedCut = [(.inr earnedPending, (2 : Nat))] ∧
            contributions jointSource 9 earnedPending = [suffix] ∧
            suffix.2 = 2 ∧
            (suffix.1, (2 : Nat) * suffix.2) ∈ jointRun ∧
            (retained (Sum.inr earnedPending)).trace = jointEarnedTrace ∧
            (retained suffix.1).trace = jointReturnTrace ∧
            (traceReplayFrom jointSpec jointAssignment jointEarnedLedger
                earnedPending.state
                ((retained suffix.1).trace.drop jointEarnedTrace.length)).map
              Prod.snd =
              some jointProductionLedger := by
  obtain ⟨pending, history, cert, issued, ledgerEq, denoted, haltedCert, _accepted,
      delivered, whole, _payment⟩ := earned_suspension_resumes_the_halted_run
  have replayed := replayed_endpoint_resumes_as_the_earned_consumer history 9 issued
  obtain ⟨_advance, _nonempty, dupStays, _denoteDup, _dupNe, _coeff, _oneFactor, _revDen,
      _dedup, sourceOrder, reverseOrder⟩ := nonempty_duplicate_factors_stay_in_order
  obtain ⟨earnedPending, suffix, earnedCut, suffixRun, suffixPay, member, pendingTrace,
      suffixTrace, continued⟩ := joint_incoming_payment_multiplies_the_suffix
  obtain ⟨_b0, _b3, _b6, _b11, _b15, _p0, _p3, _led6, _pay6, _led11, _led15, _pay15,
      _control, split69⟩ := source_budgets_issue_the_reached_slices
  refine ⟨pending, history, cert, issued, haltedCert, ledgerEq, denoted,
    replayed.1.trans replayed.2.1, delivered, whole,
    (joint_resume_uses_the_recorded_composition 6 9).trans split69, dupStays,
    sourceOrder, reverseOrder, ⟨earnedPending, suffix, earnedCut, suffixRun, suffixPay,
      member, pendingTrace, suffixTrace, continued⟩⟩

/-- The fuel-6 pending endpoint with an empty holder is refused.
`missingRights` keeps that submitted account, and the suffix is empty.
`replay_empty_held_is_never_accepted` already rules out acceptance.
This is the retained payload on `jointSpec`, one concrete program.
Trace reconstruction does not supply the missing rights. -/
theorem empty_held_pending_keeps_the_paid_account :
    ∃ (pending : JointOccurrence)
      (history : History (pathMachine jointSpec jointStart) jointStart pending.state)
      (cert : SourceCertificate) (paid : PresentedAccount),
      issueEarned history = some cert ∧
        cert.halted = false ∧
        cert.ledger = jointEarnedLedger ∧
        denote cert.ledger = 2 ∧
        paid = { endpointAccount history with
          held := (∅ : Rights)
          requested := (∅ : Rights) } ∧
        acceptOwnedReplay history paid = .reject .missingRights paid ∧
        resumeReplayed history paid 9 =
          .reject .missingRights ⟨paid, paid.ledger, [], paid.cut⟩ := by
  obtain ⟨pending, history, cert, issued, haltedCert, ledgerEq, denoted,
      _resumeEndpoint, _delivered, _whole, _weighted, _dup, _order, _rev, _inner⟩ :=
    replay_then_resume_is_the_independent_split
  obtain ⟨traceEq, ledgerEqI, payEq, _ctrl, _work, _receipts, haltedEq, _nextCell,
      _nextEval, _clock, replayEq, _residual⟩ :=
    earned_history_is_the_passive_issuer issued
  have notHalted : isHalted pending.state = false := haltedEq.symm.trans haltedCert
  let paid : PresentedAccount :=
    { endpointAccount history with
        held := (∅ : Rights)
        requested := (∅ : Rights) }
  have exposed := endpoint_admission_exposes_the_checked_views issued
  have rightsForce : cert.rights = {Right.force} := by
    rw [earned_certificate_rights history issued]
    unfold requiredRights
    split
    · rename_i _ _ hcontrol
      simp [isHalted, hcontrol] at notHalted
    · rfl
  have missing :
      (!decide (cert.rights ⊆ paid.held) ||
          (restrict? paid.held paid.requested).isNone) = true := by
    have notSubset : ¬ ({Right.force} : Rights) ⊆ (∅ : Rights) := by decide
    simp [paid, rightsForce, notSubset, restrict?]
  have rejectedViews :=
    admitViews_missing_submitted_held cert (endpointAccount history) paid
      rfl rfl rfl exposed.1 missing
  have notAccount : ¬ paid.ledger ≠ cert.ledger := by
    intro bad
    apply bad
    simp [paid, endpointAccount, ledgerEqI]
  have notTrace : ¬ earnedTrace history ≠ cert.trace := fun bad => bad traceEq.symm
  have notPay : ¬ denote cert.ledger ≠ cert.payment := fun bad => bad payEq.symm
  have walk :
      replayAccount (earnedTrace history) = some (pending.state, cert.ledger) := by
    simpa [traceEq] using replayEq
  have replayImage :
      replayedAccount pending.state (earnedTrace history) cert.ledger =
        endpointAccount history := by
    simpa [traceEq] using
      (replayed_account_is_the_earned_endpoint history issued).2.1
  have cutShape : paid.cut =
      [(Sum.inr (⟨pending.state, earnedTrace history⟩ : JointOccurrence),
        denote (earnedLedger history))] := by
    simp [paid, endpointAccount, notHalted]
  have refused : acceptOwnedReplay history paid = .reject .missingRights paid := by
    unfold acceptOwnedReplay
    rw [issued, cutShape]
    dsimp
    rw [retain_inr_occurrence]
    dsimp
    rw [walk]
    simp only [paid, decide_eq_false notAccount, decide_eq_false notTrace,
      decide_eq_false notPay, Bool.or_false, not_true_eq_false, decide_false]
    rw [if_neg Bool.false_ne_true]
    rw [replayImage]
    have overlay :
        { endpointAccount history with
            held := paid.held,
            requested := paid.requested,
            rival := paid.rival } = paid := by
      simp [paid]
    rw [overlay]
    unfold admitIssued
    rw [show paid.rival = none by simp [paid, endpointAccount]]
    dsimp
    unfold admitComparable
    rw [rejectedViews]
  exact ⟨pending, history, cert, paid, issued, haltedCert, ledgerEq, denoted, rfl,
    refused, refused_replay_does_not_resume history paid 9 refused⟩

/-- One selection per unit of allowance, or the actual controller frontier is
exhausted. This is `Recording.stream_request_boundary` at the joint schedule.
A proper open prefix cannot certify that allowance. Phase frames, duplicate
charges, damaged phases, and over-budget selections stay in
`NativeCostLedger.Recording.PhaseReplay`. -/
theorem joint_request_stream_respects_the_allowance (fuel : Nat) :
    (stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve
        fuel jointAuthoredSnapshot).length ≤ fuel ∧
      ((stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve
          fuel jointAuthoredSnapshot).length = fuel ∨
        (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule fuel
          jointAuthoredSnapshot).search.frontier = []) :=
  stream_request_boundary (occurrenceSystem jointSpec) jointAuthoredSchedule
    jointNodeObserve fuel jointAuthoredSnapshot

theorem joint_short_open_stream_is_not_the_allowance (fuel : Nat)
    (short : (stream (occurrenceSystem jointSpec) jointAuthoredSchedule
        jointNodeObserve fuel jointAuthoredSnapshot).length < fuel)
    (pending : (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule fuel
        jointAuthoredSnapshot).search.frontier ≠ []) :
    False := by
  rcases (joint_request_stream_respects_the_allowance fuel).2 with full | empty
  · exact absurd full (Nat.ne_of_lt short)
  · exact pending empty

/-- The fuel-15 returned request is inside the qualified from-start record,
and replaying its endpoint accepts that endpoint. The observation stream
obeys the allowance boundary. A recorder enabled after the disabled first
step does not complete that from-start record: its complete result is only
the suffix. Erasing the qualified record is the plain run, which is not this
ledger. The earned prefix trace, presented on the complete paid account, is
refused. -/
theorem retained_replay_stays_in_the_qualified_request :
    ∃ (record : Prefix JointOccurrence)
      (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat)
      (history : History (pathMachine jointSpec jointStart) jointStart
        (retained leaf.1).state)
      (cert : SourceCertificate),
      (jointRecordedRun (some 15) 15).memory.2 = some record ∧
        sourceRetained leaf.1 ∈ record.items ∧
        acceptOwnedReplay history (endpointAccount history) =
          .accept (endpointAccount history) ∧
        (stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve
            15 jointAuthoredSnapshot).length ≤ 15 ∧
        ((stream (occurrenceSystem jointSpec) jointAuthoredSchedule
            jointNodeObserve 15 jointAuthoredSnapshot).length = 15 ∨
          (Snapshot.run (occurrenceSystem jointSpec) jointAuthoredSchedule 15
            jointAuthoredSnapshot).search.frontier = []) ∧
        ((jointRecordedRun (some 2) 2).memory.2).bind Prefix.complete? ≠
          (jointLateRecordedRun.memory.2).bind Prefix.complete? ∧
        stream (occurrenceSystem jointSpec) jointAuthoredSchedule jointNodeObserve 2
            jointAuthoredSnapshot =
          [WorkOccurrence.root jointStart] ++
            stream (occurrenceSystem jointSpec) jointAuthoredSchedule
              jointNodeObserve 1 (jointPlainRun 1) ∧
        erase (jointRecordedRun (some 15) 15) = jointPlainRun 15 ∧
        acceptOwnedReplay history
            ⟨[(Sum.inr (⟨jointStart, jointEarnedTrace⟩ : JointOccurrence),
                denote cert.ledger)],
              cert.ledger, cert.roots, cert.rights, cert.rights, none⟩ =
          .reject .incoherentResidual
            ⟨[(Sum.inr (⟨jointStart, jointEarnedTrace⟩ : JointOccurrence),
                denote cert.ledger)],
              cert.ledger, cert.roots, cert.rights, cert.rights, none⟩ ∧
          denote jointEarnedLedger = 2 ∧
          denote cert.ledger = 4 := by
  obtain ⟨record, leaf, history, cert, recorded, member, _runEq, _follow, _replayWalk,
      issued, certLedger, _denoted, _certTrace, _replayCut, accepted, _cutEq, _ledgerEq⟩ :=
    owned_return_replays_the_retained_request
  have boundary := joint_request_stream_respects_the_allowance 15
  have late := late_recording_cannot_complete_the_earlier_source_history
  have erasedRun := joint_recorded_run_erases (some 15) 15
  have earnedTwo := joint_prefix_replays_are_the_source_ledgers.2.2.2.2.1
  have productionFour := joint_prefix_replays_are_the_source_ledgers.2.2.2.2.2.1
  have prefixNe : jointEarnedLedger ≠ cert.ledger := by
    intro eq
    have denoted := congrArg denote eq
    rw [earnedTwo, certLedger, productionFour] at denoted
    omega
  have prefixWalk :
      ∃ state, replayAccount jointEarnedTrace = some (state, jointEarnedLedger) := by
    have mapped := joint_prefix_replays_are_the_source_ledgers.2.1
    cases walked : replayAccount jointEarnedTrace with
    | none =>
        simp [jointReplay, walked] at mapped
    | some result =>
        cases result with
        | mk state ledger =>
            simp [jointReplay, walked] at mapped
            cases mapped
            exact ⟨state, rfl⟩
  obtain ⟨_prefixState, prefixEq⟩ := prefixWalk
  have prefixRefused :
      acceptOwnedReplay history
          ⟨[(Sum.inr (⟨jointStart, jointEarnedTrace⟩ : JointOccurrence),
              denote cert.ledger)],
            cert.ledger, cert.roots, cert.rights, cert.rights, none⟩ =
        .reject .incoherentResidual
          ⟨[(Sum.inr (⟨jointStart, jointEarnedTrace⟩ : JointOccurrence),
              denote cert.ledger)],
            cert.ledger, cert.roots, cert.rights, cert.rights, none⟩ := by
    unfold acceptOwnedReplay
    rw [issued]
    simp only [retain_inr_occurrence]
    rw [prefixEq]
    simp only [decide_eq_true prefixNe, Bool.true_or]
    rfl
  exact ⟨record, leaf, history, cert, recorded, member, accepted, boundary.1, boundary.2,
    late.2.2.2, late.2.2.1, erasedRun, prefixRefused, earnedTwo,
    by rw [certLedger]; exact productionFour⟩

/-- Refusal keeps the submitted account. A forged ledger and a missing trace
are refused. A replayed occurrence with empty roots, force held, and an
inspect request is `missingRights`; that submitted account is kept. Held is
not rebuilt from `requiredRights`. The erased current is rebuilt by replay
because its held set is the certificate's inspect right, and
`consumeAuthenticated` still refuses that erased submission. Neither
reconstruction is permission to execute the submitted representation.
Lookups are concrete cell results. -/
theorem owned_replay_separates_reconstruction_from_refusal :
    ∃ (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat)
      (history : History (pathMachine jointSpec jointStart) jointStart
        (retained leaf.1).state)
      (cert : SourceCertificate),
      issueEarned history = some cert ∧
        acceptOwnedReplay history
            { endpointAccount history with ledger := jointEarnedLedger } =
          .reject .incoherentResidual
            { endpointAccount history with ledger := jointEarnedLedger } ∧
        denote jointEarnedLedger = 2 ∧
        denote cert.ledger = 4 ∧
        acceptOwnedReplay history
            { endpointAccount history with cut := [] } =
          .reject .incompleteResidual
            { endpointAccount history with cut := [] } ∧
        acceptOwnedReplay history
            ⟨[(Sum.inr (⟨jointStart, [9]⟩ : JointOccurrence), denote cert.ledger)],
              cert.ledger, cert.roots, cert.rights, cert.rights, none⟩ =
          .reject .incoherentResidual
            ⟨[(Sum.inr (⟨jointStart, [9]⟩ : JointOccurrence), denote cert.ledger)],
              cert.ledger, cert.roots, cert.rights, cert.rights, none⟩ ∧
        acceptOwnedReplay history
            ⟨[(Sum.inl (⟨(sourceRetained leaf.1).state,
                  (sourceRetained leaf.1).trace⟩ : JointOccurrence),
                denote cert.ledger)],
              cert.ledger, [], {Right.force}, {Right.inspect}, none⟩ =
          .reject .missingRights
            ⟨[(Sum.inl (⟨(sourceRetained leaf.1).state,
                  (sourceRetained leaf.1).trace⟩ : JointOccurrence),
                denote cert.ledger)],
              cert.ledger, [], {Right.force}, {Right.inspect}, none⟩ ∧
        (endpointAccount history).roots = [jointLeftCell, jointRightCell] ∧
        (endpointAccount history).held = {Right.inspect} ∧
        acceptOwnedReplay history
            ⟨jointErasedRun, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩ =
          .accept (endpointAccount history) ∧
        ((endpointAccount history).cut.map fun item =>
            (sourceRetained item.1).state.world.heap.lookup jointLeftCell) =
          [some (jointValued 3)] ∧
        (jointErasedRun.map fun item =>
            (sourceRetained item.1).state.world.heap.lookup jointLeftCell) =
          [none] ∧
        consumeAuthenticated history
            ⟨jointErasedRun, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩ 0 =
          .reject .changedDependency
            ⟨⟨jointErasedRun, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩,
              cert.ledger, [], jointErasedRun⟩ ∧
        resumeReplayed history
            { endpointAccount history with ledger := jointEarnedLedger } 0 =
          .reject .incoherentResidual
            ⟨{ endpointAccount history with ledger := jointEarnedLedger },
              jointEarnedLedger, [], (endpointAccount history).cut⟩ ∧
        resumeReplayed history
            ⟨jointErasedRun, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩ 0 =
          .accept (resumeAccepted (endpointAccount history) cert.ledger 0) ∧
        (resumeAccepted (endpointAccount history) cert.ledger 0).account =
          endpointAccount history ∧
        (resumeAccepted (endpointAccount history) cert.ledger 0).produced = [] := by
  obtain ⟨_record, leaf, history, cert, _recorded, _member, runEq, _follow, replayWalk,
      issued, certLedger, _denoted, certTrace, replayCut, _accepted, cutEq, _ledgerEq⟩ :=
    owned_return_replays_the_retained_request
  obtain ⟨leafR, runR, leafLeft, _payR, _traceR, _pathR, haltedR, controlR, leftLookup,
      _rightLookup, _historyR, _indicesR, _productionR, _validR, _denotedR, _recordedR⟩ :=
    joint_returned_source_account
  have leafEq : leaf = leafR := by
    obtain ⟨eqLeaf, _nil⟩ := List.cons.inj (runEq.symm.trans runR)
    exact eqLeaf
  have earnedTwo := joint_prefix_replays_are_the_source_ledgers.2.2.2.2.1
  have productionFour := joint_prefix_replays_are_the_source_ledgers.2.2.2.2.2.1
  have issuer := earned_history_is_the_passive_issuer issued
  have ledgerNe : jointEarnedLedger ≠ cert.ledger := by
    intro eq
    have same := congrArg denote eq
    rw [earnedTwo, certLedger, productionFour] at same
    omega
  let forged : PresentedAccount :=
    { endpointAccount history with ledger := jointEarnedLedger }
  have forgedRefused : acceptOwnedReplay history forged =
      .reject .incoherentResidual forged := by
    have cutF : forged.cut = [leaf] := by
      simp [forged, cutEq, runEq]
    unfold acceptOwnedReplay
    rw [issued, cutF]
    dsimp
    rw [replayWalk]
    simp only [forged, decide_eq_true ledgerNe, Bool.or_true, Bool.true_or]
    rfl
  let bare : PresentedAccount := { endpointAccount history with cut := [] }
  have bareRefused : acceptOwnedReplay history bare =
      .reject .incompleteResidual bare := by
    unfold acceptOwnedReplay
    rw [issued]
  let missingTrace : PresentedAccount :=
    ⟨[(Sum.inr (⟨jointStart, [9]⟩ : JointOccurrence), denote cert.ledger)],
      cert.ledger, cert.roots, cert.rights, cert.rights, none⟩
  have missingIndex : replayAccount [9] = none := forged_leaf_issues_itself.2.2.1
  have missingRefused : acceptOwnedReplay history missingTrace =
      .reject .incoherentResidual missingTrace := by
    unfold acceptOwnedReplay
    rw [issued]
    simp only [missingTrace, retain_inr_occurrence]
    rw [missingIndex]
  let missingRoots : PresentedAccount :=
    ⟨[(Sum.inl (⟨(sourceRetained leaf.1).state,
          (sourceRetained leaf.1).trace⟩ : JointOccurrence),
        denote cert.ledger)],
      cert.ledger, [], {Right.force}, {Right.inspect}, none⟩
  have notLedger : ¬ cert.ledger ≠ cert.ledger := fun h => h rfl
  have notTrace : ¬ (sourceRetained leaf.1).trace ≠ cert.trace := fun h => h certTrace.symm
  have notPay : ¬ denote cert.ledger ≠ cert.payment := by
    rw [← issuer.2.2.1]
    intro h
    exact h rfl
  have rootsEndpoint : (endpointAccount history).roots =
      [jointLeftCell, jointRightCell] := by
    have controlLeaf : (sourceRetained leaf.1).state.control =
        .halted (.value jointValue) := by
      rw [leafEq]
      exact controlR
    simp [endpointAccount, rootedCells, controlLeaf, outcomeRoots, jointValue, occurrencesOf]
  have heldEndpoint : (endpointAccount history).held = {Right.inspect} := by
    have controlLeaf : (sourceRetained leaf.1).state.control =
        .halted (.value jointValue) := by
      rw [leafEq]
      exact controlR
    simp [endpointAccount, requiredRights, controlLeaf]
  have requestedEndpoint : (endpointAccount history).requested = {Right.inspect} := by
    have controlLeaf : (sourceRetained leaf.1).state.control =
        .halted (.value jointValue) := by
      rw [leafEq]
      exact controlR
    simp [endpointAccount, requiredRights, controlLeaf]
  have rivalEndpoint : (endpointAccount history).rival = none := by
    unfold endpointAccount
    rfl
  have forceInspectRefused : acceptOwnedReplay history missingRoots =
      .reject .missingRights missingRoots := by
    unfold acceptOwnedReplay
    rw [issued]
    simp only [missingRoots, retain_inl_occurrence]
    rw [replayWalk]
    simp only [decide_eq_false notLedger, decide_eq_false notTrace,
      decide_eq_false notPay, Bool.or_false]
    rw [if_neg Bool.false_ne_true]
    rw [replayCut]
    let presented : PresentedAccount :=
      { endpointAccount history with
          held := {Right.force}
          requested := {Right.inspect} }
    have presentedEq :
        { endpointAccount history with
            held := missingRoots.held
            requested := missingRoots.requested
            rival := missingRoots.rival } = presented := by
      simp [missingRoots, presented, rivalEndpoint]
    rw [presentedEq]
    have rightsInspect : cert.rights = {Right.inspect} := by
      unfold issueEarned at issued
      split at issued
      · simp at issued
      · cases issued
        simpa [endpointAccount] using heldEndpoint
    have exposed := endpoint_admission_exposes_the_checked_views issued
    have missing :
        (!decide (cert.rights ⊆ presented.held) ||
            (restrict? presented.held presented.requested).isNone) = true := by
      have notSubset : ¬ ({Right.inspect} : Rights) ⊆ {Right.force} := by decide
      simp [presented, rightsInspect, restrict?, notSubset]
    have rejectedViews :=
      admitViews_missing_submitted_held cert (endpointAccount history) presented
        rfl rfl rfl exposed.1 missing
    have rejected : admitIssued cert presented = .reject .missingRights presented := by
      unfold admitIssued
      rw [show presented.rival = none by simp [presented, rivalEndpoint]]
      dsimp
      unfold admitComparable
      rw [rejectedViews]
    rw [rejected]
  have haltedTarget : isHalted (sourceRetained leaf.1).state = true := by
    rw [leafEq]
    exact haltedR
  have factors := (issued_passive_factors_are_the_earned_ledger history issued).1
  have historyTrace : (sourceRetained leaf.1).trace = earnedTrace history :=
    certTrace.symm.trans issuer.1
  have historyLedger : earnedLedger history =
      (readGraph (sourceRetained leaf.1).state.world.receipts.nodes).factors := by
    rw [← issuer.2.2.2.2.2.1]
    exact factors.symm
  have cutIssued : issueCut jointRun = some cert := by
    have cutLeaf : issueCut jointRun = issueLeaf leaf := by
      simp [issueCut, runEq]
    cases hleaf : issueLeaf leaf with
    | none =>
        have mapped : (issueCut jointRun).map SourceCertificate.ledger =
            some jointProductionLedger := by
          obtain ⟨_b0, _b3, _b6, _b11, b15, _p0, _p3, _led6, _pay6, _led11, led15,
              _pay15, _ctrl, _split⟩ := source_budgets_issue_the_reached_slices
          simpa [b15] using led15
        simp [cutLeaf, hleaf] at mapped
    | some cert' =>
        have issued' :=
          issueEarned_matches_issueLeaf history rfl historyTrace historyLedger hleaf
        have cert'Eq : cert' = cert := by
          exact Option.some.inj (issued'.symm.trans issued)
        simp [cutLeaf, hleaf, cert'Eq]
  let erasedAccount : PresentedAccount :=
    ⟨jointErasedRun, cert.ledger, cert.roots, cert.rights, cert.rights, none⟩
  have asInl : leaf.1 = Sum.inl (sourceRetained leaf.1) := by
    have leftFlag : leaf.1.isLeft = true := by
      rw [leafEq]
      exact leafLeft
    cases htag : leaf.1 with
    | inl _ =>
        congr 1
    | inr _ =>
        simp [Sum.isLeft, htag] at leftFlag
  have erasedShape : jointErasedRun =
      [(Sum.inl (eraseJointCurrent (sourceRetained leaf.1)), leaf.2)] := by
    unfold jointErasedRun
    rw [runEq]
    simp only [List.map_cons, List.map_nil]
    conv_lhs => rw [asInl]
    simp only [Sum.map_inl]
  have acceptedLookup :
      ((endpointAccount history).cut.map fun item =>
          (sourceRetained item.1).state.world.heap.lookup jointLeftCell) =
        [some (jointValued 3)] := by
    rw [cutEq, runEq, leafEq]
    simp only [List.map_cons, List.map_nil]
    exact congrArg (fun result => [result]) leftLookup
  have erasedLookup :
      (jointErasedRun.map fun item =>
          (sourceRetained item.1).state.world.heap.lookup jointLeftCell) =
        [none] := by
    rw [erasedShape]
    simp only [List.map_cons, List.map_nil, retain_inl_occurrence]
    unfold eraseJointCurrent
      Mettapedia.Machines.BranchLocalNeed.NeedReference.Heap.lookup
    rfl
  have erasedRebuilt : acceptOwnedReplay history erasedAccount =
      .accept (endpointAccount history) := by
    have traceKept : (eraseJointCurrent (sourceRetained leaf.1)).trace =
        (sourceRetained leaf.1).trace := rfl
    have cutE : erasedAccount.cut =
        [(Sum.inl (eraseJointCurrent (sourceRetained leaf.1)), leaf.2)] := by
      simp only [erasedAccount, erasedShape]
    unfold acceptOwnedReplay
    rw [issued, cutE]
    dsimp
    rw [retain_inl_occurrence, traceKept]
    rw [replayWalk]
    simp only [erasedAccount, decide_eq_false notTrace, decide_eq_false notPay,
      Bool.or_false, not_true_eq_false, decide_false]
    rw [if_neg Bool.false_ne_true]
    have rightsEq : cert.rights = (endpointAccount history).requested := by
      have mapped := source_issue_reads_the_three_cuts.2.2.2.2.2.1
      rw [cutIssued] at mapped
      exact (Option.some.inj mapped).trans requestedEndpoint.symm
    have heldEq : cert.rights = (endpointAccount history).held :=
      rightsEq.trans (requestedEndpoint.trans heldEndpoint.symm)
    rw [replayCut]
    have canonicalAccount :
        { endpointAccount history with
            held := cert.rights,
            requested := cert.rights,
            rival := none } = endpointAccount history := by
      rw [heldEq, ← rivalEndpoint]
      have sameRequest :
          (endpointAccount history).held = (endpointAccount history).requested :=
        heldEndpoint.trans requestedEndpoint.symm
      nth_rw 2 [sameRequest]
    rw [canonicalAccount, earned_endpoint_is_admitted issued]
  have erasedRaw :
      (issueCut jointRun).bind (fun issuedCert =>
        some (admitIssued issuedCert ⟨jointErasedRun, issuedCert.ledger, issuedCert.roots,
          issuedCert.rights, issuedCert.rights, none⟩)) =
      (issueCut jointRun).bind (fun issuedCert =>
        some (.reject .changedDependency ⟨jointErasedRun, issuedCert.ledger,
          issuedCert.roots, issuedCert.rights, issuedCert.rights, none⟩)) := by
    rfl
  have erasedRefused : consumeAuthenticated history erasedAccount 0 =
      .reject .changedDependency
        ⟨erasedAccount, cert.ledger, [], jointErasedRun⟩ := by
    rw [cutIssued] at erasedRaw
    exact issued_refusal_does_not_resume history erasedAccount 0 issued
      (Option.some.inj erasedRaw)
  have forgedResume := refused_replay_does_not_resume history forged 0 forgedRefused
  have erasedResume : resumeReplayed history erasedAccount 0 =
      .accept (resumeAccepted (endpointAccount history) cert.ledger 0) := by
    unfold resumeReplayed
    rw [erasedRebuilt, issued]
  have haltedPacket :=
    halted_replay_resumes_without_a_new_factor history 0 issued haltedTarget
  refine ⟨leaf, history, cert, issued, forgedRefused, earnedTwo,
    by rw [certLedger]; exact productionFour, bareRefused, missingRefused, forceInspectRefused,
    rootsEndpoint, heldEndpoint, erasedRebuilt, acceptedLookup, erasedLookup, erasedRefused,
    by simpa [forged] using forgedResume, erasedResume, ?_, haltedPacket.2.1⟩
  · simp [resumeAccepted]

/-- The canonical replayed return is the paid custody of a reached shared
host. Retiring client 0 leaves client 1 live, with both returned cells still
unread. Passive inspection does not change that custody or its delivered
list. The resumed halted account produces no new factor. -/
theorem replayed_return_keeps_the_other_consumers_roots (suffix : Nat) :
    ∃ (target : JointMachine)
      (history : History (pathMachine jointSpec jointStart) jointStart target)
      (cert : SourceCertificate)
      (account : PresentedAccount)
      (host : Host (SharedConsumers JointLedger) (Fin 2) (PaidCustody × List JointLedger))
      (retired : SharedConsumers JointLedger),
      issueEarned history = some cert ∧
        account = endpointAccount history ∧
        replayedAccount target cert.trace cert.ledger = account ∧
        acceptOwnedReplay history account = .accept account ∧
        resumeReplayed history account suffix =
          .accept (resumeAccepted account cert.ledger suffix) ∧
        (resumeAccepted account cert.ledger suffix).produced = [] ∧
        (resumeAccepted account cert.ledger suffix).delivered = jointProductionLedger ∧
        (retired.seats 0).live = false ∧
        (retired.seats 1).live = true ∧
        unread retired.ownership.log 1 = [jointLeftCell, jointRightCell] ∧
        (submit (sharedSystem cert.ledger) (frameAct cert.ledger) host.epoch
          (SharedAct.inspect 0) host).world = host.world ∧
        (submit (sharedSystem cert.ledger) (frameAct cert.ledger) host.epoch
          (SharedAct.inspect 0) host).delivered = host.delivered := by
  obtain ⟨target, history, cert, account, _accepted, _handles, host, retired, _cutIssued,
      issuedHistory, accountEq, _admitted, _ledgerEq, _paymentDenote, _denoted, _rights,
      _halted, _roots, _accountLedger, _held, _requested, _cutFour, _paired, _different,
      acceptedEq, producedNil, _resumedCut, deliveredPaid, _emptyDelivered, _emptyObs,
      _retainedRet, dead, alive, _handleKept, _auth, _unreadZero, unreadOne, _submitDelivered,
      _submitLedger, _submitPayment, _submitRights, _submitCut, _submitObs, _nonempty⟩ :=
    returned_retirement_keeps_the_nonempty_paid_account suffix
  have replayed := replayed_account_is_the_earned_endpoint history issuedHistory
  have accepted := accept_owned_replay_accepts_the_earned_endpoint history issuedHistory
  have resumed :=
    replayed_endpoint_resumes_as_the_earned_consumer history suffix issuedHistory
  have inspected := submit_inspect_keeps_the_paid_frame cert.ledger host
  refine ⟨target, history, cert, account, host, retired, issuedHistory, accountEq, ?_, ?_,
      ?_, ?_, ?_, dead, alive, unreadOne, inspected.1, inspected.2⟩
  · rw [accountEq]
    exact replayed.2.1
  · rw [accountEq]
    exact accepted
  · rw [accountEq]
    exact resumed.1.trans resumed.2.1
  · simpa [acceptedEq] using producedNil
  · simpa [acceptedEq] using deliveredPaid

/-- Checked fields other than the rival determine `admitViews`. A different
rival returns the same branch on the account that was actually presented. -/
private theorem admitViews_checked
    (issued : SourceCertificate) (account presented : PresentedAccount)
    (cutEq : presented.cut = account.cut)
    (ledgerEq : presented.ledger = account.ledger)
    (rootsEq : presented.roots = account.roots)
    (heldEq : presented.held = account.held)
    (rightsSame :
      (!decide (issued.rights ⊆ presented.held) ||
          (restrict? presented.held presented.requested).isNone) =
        (!decide (issued.rights ⊆ account.held) ||
          (restrict? account.held account.requested).isNone))
    (accepted : admitViews issued account = .accept account) :
    admitViews issued presented = .accept presented := by
  rcases account with ⟨cut, ledger, roots, held, requested, oldRival⟩
  rcases presented with ⟨presentedCut, presentedLedger, presentedRoots,
    presentedHeld, presentedRequest, presentedRival⟩
  simp only at cutEq ledgerEq rootsEq heldEq
  subst presentedCut
  subst presentedLedger
  subst presentedRoots
  subst presentedHeld
  unfold admitViews at accepted ⊢
  dsimp only at accepted ⊢
  rw [rightsSame]
  repeat' first
    | (solve | cases accepted)
    | split at accepted
  all_goals simp_all
  all_goals aesop

/-- The same checked prefix reaches `missingRights` when the submitted
request is not granted by the replayed held rights. -/
private theorem admitViews_missing_rights
    (issued : SourceCertificate) (account presented : PresentedAccount)
    (cutEq : presented.cut = account.cut)
    (ledgerEq : presented.ledger = account.ledger)
    (rootsEq : presented.roots = account.roots)
    (heldEq : presented.held = account.held)
    (accepted : admitViews issued account = .accept account)
    (missing :
      (!decide (issued.rights ⊆ presented.held) ||
          (restrict? presented.held presented.requested).isNone) = true) :
    admitViews issued presented = .reject .missingRights presented := by
  rcases account with ⟨cut, ledger, roots, held, requested, oldRival⟩
  rcases presented with ⟨presentedCut, presentedLedger, presentedRoots,
    presentedHeld, presentedRequest, presentedRival⟩
  simp only at cutEq ledgerEq rootsEq heldEq
  subst presentedCut
  subst presentedLedger
  subst presentedRoots
  subst presentedHeld
  unfold admitViews at accepted ⊢
  dsimp only at accepted ⊢
  rw [missing]
  repeat' first
    | (solve | cases accepted)
    | split at accepted
  all_goals simp_all
  all_goals aesop

/-- An empty request on the fuel-6 pending holder is accepted. Held stays
`{Right.force}`. Suffix 9 delivers `jointEarnedLedger`, resumes `jointRun`,
and produces that pending occurrence's source suffix. `jointSpec` is one
concrete program. The empty request does not grant authority. -/
theorem paid_pending_empty_request_resumes_the_source :
    ∃ (pending : JointOccurrence)
      (history : History (pathMachine jointSpec jointStart) jointStart pending.state)
      (cert : SourceCertificate) (narrowed : PresentedAccount),
      issueEarned history = some cert ∧
        cert.halted = false ∧
        cert.ledger = jointEarnedLedger ∧
        denote cert.ledger = 2 ∧
        narrowed = { endpointAccount history with requested := (∅ : Rights) } ∧
        narrowed.held = {Right.force} ∧
        narrowed.requested = (∅ : Rights) ∧
        narrowed.rival = none ∧
        acceptOwnedReplay history narrowed = .accept narrowed ∧
        resumeReplayed history narrowed 9 =
          .accept (resumeAccepted narrowed cert.ledger 9) ∧
        (resumeAccepted narrowed cert.ledger 9).account = narrowed ∧
        (resumeAccepted narrowed cert.ledger 9).delivered = jointEarnedLedger ∧
        (resumeAccepted narrowed cert.ledger 9).resumed = jointRun ∧
        (resumeAccepted narrowed cert.ledger 9).produced =
          contributions jointSource 9
            (⟨pending.state, earnedTrace history⟩ : JointOccurrence) := by
  obtain ⟨pending, history, cert, issued, haltedCert, ledgerEq, denoted,
      _resumeEndpoint, _delivered, whole, _weighted, _dup, _order, _rev, _inner⟩ :=
    replay_then_resume_is_the_independent_split
  obtain ⟨traceEq, ledgerEqI, payEq, _ctrl, _work, _receipts, haltedEq, _nextCell,
      _nextEval, _clock, replayEq, _residual⟩ :=
    earned_history_is_the_passive_issuer issued
  have notHalted : isHalted pending.state = false := haltedEq.symm.trans haltedCert
  let narrowed : PresentedAccount :=
    { endpointAccount history with requested := (∅ : Rights) }
  have exposed := endpoint_admission_exposes_the_checked_views issued
  have rightsForce : cert.rights = {Right.force} := by
    rw [earned_certificate_rights history issued]
    unfold requiredRights
    split
    · rename_i _ _ hcontrol
      simp [isHalted, hcontrol] at notHalted
    · rfl
  have heldForce : narrowed.held = {Right.force} := by
    simp only [narrowed, endpointAccount]
    exact (earned_certificate_rights history issued).symm.trans rightsForce
  have requestedEmpty : narrowed.requested = (∅ : Rights) := by
    simp [narrowed]
  have rivalNone : narrowed.rival = none := by
    simp [narrowed, endpointAccount]
  have narrowedRights :
      (!decide (cert.rights ⊆ narrowed.held) ||
          (restrict? narrowed.held narrowed.requested).isNone) =
        (!decide (cert.rights ⊆ (endpointAccount history).held) ||
          (restrict? (endpointAccount history).held
            (endpointAccount history).requested).isNone) := by
    have heldEndpoint : (endpointAccount history).held = {Right.force} := by
      simpa [narrowed] using heldForce
    have requestedEndpoint : (endpointAccount history).requested = {Right.force} := by
      simp only [endpointAccount]
      exact (earned_certificate_rights history issued).symm.trans rightsForce
    simp [narrowed, heldEndpoint, requestedEndpoint, rightsForce, restrict?]
  have narrowedAdmitted : admitIssued cert narrowed = .accept narrowed := by
    have views :=
      admitViews_checked cert (endpointAccount history) narrowed rfl rfl rfl rfl
        narrowedRights exposed.1
    have residual : residualAgrees cert narrowed = true := by
      change residualAgrees cert (endpointAccount history) = true
      exact exposed.2
    unfold admitIssued
    rw [show narrowed.rival = none by simp [narrowed, endpointAccount]]
    dsimp
    unfold admitComparable
    rw [views, residual]
    rfl
  have notAccount : ¬ narrowed.ledger ≠ cert.ledger := by
    intro bad
    apply bad
    simp [narrowed, endpointAccount, ledgerEqI]
  have notTrace : ¬ earnedTrace history ≠ cert.trace := fun bad => bad traceEq.symm
  have notPay : ¬ denote cert.ledger ≠ cert.payment := fun bad => bad payEq.symm
  have walk :
      replayAccount (earnedTrace history) = some (pending.state, cert.ledger) := by
    simpa [traceEq] using replayEq
  have replayImage :
      replayedAccount pending.state (earnedTrace history) cert.ledger =
        endpointAccount history := by
    simpa [traceEq] using
      (replayed_account_is_the_earned_endpoint history issued).2.1
  have cutShape : narrowed.cut =
      [(Sum.inr (⟨pending.state, earnedTrace history⟩ : JointOccurrence),
        denote (earnedLedger history))] := by
    simp [narrowed, endpointAccount, notHalted]
  have narrowedAccepted : acceptOwnedReplay history narrowed = .accept narrowed := by
    unfold acceptOwnedReplay
    rw [issued, cutShape]
    dsimp
    rw [retain_inr_occurrence]
    dsimp
    rw [walk]
    simp only [narrowed, decide_eq_false notAccount, decide_eq_false notTrace,
      decide_eq_false notPay, Bool.or_false, not_true_eq_false, decide_false]
    rw [if_neg Bool.false_ne_true]
    rw [replayImage]
    have overlay :
        { endpointAccount history with
            held := narrowed.held,
            requested := narrowed.requested,
            rival := narrowed.rival } = narrowed := by
      rfl
    rw [overlay, narrowedAdmitted]
  have cutSame : narrowed.cut = (endpointAccount history).cut := by
    simp [narrowed]
  have resumedEq :
      (resumeAccepted narrowed cert.ledger 9).resumed = jointRun := by
    simp only [resumeAccepted, cutSame] at whole ⊢
    exact whole
  have producedEq :
      (resumeAccepted narrowed cert.ledger 9).produced =
        contributions jointSource 9
          (⟨pending.state, earnedTrace history⟩ : JointOccurrence) := by
    have base :=
      (pending_replay_produces_the_suffix history 9 issued notHalted).1
    simp only [resumeAccepted, cutSame] at base ⊢
    exact base
  refine ⟨pending, history, cert, narrowed, issued, haltedCert, ledgerEq, denoted, rfl,
    heldForce, requestedEmpty, rivalNone, narrowedAccepted, ?_, rfl, ?_, resumedEq,
    producedEq⟩
  · unfold resumeReplayed
    rw [narrowedAccepted, issued]
  · simp [resumeAccepted, ledgerEq]

/-- The replayed machine still supplies the cut, ledger, roots, and held
rights. A conflicting `jointOwnerClaim 1` is refused by `Scoped.merge?` and
the original paid account is kept. Re-presenting the issued claim is
`Scoped.merge_self` when that production ledger is `Valid`; the accepted
account still carries the claim. Diagonal equality does not add execution
permission. An empty request is kept, and `{Right.force}` on the halted
machine is `missingRights`. -/
theorem owned_replay_checks_the_submitted_claim_and_request :
    ∃ (leaf : (JointOccurrence ⊕ JointOccurrence) × Nat)
      (history : History (pathMachine jointSpec jointStart) jointStart
        (retained leaf.1).state)
      (cert : SourceCertificate),
      issueEarned history = some cert ∧
        cert.ledger = jointProductionLedger ∧
        denote cert.ledger = 4 ∧
        Valid cert.claim.productions ∧
        Scoped.merge? cert.claim cert.claim = some cert.claim ∧
        Scoped.merge? cert.claim (jointOwnerClaim 1) = none ∧
        acceptOwnedReplay history
            { endpointAccount history with rival := some (jointOwnerClaim 1) } =
          .reject .incoherentResidual
            { endpointAccount history with rival := some (jointOwnerClaim 1) } ∧
        ({ endpointAccount history with rival := some (jointOwnerClaim 1) }).ledger =
          jointProductionLedger ∧
        ({ endpointAccount history with rival := some (jointOwnerClaim 1) }).rival =
          some (jointOwnerClaim 1) ∧
        acceptOwnedReplay history
            { endpointAccount history with rival := some cert.claim } =
          .accept { endpointAccount history with rival := some cert.claim } ∧
        ({ endpointAccount history with rival := some cert.claim }).rival =
          some cert.claim ∧
        acceptOwnedReplay history
            { endpointAccount history with requested := ∅ } =
          .accept { endpointAccount history with requested := ∅ } ∧
        ({ endpointAccount history with requested := ∅ }).requested = ∅ ∧
        acceptOwnedReplay history
            { endpointAccount history with requested := {Right.force} } =
          .reject .missingRights
            { endpointAccount history with requested := {Right.force} } ∧
        ({ endpointAccount history with requested := {Right.force} }).ledger =
          jointProductionLedger ∧
        ({ endpointAccount history with requested := {Right.force} }).requested =
          {Right.force} := by
  obtain ⟨_record, leaf, history, cert, _kept, _member, runEq, _follow, replayWalk,
      issued, certLedger, _denoted, certTrace, replayCut, _acceptedEndpoint, cutEq,
      ledgerEq⟩ := owned_return_replays_the_retained_request
  have issuer := earned_history_is_the_passive_issuer issued
  have productionFour := joint_prefix_replays_are_the_source_ledgers.2.2.2.2.2.1
  have denotedFour : denote cert.ledger = 4 := by
    rw [certLedger]
    exact productionFour
  have claimProductions : cert.claim.productions = cert.ledger := by
    unfold issueEarned at issued
    split at issued
    · simp at issued
    · cases issued
      rfl
  obtain ⟨_leafR, _runR, _leftR, _payR, _traceR, _pathR, _haltR, _controlR, _leftLookup,
      _rightLookup, _historyR, _indicesR, _productionR, validLedger, _denotedR, _recordedR⟩ :=
    joint_returned_source_account
  have validClaim : Valid cert.claim.productions := by
    rw [claimProductions, certLedger]
    exact validLedger
  have merged : Scoped.merge? cert.claim cert.claim = some cert.claim :=
    Scoped.merge_self cert.claim validClaim
  have factors := (issued_passive_factors_are_the_earned_ledger history issued).1
  have historyTrace : (retained leaf.1).trace = earnedTrace history :=
    certTrace.symm.trans issuer.1
  have historyLedger : earnedLedger history =
      (readGraph (retained leaf.1).state.world.receipts.nodes).factors := by
    rw [← issuer.2.2.2.2.2.1]
    exact factors.symm
  have cutIssued : issueCut jointRun = some cert := by
    have cutLeaf : issueCut jointRun = issueLeaf leaf := by
      simp [issueCut, runEq]
    cases hleaf : issueLeaf leaf with
    | none =>
        have mapped : (issueCut jointRun).map SourceCertificate.ledger =
            some jointProductionLedger := by
          obtain ⟨_b0, _b3, _b6, _b11, b15, _p0, _p3, _led6, _pay6, _led11, led15,
              _pay15, _ctrl, _split⟩ := source_budgets_issue_the_reached_slices
          simpa [b15] using led15
        simp [cutLeaf, hleaf] at mapped
    | some cert' =>
        have issued' :=
          issueEarned_matches_issueLeaf history rfl historyTrace historyLedger hleaf
        have cert'Eq : cert' = cert := by
          exact Option.some.inj (issued'.symm.trans issued)
        simp [cutLeaf, hleaf, cert'Eq]
  have leftOwner : cert.claim.claims jointLeftFactor.identity = some 0 := by
    have mapped := source_issue_reads_the_three_cuts.2.2.2.2.2.2.2.2.2.1
    rw [cutIssued] at mapped
    exact Option.some.inj mapped
  have rightsInspect : cert.rights = {Right.inspect} := by
    have mapped := source_issue_reads_the_three_cuts.2.2.2.2.2.1
    rw [cutIssued] at mapped
    exact Option.some.inj mapped
  have clash : Scoped.merge? cert.claim (jointOwnerClaim 1) = none :=
    Scoped.conflicting_claims_refused cert.claim (jointOwnerClaim 1)
      (joint_owner_claim_is_supported 1) leftOwner
      (by decide : (jointOwnerClaim 1).claims jointLeftFactor.identity = some 1)
      (by decide : (0 : Nat) ≠ 1)
  have notAccount : ¬ (endpointAccount history).ledger ≠ cert.ledger :=
    fun h => h ledgerEq
  have notTrace : ¬ (retained leaf.1).trace ≠ cert.trace := fun h => h certTrace.symm
  have notPay : ¬ denote cert.ledger ≠ cert.payment := fun h => h issuer.2.2.1.symm
  have cutLeafEq : (endpointAccount history).cut = [leaf] := cutEq.trans runEq
  have rivalEndpoint : (endpointAccount history).rival = none := by
    unfold endpointAccount
    rfl
  have controlLeaf : (retained leaf.1).state.control =
      .halted (.value jointValue) := by
    have leafSame : leaf = _leafR := by
      obtain ⟨eqLeaf, _nil⟩ := List.cons.inj (runEq.symm.trans _runR)
      exact eqLeaf
    rw [leafSame]
    exact _controlR
  have requestedEndpoint : (endpointAccount history).requested = {Right.inspect} := by
    simp [endpointAccount, requiredRights, controlLeaf]
  have heldEndpoint : (endpointAccount history).held = {Right.inspect} := by
    simp [endpointAccount, requiredRights, controlLeaf]
  have admittedEndpoint := earned_endpoint_is_admitted issued
  have endpointViews : admitViews cert (endpointAccount history) =
      .accept (endpointAccount history) ∧
      residualAgrees cert (endpointAccount history) = true := by
    have pack := admittedEndpoint
    unfold admitIssued at pack
    rw [rivalEndpoint] at pack
    change admitComparable cert (endpointAccount history) =
      .accept (endpointAccount history) at pack
    unfold admitComparable at pack
    split at pack
    · cases pack
    · rename_i account viewsEq
      split at pack
      · rename_i residualEq
        have accountEq : account = endpointAccount history := by
          injection pack
        cases accountEq
        exact ⟨viewsEq, residualEq⟩
      · cases pack
  have endpointView := endpointViews.1
  have endpointResidual := endpointViews.2
  let conflicted : PresentedAccount :=
    { endpointAccount history with rival := some (jointOwnerClaim 1) }
  have conflictedRefused : acceptOwnedReplay history conflicted =
      .reject .incoherentResidual conflicted := by
    have cutC : conflicted.cut = [leaf] := by simp [conflicted, cutLeafEq]
    unfold acceptOwnedReplay
    rw [issued, cutC]
    dsimp
    rw [replayWalk]
    simp only [conflicted, decide_eq_false notAccount, decide_eq_false notTrace,
      decide_eq_false notPay, Bool.or_false, not_true_eq_false, decide_false]
    rw [if_neg Bool.false_ne_true]
    rw [replayCut]
    have overlay :
        { endpointAccount history with
            held := conflicted.held,
            requested := conflicted.requested,
            rival := conflicted.rival } = conflicted := by
      rfl
    rw [overlay]
    unfold admitIssued
    rw [show conflicted.rival = some (jointOwnerClaim 1) by rfl]
    dsimp
    rw [clash]
  let compatible : PresentedAccount :=
    { endpointAccount history with rival := some cert.claim }
  have compatibleAdmitted : admitIssued cert compatible = .accept compatible := by
    have views :=
      admitViews_checked cert (endpointAccount history) compatible rfl rfl rfl rfl rfl
        endpointView
    have residual : residualAgrees cert compatible = true := by
      change residualAgrees cert (endpointAccount history) = true
      exact endpointResidual
    unfold admitIssued
    rw [show compatible.rival = some cert.claim by rfl]
    dsimp
    rw [merged]
    dsimp
    unfold admitComparable
    rw [views, residual]
    rfl
  have compatibleAccepted : acceptOwnedReplay history compatible =
      .accept compatible := by
    have cutC : compatible.cut = [leaf] := by simp [compatible, cutLeafEq]
    unfold acceptOwnedReplay
    rw [issued, cutC]
    dsimp
    rw [replayWalk]
    simp only [compatible, decide_eq_false notAccount, decide_eq_false notTrace,
      decide_eq_false notPay, Bool.or_false, not_true_eq_false, decide_false]
    rw [if_neg Bool.false_ne_true]
    rw [replayCut]
    have overlay :
        { endpointAccount history with
            held := compatible.held,
            requested := compatible.requested,
            rival := compatible.rival } = compatible := by
      rfl
    rw [overlay, compatibleAdmitted]
  let narrowed : PresentedAccount :=
    { endpointAccount history with requested := ∅ }
  have narrowedRights :
      (!decide (cert.rights ⊆ narrowed.held) ||
          (restrict? narrowed.held narrowed.requested).isNone) =
        (!decide (cert.rights ⊆ (endpointAccount history).held) ||
          (restrict? (endpointAccount history).held
            (endpointAccount history).requested).isNone) := by
    simp [narrowed, rightsInspect, heldEndpoint, requestedEndpoint, restrict?]
  have narrowedAdmitted : admitIssued cert narrowed = .accept narrowed := by
    have views :=
      admitViews_checked cert (endpointAccount history) narrowed rfl rfl rfl rfl
        narrowedRights endpointView
    have residual : residualAgrees cert narrowed = true := by
      change residualAgrees cert (endpointAccount history) = true
      exact endpointResidual
    unfold admitIssued
    rw [show narrowed.rival = none by simp [narrowed, rivalEndpoint]]
    dsimp
    unfold admitComparable
    rw [views, residual]
    rfl
  have narrowedAccepted : acceptOwnedReplay history narrowed =
      .accept narrowed := by
    have cutC : narrowed.cut = [leaf] := by simp [narrowed, cutLeafEq]
    unfold acceptOwnedReplay
    rw [issued, cutC]
    dsimp
    rw [replayWalk]
    simp only [narrowed, decide_eq_false notAccount, decide_eq_false notTrace,
      decide_eq_false notPay, Bool.or_false, not_true_eq_false, decide_false]
    rw [if_neg Bool.false_ne_true]
    rw [replayCut]
    have overlay :
        { endpointAccount history with
            held := narrowed.held,
            requested := narrowed.requested,
            rival := narrowed.rival } = narrowed := by
      rfl
    rw [overlay, narrowedAdmitted]
  let escalated : PresentedAccount :=
    { endpointAccount history with requested := {Right.force} }
  have escalatedMissing :
      (!decide (cert.rights ⊆ escalated.held) ||
          (restrict? escalated.held escalated.requested).isNone) = true := by
    have notForce : ¬ ({Right.force} : Rights) ⊆ {Right.inspect} := by decide
    simp [escalated, rightsInspect, heldEndpoint, restrict?, notForce]
  have escalatedRefused : acceptOwnedReplay history escalated =
      .reject .missingRights escalated := by
    have views :=
      admitViews_missing_rights cert (endpointAccount history) escalated rfl rfl rfl rfl
        endpointView escalatedMissing
    have cutC : escalated.cut = [leaf] := by simp [escalated, cutLeafEq]
    unfold acceptOwnedReplay
    rw [issued, cutC]
    dsimp
    rw [replayWalk]
    simp only [escalated, decide_eq_false notAccount, decide_eq_false notTrace,
      decide_eq_false notPay, Bool.or_false, not_true_eq_false, decide_false]
    rw [if_neg Bool.false_ne_true]
    rw [replayCut]
    have overlay :
        { endpointAccount history with
            held := escalated.held,
            requested := escalated.requested,
            rival := escalated.rival } = escalated := by
      rfl
    rw [overlay]
    unfold admitIssued
    rw [show escalated.rival = none by simp [escalated, rivalEndpoint]]
    dsimp
    unfold admitComparable
    rw [views]
  refine ⟨leaf, history, cert, issued, certLedger, denotedFour, validClaim, merged,
    clash, conflictedRefused, ?_, ?_, compatibleAccepted, ?_, narrowedAccepted, ?_,
    escalatedRefused, ?_, ?_⟩
  · simp [ledgerEq, certLedger]
  · rfl
  · rfl
  · rfl
  · simp [ledgerEq, certLedger]
  · rfl

/-! ## Reused qualified controls

`section Histories` does not create a namespace. The four facts above are
`NeedWeightedResumption.ProductionResumptionControls.suspension_retains_paid_production`,
`completed_shared_production`, `resumed_shared_production`, and
`resetting_incoming_coefficient_refused`. -/

end Mettapedia.Machines.Cursor.ProducerAccountTransport
