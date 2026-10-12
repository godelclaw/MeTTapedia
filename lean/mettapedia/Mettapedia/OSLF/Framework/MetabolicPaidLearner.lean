import Mettapedia.OSLF.Framework.MetabolicPaidTrace
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicInitialConfiguration

/-!
# Structural funding for actual learner events

The coupled event relation requires both an original paid event and an actual
prefix debit from the same acquired stack. The finite controller remaining
after a debit is already present in the initial process. Coupled paths project
to the original learner path and to an occurrence execution of the structural
rho protocol, retaining the remaining stack at every event boundary.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.MetabolicPaidLearner

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourceClaimHistory
open Mettapedia.OSLF.Framework.MetabolicPaidTrace
open Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators
open Mettapedia.CognitiveArchitecture.Consciousness.PaidWorkspaceExperiments
open Mettapedia.GSLT.Causality Mettapedia.GSLT.Causality.ProbeCampaign
open Mettapedia.OSLF.Framework.FiniteAssayLearner
open CanonicalBag LanguageDefGSLT

universe u
variable {Head : Type u}

/-- A charge selects an ordered prefix of the actual stack. -/
structure StackSplit (stack : Stack Head) (charge : Nat) where
  consumed : Stack Head
  suffix : Stack Head
  original : stack = consumed.append suffix
  counted : consumed.size = charge

def splitAffordable (stack : Stack Head) (charge : Nat) (available : charge ≤ stack.size) :
    StackSplit stack charge := by
  induction charge generalizing stack with
  | zero => exact ⟨.empty, stack, rfl, rfl⟩
  | succ charge inductionHypothesis =>
      cases stack with
      | empty => simp only [Stack.size] at available; omega
      | cell head tail =>
          have enough : charge ≤ tail.size := by
            simp only [Stack.size] at available
            omega
          let split := inductionHypothesis tail enough
          refine ⟨.cell head split.consumed, split.suffix, ?_, ?_⟩
          · change Stack.cell head tail = Stack.cell head (split.consumed.append split.suffix)
            exact congrArg (Stack.cell head) split.original
          · change split.consumed.size + 1 = charge + 1
            exact congrArg (fun amount => amount + 1) split.counted

namespace StackSplit

theorem balance {stack : Stack Head} {charge : Nat} (split : StackSplit stack charge) :
    stack.size = split.suffix.size + charge := by
  have readout := congrArg Stack.size split.original
  rw [Stack.append_size, split.counted, Nat.add_comm] at readout
  exact readout

theorem head_readout {stack : Stack Head} {charge : Nat} (split : StackSplit stack charge) :
    stack.heads = split.consumed.heads ++ split.suffix.heads := by
  exact (congrArg Stack.heads split.original).trans (Stack.append_heads _ _)

end StackSplit

/-- A debit block uses the installed controller and leaves its exact future
continuation in the resulting inventory. -/
structure DebitBlock (encoding : Encoding Head) (consumed suffix : Stack Head)
    (future : Nat) (record : List Head) (source : Configuration) where
  admitted : inventory source =
    fromProcess (live encoding (consumed.append suffix) (consumed.size + future) record)
  target : Configuration
  execution : Execution source target
  length : execution.length = 2 * consumed.size
  remaining : inventory target =
    fromProcess (live encoding suffix future (consumed.heads.reverse ++ record))

def debitBlock (encoding : Encoding Head) (consumed suffix : Stack Head)
    (future : Nat) (record : List Head) (source : Configuration)
    (sourceInventory : inventory source =
      fromProcess (live encoding (consumed.append suffix) (consumed.size + future) record)) :
    DebitBlock encoding consumed suffix future record source := by
  induction consumed generalizing source record with
  | empty =>
      refine ⟨sourceInventory, source, .done source, rfl, ?_⟩
      simpa only [Stack.append, Stack.size, Nat.zero_add, Stack.heads, List.reverse_nil,
        List.nil_append] using sourceInventory
  | cell head rest inductionHypothesis =>
      have installed : inventory source =
          fromProcess (live encoding (.cell head (rest.append suffix)) (rest.size + future + 1) record) := by
        simpa only [Stack.append, Stack.size, Nat.add_right_comm] using sourceInventory
      let first := cycle encoding head (rest.append suffix) (rest.size + future) record source installed
      let later := inductionHypothesis (head :: record) first.pop.target first.remaining
      refine ⟨sourceInventory, later.target, first.execution.append later.execution, ?_, ?_⟩
      · rw [Execution.append_length, first.execution_length, later.length]
        simp only [Stack.size]
        omega
      · simpa only [Stack.heads, List.reverse_cons, List.append_assoc,
          List.singleton_append] using later.remaining

/-- A coupled event is admitted only with an actual paid firing and an
actual structural debit of exactly that event's charge. -/
structure CoupledEvent (encoding : Encoding Head) {question : Question}
    {before after : Marking} (event : Event question before after)
    (stack : Stack Head) (future : Nat) (record : List Head) (source : Configuration) where
  split : StackSplit stack event.charge
  balance : stack.size = purse before
  debit : DebitBlock encoding split.consumed split.suffix future record source

namespace CoupledEvent

theorem affordable {encoding : Encoding Head} {question : Question} {before after : Marking}
    {event : Event question before after} {stack : Stack Head} {future : Nat}
    {record : List Head} {source : Configuration}
    (coupling : CoupledEvent encoding event stack future record source) :
    event.charge ≤ stack.size := by
  rw [coupling.balance]
  exact event.affordable

theorem remaining_balance {encoding : Encoding Head} {question : Question} {before after : Marking}
    {event : Event question before after} {stack : Stack Head} {future : Nat}
    {record : List Head} {source : Configuration}
    (coupling : CoupledEvent encoding event stack future record source) :
    coupling.split.suffix.size = purse after := by
  have paid := event.balance
  have physical := coupling.split.balance
  have agreement := coupling.balance
  omega

theorem exact_charge {encoding : Encoding Head} {question : Question} {before after : Marking}
    {event : Event question before after} {stack : Stack Head} {future : Nat}
    {record : List Head} {source : Configuration}
    (coupling : CoupledEvent encoding event stack future record source) :
    coupling.debit.execution.length = 2 * event.charge := by
  rw [coupling.debit.length, coupling.split.counted]

end CoupledEvent

/-- This paired semantics stores event-by-event synchronization. The path
index counts the installed debit continuation, rather than granting fuel. -/
inductive CoupledPath (encoding : Encoding Head) (question : Question) :
    Marking → Marking → Stack Head → List Head → Configuration → Nat → Type (max u 0) where
  | nil (marking : Marking) (stack : Stack Head) (record : List Head) (source : Configuration)
      (balance : stack.size = purse marking)
      (admitted : inventory source = fromProcess (live encoding stack 0 record)) :
      CoupledPath encoding question marking marking stack record source 0
  | cons {before middle after : Marking} {stack : Stack Head} {record : List Head}
      {source : Configuration} {future : Nat} (event : Event question before middle)
      (coupling : CoupledEvent encoding event stack future record source)
      (rest : CoupledPath encoding question middle after coupling.split.suffix
        (coupling.split.consumed.heads.reverse ++ record) coupling.debit.target future) :
      CoupledPath encoding question before after stack record source (event.charge + future)

namespace CoupledPath

variable {encoding : Encoding Head} {question : Question}

def paid : {before after : Marking} → {stack : Stack Head} → {record : List Head} →
    {source : Configuration} → {fuel : Nat} →
    CoupledPath encoding question before after stack record source fuel → Path question before after
  | _, _, _, _, _, _, .nil marking _ _ _ _ _ => .nil marking
  | _, _, _, _, _, _, .cons event _ rest => .cons event (paid rest)

def finalStack : {before after : Marking} → {stack : Stack Head} → {record : List Head} →
    {source : Configuration} → {fuel : Nat} →
    CoupledPath encoding question before after stack record source fuel → Stack Head
  | _, _, _, _, _, _, .nil _ stack _ _ _ _ => stack
  | _, _, _, _, _, _, .cons _ _ rest => finalStack rest

def finalRecord : {before after : Marking} → {stack : Stack Head} → {record : List Head} →
    {source : Configuration} → {fuel : Nat} →
    CoupledPath encoding question before after stack record source fuel → List Head
  | _, _, _, _, _, _, .nil _ _ record _ _ _ => record
  | _, _, _, _, _, _, .cons _ _ rest => finalRecord rest

def target : {before after : Marking} → {stack : Stack Head} → {record : List Head} →
    {source : Configuration} → {fuel : Nat} →
    CoupledPath encoding question before after stack record source fuel → Configuration
  | _, _, _, _, _, _, .nil _ _ _ source _ _ => source
  | _, _, _, _, _, _, .cons _ _ rest => target rest

def execution : {before after : Marking} → {stack : Stack Head} → {record : List Head} →
    {source : Configuration} → {fuel : Nat} →
    (path : CoupledPath encoding question before after stack record source fuel) →
      Execution source path.target
  | _, _, _, _, _, _, .nil _ _ _ source _ _ => .done source
  | _, _, _, _, _, _, .cons _ coupling rest => coupling.debit.execution.append (execution rest)

def consumedHeads : {before after : Marking} → {stack : Stack Head} → {record : List Head} →
    {source : Configuration} → {fuel : Nat} →
    CoupledPath encoding question before after stack record source fuel → List Head
  | _, _, _, _, _, _, .nil _ _ _ _ _ _ => []
  | _, _, _, _, _, _, .cons _ coupling rest => coupling.split.consumed.heads ++ consumedHeads rest

theorem initial_balance {before after : Marking} {stack : Stack Head} {record : List Head}
    {source : Configuration} {fuel : Nat}
    (path : CoupledPath encoding question before after stack record source fuel) :
    stack.size = purse before := by
  cases path with
  | nil _ _ _ _ balance _ => exact balance
  | cons _ coupling _ => exact coupling.balance

theorem initial_inventory {before after : Marking} {stack : Stack Head} {record : List Head}
    {source : Configuration} {fuel : Nat}
    (path : CoupledPath encoding question before after stack record source fuel) :
    inventory source = fromProcess (live encoding stack fuel record) := by
  cases path with
  | nil _ _ _ _ _ admitted => exact admitted
  | cons event coupling _ =>
      have exactSource := coupling.debit.admitted
      simpa only [coupling.split.counted, ← coupling.split.original] using exactSource

theorem paid_spent {before after : Marking} {stack : Stack Head} {record : List Head}
    {source : Configuration} {fuel : Nat}
    (path : CoupledPath encoding question before after stack record source fuel) :
    path.paid.spent = fuel := by
  induction path with
  | nil => rfl
  | cons event coupling rest inductionHypothesis =>
      change event.charge + rest.paid.spent = _
      rw [inductionHypothesis]

theorem execution_length {before after : Marking} {stack : Stack Head} {record : List Head}
    {source : Configuration} {fuel : Nat}
    (path : CoupledPath encoding question before after stack record source fuel) :
    path.execution.length = 2 * fuel := by
  induction path with
  | nil => rfl
  | cons event coupling rest inductionHypothesis =>
      change (coupling.debit.execution.append rest.execution).length = _
      rw [Execution.append_length, coupling.exact_charge, inductionHypothesis, Nat.mul_add]

theorem remaining_balance {before after : Marking} {stack : Stack Head} {record : List Head}
    {source : Configuration} {fuel : Nat}
    (path : CoupledPath encoding question before after stack record source fuel) :
    path.finalStack.size = purse after := by
  induction path with
  | nil _ _ _ _ balance _ => exact balance
  | cons _ _ _ inductionHypothesis => exact inductionHypothesis

theorem remaining_inventory {before after : Marking} {stack : Stack Head} {record : List Head}
    {source : Configuration} {fuel : Nat}
    (path : CoupledPath encoding question before after stack record source fuel) :
    inventory path.target = fromProcess (live encoding path.finalStack 0 path.finalRecord) := by
  induction path with
  | nil _ _ _ _ _ admitted => exact admitted
  | cons _ _ _ inductionHypothesis => exact inductionHypothesis

theorem ledger {before after : Marking} {stack : Stack Head} {record : List Head}
    {source : Configuration} {fuel : Nat}
    (path : CoupledPath encoding question before after stack record source fuel) :
    stack.size = path.finalStack.size + fuel := by
  induction path with
  | nil => exact (Nat.add_zero _).symm
  | cons event coupling rest inductionHypothesis =>
      have physical := coupling.split.balance
      simp only [finalStack]
      omega

theorem ordered_heads {before after : Marking} {stack : Stack Head} {record : List Head}
    {source : Configuration} {fuel : Nat}
    (path : CoupledPath encoding question before after stack record source fuel) :
    stack.heads = path.consumedHeads ++ path.finalStack.heads := by
  induction path with
  | nil => exact (List.nil_append _).symm
  | cons event coupling rest inductionHypothesis =>
      have selected := coupling.split.head_readout
      simp only [consumedHeads, finalStack]
      rw [List.append_assoc, ← inductionHypothesis]
      exact selected

theorem spent_record {before after : Marking} {stack : Stack Head} {record : List Head}
    {source : Configuration} {fuel : Nat}
    (path : CoupledPath encoding question before after stack record source fuel) :
    path.finalRecord = path.consumedHeads.reverse ++ record := by
  induction path with
  | nil => rfl
  | cons event coupling rest inductionHypothesis =>
      change rest.finalRecord = (coupling.split.consumed.heads ++ rest.consumedHeads).reverse ++ _
      rw [List.reverse_append, List.append_assoc]
      exact inductionHypothesis

theorem consumed_count {before after : Marking} {stack : Stack Head} {record : List Head}
    {source : Configuration} {fuel : Nat}
    (path : CoupledPath encoding question before after stack record source fuel) :
    path.consumedHeads.length = fuel := by
  induction path with
  | nil => rfl
  | cons event coupling rest inductionHypothesis =>
      change (coupling.split.consumed.heads ++ rest.consumedHeads).length = _
      rw [List.length_append, ← Stack.size_eq_length, coupling.split.counted, inductionHypothesis]

end CoupledPath

def couple (encoding : Encoding Head) {question : Question} {before after : Marking}
    (path : Path question before after) (stack : Stack Head) (record : List Head)
    (source : Configuration) (balance : stack.size = purse before)
    (sourceInventory : inventory source = fromProcess (live encoding stack path.spent record)) :
    CoupledPath encoding question before after stack record source path.spent := by
  induction path generalizing stack record source with
  | nil marking => exact .nil marking stack record source balance sourceInventory
  | @cons first middle last event rest inductionHypothesis =>
      have available : event.charge ≤ stack.size := by
        rw [balance]
        exact event.affordable
      let split := splitAffordable stack event.charge available
      have installed : inventory source = fromProcess
          (live encoding (split.consumed.append split.suffix) (split.consumed.size + rest.spent) record) := by
        rw [split.counted, ← split.original]
        exact sourceInventory
      let debit := debitBlock encoding split.consumed split.suffix rest.spent record source installed
      let eventCoupling : CoupledEvent encoding event stack rest.spent record source :=
        ⟨split, balance, debit⟩
      let remaining := inductionHypothesis split.suffix (split.consumed.heads.reverse ++ record)
        debit.target eventCoupling.remaining_balance debit.remaining
      exact .cons event eventCoupling remaining

theorem couple_paid (encoding : Encoding Head) {question : Question} {before after : Marking}
    (path : Path question before after) (stack : Stack Head) (record : List Head)
    (source : Configuration) (balance : stack.size = purse before)
    (sourceInventory : inventory source = fromProcess (live encoding stack path.spent record)) :
    (couple encoding path stack record source balance sourceInventory).paid = path := by
  induction path generalizing stack record source with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      change Path.cons event _ = Path.cons event rest
      apply congrArg (Path.cons event)
      exact inductionHypothesis _ _ _ _ _

/-- The complete receipt retains the original experiment, actual resource
acquisition and its event-by-event physical funding. -/
structure AcquiredExperiment (encoding : Encoding Head) (state : State) (question : Question)
    (stack : Stack Head) (session provider client : Nat) (record : List Head)
    (source : Configuration) where
  experiment : Experiment state question stack.size session provider client
  initial : inventory source = fromProcess
    (acquisitionSource encoding stack (experimentPath experiment).spent record)
  acquisition : Acquisition encoding stack (experimentPath experiment).spent record source
  coupling : CoupledPath encoding question (.probe state stack.size)
    (.assay experiment.assay.endpoint) stack record acquisition.claim.target (experimentPath experiment).spent
  paidComparison : coupling.paid = experimentPath experiment

def acquireExperiment (encoding : Encoding Head) {state : State} {question : Question}
    {stack : Stack Head} {session provider client : Nat} (record : List Head)
    (experiment : Experiment state question stack.size session provider client)
    (source : Configuration)
    (sourceInventory : inventory source = fromProcess
      (acquisitionSource encoding stack (experimentPath experiment).spent record)) :
    AcquiredExperiment encoding state question stack session provider client record source := by
  let transferred := acquire encoding stack (experimentPath experiment).spent record source sourceInventory
  let synchronized := couple encoding (experimentPath experiment) stack record transferred.claim.target
    rfl transferred.transferred
  exact ⟨experiment, sourceInventory, transferred, synchronized,
    couple_paid encoding (experimentPath experiment) stack record transferred.claim.target rfl
      transferred.transferred⟩

def sourceFor (encoding : Encoding Head) (state : State) (question : Question)
    (stack : Stack Head) (session provider client : Nat) (record : List Head)
    (origin : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Origin) (firstKey : Nat) : Configuration :=
  let experiment := execute state question stack.size session provider client
  annotate (acquisitionSource encoding stack (experimentPath experiment).spent record) origin firstKey

/-- The initial stack is actual offered syntax with separately supplied
occurrence origins. No scalar balance is granted by this constructor. -/
def executeMetabolic (encoding : Encoding Head) (state : State) (question : Question)
    (stack : Stack Head) (session provider client : Nat) (record : List Head)
    (origin : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Origin) (firstKey : Nat) :
    AcquiredExperiment encoding state question stack session provider client record
      (sourceFor encoding state question stack session provider client record origin firstKey) :=
  acquireExperiment encoding record (execute state question stack.size session provider client)
    (sourceFor encoding state question stack session provider client record origin firstKey)
    (annotate_inventory _ _ _)

namespace AcquiredExperiment

variable {encoding : Encoding Head} {state : State} {question : Question} {stack : Stack Head}
variable {session provider client : Nat} {record : List Head} {source : Configuration}

def execution (receipt : AcquiredExperiment encoding state question stack session provider client record source) :
    Execution source receipt.coupling.target :=
  receipt.acquisition.execution.append receipt.coupling.execution

def answers (receipt : AcquiredExperiment encoding state question stack session provider client record source) :
    Multiset (Response Bool Nat) := receipt.experiment.responses

def revision (receipt : AcquiredExperiment encoding state question stack session provider client record source)
    (hypotheses : Finset Mode) : Finset Mode :=
  revise prediction hypotheses question receipt.answers

theorem execution_length
    (receipt : AcquiredExperiment encoding state question stack session provider client record source) :
    receipt.execution.length = 1 + 2 * receipt.experiment.spent := by
  rw [execution, Execution.append_length, receipt.acquisition.execution_length,
    receipt.coupling.execution_length, experimentPath_spent]

theorem actual_public_execution
    (receipt : AcquiredExperiment encoding state question stack session provider client record source) :
    Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout source) (readout receipt.coupling.target) :=
  receipt.execution.public_history

theorem current_resource
    (receipt : AcquiredExperiment encoding state question stack session provider client record source) :
    inventory receipt.coupling.target =
        fromProcess (live encoding receipt.coupling.finalStack 0 receipt.coupling.finalRecord) ∧
      receipt.coupling.finalStack.size = receipt.experiment.remaining :=
  ⟨receipt.coupling.remaining_inventory, receipt.coupling.remaining_balance⟩

theorem resource_ledger
    (receipt : AcquiredExperiment encoding state question stack session provider client record source) :
    stack.size = receipt.coupling.finalStack.size + receipt.experiment.spent := by
  have physical := receipt.coupling.ledger
  exact physical.trans (congrArg (fun amount => receipt.coupling.finalStack.size + amount)
    (experimentPath_spent receipt.experiment))

theorem charge_occurrences
    (receipt : AcquiredExperiment encoding state question stack session provider client record source) :
    receipt.coupling.paid.assayEntries =
      (assaySystem question).pathEntries receipt.experiment.assay.path := by
  rw [receipt.paidComparison]
  exact experimentPath_entries receipt.experiment

theorem completed_intervention
    (receipt : AcquiredExperiment encoding state question stack session provider client record source) :
    receipt.coupling.paid.commands = question.commands.take stack.size := by
  rw [receipt.paidComparison]
  exact experimentPath_commands receipt.experiment

theorem no_repeated_claim
    (receipt : AcquiredExperiment encoding state question stack session provider client record source)
    (distinct : Distinct source) : receipt.execution.claimedKeys.Nodup :=
  receipt.execution.claimedKeys_nodup distinct

theorem underfunded_silent
    (receipt : AcquiredExperiment encoding state question stack session provider client record source)
    (insufficient : stack.size < question.commands.length + 2 + 3) : receipt.answers = 0 :=
  receipt.experiment.underfunded_silent insufficient

theorem silence_preserves_candidates
    (receipt : AcquiredExperiment encoding state question stack session provider client record source)
    (insufficient : stack.size < question.commands.length + 2 + 3) (hypotheses : Finset Mode) :
    receipt.revision hypotheses = hypotheses := by
  rw [revision, receipt.underfunded_silent insufficient]
  exact silence_preserves prediction hypotheses question

/-- This applies to supplied prefixes, not only to a controller chosen to
finish every affordable instruction. -/
theorem correct_candidate_survives (mode : Mode)
    (receipt : AcquiredExperiment encoding
      (Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators.initial mode)
      question stack session provider client record source) :
    mode ∈ receipt.revision candidates := by
  apply (revise_mem prediction candidates question receipt.answers mode).2
  refine ⟨by cases mode <;> simp [candidates], ?_⟩
  intro response present
  have sound := receipt.experiment.response_sound response present
  rw [sound.2.1]
  change observation (Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators.initial mode)
    question = (session, ComplementaryAssay.verdictOf
      (observation (Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators.initial mode) question),
      client, observation (Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators.initial mode)
        question).2.1.bit
  exact (ComplementaryAssay.verdictOf_bit _).symm

end AcquiredExperiment

end Mettapedia.OSLF.Framework.MetabolicPaidLearner
