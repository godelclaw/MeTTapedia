import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionSelectionExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionCanonical

/-!
# Collection batches in MeTTa

The collection allocator supplies ordinary argument and rest-capture tasks to
the existing scoped engine. Allocation decisions and nested match histories
remain in the wire. The direct residual construction requires arranged input;
its comparison with the semantic batch is proved in ScopedCollectionCanonical.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionSelection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval BridgeKit WireKit
open RuleInstantiationExecution.GeneralExecution
open CollectionSelectionExecution (booleanTerm allocationTerm)
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_machine.metta"
    sha256 "34addb0bd7d4b78a6883cc7238a0c4741358085b9b22bdf490398a4cbd0e2b46"

def library : BridgeKit.Library :=
  ⟨CollectionSelectionExecution.library.runtime, source.program,
    ["gslt:collection-machine:", "gslt:collection-plan:"]⟩

set_option maxRecDepth 100000 in
theorem checked : library.check = true := by decide +kernel

def requestTerm (request : ScopedCollectionMachine.Request) : Term :=
  .application "CollectionRequest" [matcherRequestTerm request.machine, .natural request.index]

def jobTerm (job : ScopedCollectionMachine.Job) : Term :=
  .application "CollectionJob"
    [allocationTerm InferenceCettaWire.encodePattern job.allocation, matcherStateTerm job.state]

def stateTerm (state : ScopedCollectionMachine.State) : Term := encodeList jobTerm state

def receiptTerm (receipt : ScopedCollectionMachine.Receipt) : Term :=
  .application "CollectionReceipt"
    [allocationTerm InferenceCettaWire.encodePattern receipt.allocation, matcherAnswerTerm receipt.matching]

def firingTerm (firing : ScopedCollectionMachine.FiringReceipt) : Term :=
  .application "CollectionFiring" [receiptTerm firing.source,
    InferenceCettaWire.encodePattern firing.target]

syntax "collection_machine_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| collection_machine_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        requestTerm, jobTerm, stateTerm, receiptTerm, allocationTerm, booleanTerm,
        matcherStateTerm, matcherWorkTerm, matcherTaskTerm,
        InferenceCettaWire.encodePatterns_eq_encodeList,
        encodeList, encodeOption, $extra,*]))

@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (state : State) (left right : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right))) := by
  metta_lift checked ["left", "right"]
    (CollectionSelectionExecution.append_returns element state left right)

@[metta_head "gslt:automata:length"]
theorem length_returns {α : Type} (element : α → Term) (state : State) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:length" [encoded (encodeList element items)])
      state (number items.length) := by
  metta_lift checked ["items"]
    (by metta_lift CollectionSelectionExecution.checked ["items"]
      (CollectionSelectionExecution.scoped_length_returns element state items))

@[metta_head "gslt:collection:allocate"]
theorem allocate_returns {α : Type} (element : α → Term) (state : State)
    (idempotent : Bool) (count : Nat) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:collection:allocate"
        [encoded (booleanTerm idempotent), number count, encoded (encodeList element items)])
      state (encoded (encodeList (allocationTerm element) (tracedAllocations idempotent count items))) := by
  metta_lift checked ["idempotent", "count", "items"]
    (CollectionSelectionExecution.allocate_returns element state idempotent count items)

theorem machine_agreement :
    ProgramAgreementOn MachineTransport.executionHeads GeneralScopedMatchExecution.program
      CollectionSelectionExecution.scopedLibrary.runtime :=
  agreement_trans Mechanical.matcher_completed_agreement
    (programAgreementOn_of_retained_rows _ _ _ rfl rfl)

@[metta_head "gslt:rule:scope-matcher-run"]
theorem run_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (fuel : Nat) (machine : GeneralScopedMatchMachine.State) :
    PureReturns library.runtime [] state
      (apply "gslt:rule:scope-matcher-run"
        [encoded (matcherRequestTerm request), number fuel, encoded (matcherStateTerm machine)])
      state (encoded (matcherStateTerm (GeneralScopedMatchMachine.run request fuel machine))) := by
  metta_lift checked ["request", "fuel", "state"]
    (by metta_lift CollectionSelectionExecution.checked ["request", "fuel", "state"]
      (transport_call MachineTransport.program_closed machine_agreement
        (by decide +kernel) (by decide) (by decide +kernel) (by decide)
        ["request", "fuel", "state"] (by decide) rfl (by decide +kernel)
        (matcher_run_returns state request fuel machine)))

@[metta_head "gslt:rule:scope-matcher-complete"]
theorem machine_complete_returns (state : State) (machine : GeneralScopedMatchMachine.State) :
    PureReturns library.runtime [] state
      (apply "gslt:rule:scope-matcher-complete" [encoded (matcherStateTerm machine)])
      state (Effects.boolean (GeneralScopedMatchMachine.complete machine)) := by
  metta_lift checked ["state"]
    (by metta_lift CollectionSelectionExecution.checked ["state"]
      (transport_call MachineTransport.program_closed machine_agreement
        (by decide +kernel) (by decide) (by decide +kernel) (by decide)
        ["state"] (by decide) rfl (by decide +kernel)
        (matcher_complete_returns state machine)))

@[metta_head "gslt:collection-machine:allocation-state"]
theorem allocation_state_returns (state : State) (request : ScopedCollectionMachine.Request)
    (allocation : Allocation Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:allocation-state"
        [encoded (requestTerm request), encoded (allocationTerm InferenceCettaWire.encodePattern allocation)])
      state (encoded (matcherStateTerm (ScopedCollectionMachine.rawAllocationState request allocation))) := by
  cases rest : request.rest with
  | none =>
      cases residual : allocation.residual with
      | nil =>
          collection_machine_eval unfolding [ScopedCollectionMachine.rawAllocationState, rest, residual,
            matcherRequestTerm, ScopedCollectionMachine.Request.machine, InferenceCettaWire.encodePattern,
            InferenceCettaWire.encodeRest, traceTerm]
      | cons first tail =>
          collection_machine_eval unfolding [ScopedCollectionMachine.rawAllocationState, rest, residual,
            matcherRequestTerm, ScopedCollectionMachine.Request.machine, InferenceCettaWire.encodePattern,
            InferenceCettaWire.encodeRest, traceTerm]
  | some name =>
      have count := length_returns InferenceCettaWire.encodePattern state request.schemas
      have path := append_returns Term.natural state request.path [request.index + request.schemas.length]
      collection_machine_eval [count, path] unfolding [ScopedCollectionMachine.rawAllocationState, rest,
        matcherRequestTerm, ScopedCollectionMachine.Request.machine, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodePatterns_eq_encodeList, InferenceCettaWire.encodeRest, traceTerm]

@[metta_head "gslt:collection-machine:jobs"]
theorem jobs_returns (state : State) (request : ScopedCollectionMachine.Request) :
    ∀ allocations : List (Allocation Pattern),
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:jobs"
        [encoded (requestTerm request), encoded (encodeList (allocationTerm InferenceCettaWire.encodePattern) allocations)])
      state (encoded (stateTerm (allocations.map fun allocation =>
        ⟨allocation, ScopedCollectionMachine.rawAllocationState request allocation⟩)))
  | [] => by collection_machine_eval
  | allocation :: tail => by
      have first := allocation_state_returns state request allocation
      have later := jobs_returns state request tail
      collection_machine_eval [first, later] unfolding [List.map_cons]

@[metta_head "gslt:collection-machine:start"]
theorem raw_start_returns (state : State) (request : ScopedCollectionMachine.Request) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:start" [encoded (requestTerm request)])
      state (encoded (stateTerm (ScopedCollectionMachine.rawStart request))) := by
  have count := length_returns InferenceCettaWire.encodePattern state request.schemas
  have allocated := allocate_returns InferenceCettaWire.encodePattern state
    (request.kind == .hashSet) request.schemas.length request.targets
  have jobs := jobs_returns state request request.allocations
  cases kind : request.kind <;>
    collection_machine_eval [count, allocated, jobs] unfolding [
      ScopedCollectionMachine.rawStart, ScopedCollectionMachine.Request.allocations,
      matcherRequestTerm, ScopedCollectionMachine.Request.machine, InferenceCettaWire.encodePattern,
      InferenceCettaWire.encodePatterns_eq_encodeList, InferenceCettaWire.encodeRest,
      InferenceCettaWire.encodeCollectionType, kind]

/-- The emitted start builds exactly the semantic job list when the carrier
has already been arranged according to its declared collection algebra. -/
theorem start_returns (state : State) (request : ScopedCollectionMachine.Request)
    (fixed : CanonicalBags.arrange request.kind request.targets = request.targets) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:start" [encoded (requestTerm request)])
      state (encoded (stateTerm (ScopedCollectionMachine.start request))) := by
  rw [← ScopedCollectionMachine.rawStart_eq request fixed]
  exact raw_start_returns state request

@[metta_head "gslt:collection-machine:resume"]
theorem resume_returns (state : State) (request : ScopedCollectionMachine.Request) (fuel : Nat) :
    ∀ jobs : ScopedCollectionMachine.State,
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:resume"
        [encoded (requestTerm request), number fuel, encoded (stateTerm jobs)])
      state (encoded (stateTerm (ScopedCollectionMachine.resume request fuel jobs)))
  | [] => by collection_machine_eval unfolding [ScopedCollectionMachine.resume]
  | job :: tail => by
      have first := run_returns state request.machine fuel job.state
      have later := resume_returns state request fuel tail
      cases job
      collection_machine_eval [first, later] unfolding [ScopedCollectionMachine.resume, List.map_cons]

@[metta_head "gslt:collection-machine:complete"]
theorem complete_returns (state : State) : ∀ jobs : ScopedCollectionMachine.State,
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:complete" [encoded (stateTerm jobs)])
      state (encoded (booleanTerm (ScopedCollectionMachine.complete jobs)))
  | [] => by collection_machine_eval unfolding [ScopedCollectionMachine.complete]
  | job :: tail => by
      have first := machine_complete_returns state job.state
      have later := complete_returns state tail
      cases done : GeneralScopedMatchMachine.complete job.state <;>
        rw [done] at first <;>
        collection_machine_eval [first, later] unfolding [ScopedCollectionMachine.complete, List.all_cons, done]

@[metta_head "gslt:collection-machine:receipts"]
theorem receipts_returns (state : State) (allocation : Allocation Pattern) :
    ∀ answers : List GeneralScopedMatchMachine.Answer,
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:receipts"
        [encoded (allocationTerm InferenceCettaWire.encodePattern allocation), encoded (encodeList matcherAnswerTerm answers)])
      state (encoded (encodeList receiptTerm (answers.map fun answer => ⟨allocation, answer⟩)))
  | [] => by collection_machine_eval
  | answer :: tail => by
      collection_machine_eval [receipts_returns state allocation tail] unfolding [List.map_cons]

@[metta_head "gslt:collection-machine:publication"]
theorem publication_returns (state : State) : ∀ jobs : ScopedCollectionMachine.State,
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:publication" [encoded (stateTerm jobs)])
      state (encoded (encodeList receiptTerm (ScopedCollectionMachine.publication jobs)))
  | [] => by collection_machine_eval unfolding [ScopedCollectionMachine.publication]
  | job :: tail => by
      have first := receipts_returns state job.allocation job.state.answers
      have later := publication_returns state tail
      have joined := append_returns receiptTerm state
        (job.state.answers.map fun answer => ⟨job.allocation, answer⟩)
        (ScopedCollectionMachine.publication tail)
      cases job
      collection_machine_eval [first, later, joined] unfolding [
        ScopedCollectionMachine.publication, List.flatMap_cons]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution
