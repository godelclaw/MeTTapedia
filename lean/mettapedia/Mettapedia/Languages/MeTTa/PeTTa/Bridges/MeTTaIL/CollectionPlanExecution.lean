import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionFiringExecution
import Mettapedia.OSLF.MeTTaIL.CollectionPlanMachine

/-! Native execution of every admitted root-collection request in plan order. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPlanExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionPlanMachine
open Effects (State)
open Eval BridgeKit WireKit
open ScopedCollectionExecution

def requestEntryTerm (entry : Nat × ScopedCollectionMachine.Request) : Term :=
  .application "CollectionPlanRequest" [.natural entry.1, requestTerm entry.2]

def jobTerm (job : Job) : Term :=
  .application "CollectionPlanJob" [.natural job.ordinal, requestTerm job.request, stateTerm job.state]

def planStateTerm (state : CollectionPlanMachine.State) : Term := encodeList jobTerm state

def planFiringTerm (firing : Firing) : Term :=
  .application "CollectionPlanFiring"
    [.natural firing.ordinal, requestTerm firing.request,
      ScopedCollectionExecution.firingTerm firing.receipt]

@[metta_head "gslt:collection-plan:start"]
theorem start_returns (state : Effects.State) :
    ∀ requests : List (Nat × ScopedCollectionMachine.Request),
    (∀ entry ∈ requests,
      CanonicalBags.arrange entry.2.kind entry.2.targets = entry.2.targets) →
    PureReturns library.runtime [] state
      (apply "gslt:collection-plan:start" [encoded (encodeList requestEntryTerm requests)])
      state (encoded (planStateTerm (CollectionPlanMachine.start requests)))
  | [], _ => by
      collection_machine_eval unfolding [planStateTerm, CollectionPlanMachine.start]
  | (ordinal, request) :: requests, fixed => by
      have first := ScopedCollectionExecution.start_returns state request
        (fixed (ordinal, request) (.head requests))
      have later := start_returns state requests fun item member =>
        fixed item (.tail (ordinal, request) member)
      collection_machine_eval [first, later] unfolding [planStateTerm, jobTerm,
        requestEntryTerm, CollectionPlanMachine.start, List.map_cons]

@[metta_head "gslt:collection-plan:resume"]
theorem resume_returns (state : Effects.State) (fuel : Nat) : ∀ jobs : CollectionPlanMachine.State,
    PureReturns library.runtime [] state
      (apply "gslt:collection-plan:resume" [number fuel, encoded (planStateTerm jobs)])
      state (encoded (planStateTerm (CollectionPlanMachine.resume fuel jobs)))
  | [] => by
      collection_machine_eval unfolding [planStateTerm, CollectionPlanMachine.resume]
  | job :: jobs => by
      have first := ScopedCollectionExecution.resume_returns state job.request fuel job.state
      have later := resume_returns state fuel jobs
      cases job
      collection_machine_eval [first, later] unfolding [planStateTerm, jobTerm,
        CollectionPlanMachine.resume, List.map_cons]

@[metta_head "gslt:collection-plan:complete"]
theorem complete_returns (state : Effects.State) : ∀ jobs : CollectionPlanMachine.State,
    PureReturns library.runtime [] state
      (apply "gslt:collection-plan:complete" [encoded (planStateTerm jobs)])
      state (encoded (CollectionSelectionExecution.booleanTerm
        (CollectionPlanMachine.complete jobs)))
  | [] => by
      collection_machine_eval unfolding [planStateTerm, CollectionPlanMachine.complete]
  | job :: jobs => by
      have first := ScopedCollectionExecution.complete_returns state job.state
      have later := complete_returns state jobs
      cases done : ScopedCollectionMachine.complete job.state with
      | false =>
          rw [done] at first
          rw [CollectionPlanMachine.complete, List.all_cons, done]
          simp only [Bool.false_and]
          collection_machine_eval [first] unfolding [planStateTerm, jobTerm]
      | true =>
          rw [done] at first
          rw [CollectionPlanMachine.complete, List.all_cons, done]
          simp only [Bool.true_and]
          collection_machine_eval [first, later] unfolding [planStateTerm, jobTerm]

@[metta_head "gslt:collection-plan:tag"]
theorem tag_returns (state : Effects.State) (ordinal : Nat)
    (request : ScopedCollectionMachine.Request) :
    ∀ firings : List ScopedCollectionMachine.FiringReceipt,
    PureReturns library.runtime [] state
      (apply "gslt:collection-plan:tag"
        [number ordinal, encoded (requestTerm request),
          encoded (encodeList ScopedCollectionExecution.firingTerm firings)])
      state (encoded (encodeList planFiringTerm
        (firings.map fun receipt => ⟨ordinal, request, receipt⟩)))
  | [] => by collection_machine_eval
  | firing :: firings => by
      have later := tag_returns state ordinal request firings
      collection_machine_eval [later] unfolding [planFiringTerm, List.map_cons]

@[metta_head "gslt:collection-plan:firings"]
theorem firings_returns (state : Effects.State) : ∀ jobs : CollectionPlanMachine.State,
    PureReturns library.runtime [] state
      (apply "gslt:collection-plan:firings" [encoded (planStateTerm jobs)])
      state (encoded (encodeList planFiringTerm (CollectionPlanMachine.publication jobs)))
  | [] => by
      collection_machine_eval unfolding [planStateTerm, CollectionPlanMachine.publication]
  | job :: jobs => by
      have receipts := ScopedCollectionExecution.publication_returns state job.state
      have first := ScopedCollectionFiringExecution.firings_returns state job.request
        (ScopedCollectionMachine.publication job.state)
      have tagged := tag_returns state job.ordinal job.request
        (ScopedCollectionMachine.firings job.request job.state)
      have later := firings_returns state jobs
      have joined := ScopedCollectionExecution.append_returns planFiringTerm state
        ((ScopedCollectionMachine.firings job.request job.state).map fun receipt =>
          (⟨job.ordinal, job.request, receipt⟩ : Firing))
        (CollectionPlanMachine.publication jobs)
      cases job
      collection_machine_eval [receipts, first, tagged, later, joined] unfolding [
        planStateTerm, jobTerm, planFiringTerm, CollectionPlanMachine.publication,
        List.flatMap_cons]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPlanExecution
