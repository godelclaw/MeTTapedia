import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine

/-!
# Native joint retained occurrence transitions

Each round advances source-job matcher lanes, appends only fresh allocation
frames, and advances the existing conditional batch. The comparison retains
the complete matcher state, continuation frames and chronological log. Source
job generation and selection of an emitted profile are separate interfaces.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceBatch CollectionOccurrenceMatcher CanonicalCompare
open Eval BridgeKit WireKit CollectionOccurrenceCollectorExecution
open CollectionOccurrenceRuntime
open scoped ProgramQuotation

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_occurrence_machine.metta"
    sha256 "bfbca7b35bfa678b4145030bf631bbe7bc4e6291cfb2e10561e152db0468f0df"

def library : Library :=
  ⟨CollectionOccurrenceCollectorExecution.library.runtime, source.program, ["gslt:occurrence-machine:"]⟩

theorem checked : library.check = true := by decide +kernel

def stateTerm (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern) : Term :=
  .application "RecursiveOccurrenceState"
    [encodeList CollectionOccurrenceMatcherExecution.laneTerm state.matchers,
      CollectionOccurrenceBatchExecution.stateTerm state.batch]

syntax "machine_from_publication% " "[" str,* "] " term:max : term
macro_rules
  | `(machine_from_publication% [$names,*] $fact) =>
    `(by
      have atRuntime := occurrence_from_publication% [$names,*] $fact
      have atCollector := by
        metta_lift CollectionOccurrenceCollectorExecution.checked [$names,*] atRuntime
      metta_lift checked [$names,*] atCollector)

syntax "occurrence_machine_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| occurrence_machine_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        stateTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

structure Ready (names footprint : List String)
    (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern) : Prop where
  matchers : ∀ lane ∈ state.matchers, LaneReady names footprint lane
  batch : CollectionOccurrenceBatchExecution.StateReady footprint state.batch

private theorem collected_job (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected sourcePattern) (work depth : Nat) :
    ∀ (answers : List RecursiveCollectionMachine.Answer)
      (published : ∀ answer ∈ answers, Published job work answer)
      {allocation : Allocation plan bound expected sourcePattern},
      allocation ∈ collect job licensed work depth answers published → allocation.job = job
  | [], _, _, member => by cases member
  | answer :: answers, published, allocation, member => by
    rcases List.mem_append.mp member with first | later
    · cases made : allocate? job licensed work answer
        (published answer List.mem_cons_self) depth with
      | none => simp only [made, Option.toList_none, List.not_mem_nil] at first
      | some selected =>
        have same : allocation = selected := by
          simpa only [made, Option.toList_some, List.mem_singleton] using first
        subst allocation
        exact (allocate_readout job licensed work depth answer
          (published answer List.mem_cons_self) made).1
    · exact collected_job job licensed work depth answers
        (fun next member => published next (List.mem_cons_of_mem _ member)) later

theorem lane_resume_ready (names footprint : List String)
    (lane : Lane plan bound expected sourcePattern) (work : Nat)
    (ready : LaneReady names footprint lane) : LaneReady names footprint (lane.resume work) := by
  exact ⟨RecursiveCollectionMachine.run_covered lane.job.request names work ready.state,
    ready.target, ready.free, ready.admitted, ready.sorted⟩

/-- Finite source-name coverage suffices for every newly created
continuation; no completed premise or publication account is assumed. -/
theorem fresh_frames_ready (names footprint : List String) (depth : Nat)
    (lanes : List (Lane plan bound expected sourcePattern))
    (ready : ∀ lane ∈ lanes, LaneReady names footprint lane)
    (allocation : Allocation plan bound expected sourcePattern)
    (member : allocation ∈ lanes.flatMap (Lane.allocations depth)) :
    CollectionOccurrenceBatchExecution.FrameReady footprint (Frame.initial allocation) := by
  obtain ⟨lane, inLanes, inLane⟩ := List.mem_flatMap.mp member
  have sameJob := collected_job lane.job lane.licensed (lane.spent + 1) depth lane.fresh
    (fun answer member => (lane.resume 1).published answer (List.mem_of_mem_drop member)) inLane
  apply RecursiveCollectionContinuation.start_free_within
  change ∀ name ∈ allocation.request.source.freeFvarNames, name ∈ footprint
  rw [allocation.request_fields.2.2.2.1, sameJob]
  exact (ready lane inLanes).free

theorem installed_ready (names footprint : List String) (depth : Nat)
    (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern)
    (ready : Ready names footprint state) :
    CollectionOccurrenceBatchExecution.StateReady footprint
      (state.batch.install (state.matchers.flatMap (Lane.allocations depth))) := by
  intro frame member
  rcases List.mem_append.mp member with old | fresh
  · exact ready.batch frame old
  · obtain ⟨allocation, inAllocations, rfl⟩ := List.mem_map.mp fresh
    exact fresh_frames_ready names footprint depth state.matchers ready.matchers allocation inAllocations

theorem round_ready (names footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth : Nat)
    (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern)
    (ready : Ready names footprint state) :
    Ready names footprint (CollectionOccurrenceMachine.round depth state) := by
  constructor
  · intro lane member
    obtain ⟨old, inMatchers, rfl⟩ := List.mem_map.mp member
    exact lane_resume_ready names footprint old 1 (ready.matchers old inMatchers)
  · exact CollectionOccurrenceBatchExecution.round_ready footprint finite provider _
      (installed_ready names footprint depth state ready)

/-- Initialize from the actual source-generated lane list. This operation
does not claim to generate that list in the target language. -/
@[metta_head "gslt:occurrence-machine:from-lanes"]
theorem from_lanes_returns (host : Effects.State) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-machine:from-lanes"
        [encoded (encodeList CollectionOccurrenceMatcherExecution.laneTerm
          (lanes plan bound expected sourcePattern))])
      host (encoded (stateTerm (CollectionOccurrenceMachine.begin plan bound expected sourcePattern))) := by
  have native := CollectionOccurrenceBatchExecution.begin_returns host
    ([] : List (Allocation plan bound expected sourcePattern))
  have atInstallation := by
    metta_lift CollectionOccurrenceInstallationExecution.checked ["frames"] native
  have begun := machine_from_publication% ["frames"] atInstallation
  occurrence_machine_eval [begun] unfolding [CollectionOccurrenceMachine.begin]

@[metta_head "gslt:occurrence-machine:round"]
theorem round_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth : Nat)
    (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern)
    (ready : Ready names footprint state) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-machine:round"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (stateTerm state)])
      host (encoded (stateTerm (CollectionOccurrenceMachine.round depth state))) := by
  have advanced := by
    metta_lift checked ["names", "environment", "depth", "lanes"]
      (advance_lanes_returns host names ordered footprint depth state.matchers ready.matchers)
  have installed := machine_from_publication% ["fresh", "state"]
    (CollectionOccurrenceInstallationExecution.install_returns host
      (state.matchers.flatMap (Lane.allocations depth)) state.batch)
  have worked := CollectionOccurrenceBatchExecution.run_returns host footprint finite provider 1
    (state.batch.install (state.matchers.flatMap (Lane.allocations depth)))
    (installed_ready names footprint depth state ready)
  have atInstallation := by
    metta_lift CollectionOccurrenceInstallationExecution.checked ["environment", "work", "state"] worked
  have continued := machine_from_publication% ["environment", "work", "state"] atInstallation
  occurrence_machine_eval [advanced, installed, continued] unfolding
    [advancedLanesTerm, CollectionOccurrenceMachine.round, CollectionOccurrenceBatch.State.run]

@[metta_head "gslt:occurrence-machine:run"]
theorem run_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth : Nat) :
    ∀ (work : Nat) (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern),
      Ready names footprint state →
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-machine:run"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, number work, encoded (stateTerm state)])
      host (encoded (stateTerm (CollectionOccurrenceMachine.run depth work state)))
  | 0, state, _ => by occurrence_machine_eval unfolding [CollectionOccurrenceMachine.run]
  | work + 1, state, ready => by
    have next := round_returns host names ordered footprint finite provider depth state ready
    have later := run_returns host names ordered footprint finite provider depth work
      (CollectionOccurrenceMachine.round depth state)
      (round_ready names footprint finite provider depth state ready)
    occurrence_machine_eval [next, later] unfolding [CollectionOccurrenceMachine.run]

@[metta_head "gslt:occurrence-machine:publication"]
theorem publication_returns (host : Effects.State)
    (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-machine:publication" [encoded (stateTerm state)])
      host (encoded (encodeList CollectionOccurrenceBatchExecution.publicationTerm state.batch.log)) := by
  have native := CollectionOccurrenceBatchExecution.publication_returns host state.batch
  have atInstallation := by
    metta_lift CollectionOccurrenceInstallationExecution.checked ["state"] native
  have read := machine_from_publication% ["state"] atInstallation
  occurrence_machine_eval [read]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution
