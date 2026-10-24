import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesFocus
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchSource
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrencePublication

/-! # Native retained runs and original completed receipt readout -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceBatch CollectionOccurrenceMatcher CollectionOccurrenceHandoff CanonicalCompare
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

theorem begin_ready (names : List String) (named : StandardWire.TableFor plan names)
    (footprint : List String) (declared : Complete.Footprint.Declared plan footprint)
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (input : Pattern) (canonical : input.hasCanonicalBinderMetadata = true) :
    CollectionOccurrenceMachineExecution.Ready names footprint
      (CollectionOccurrenceMachine.begin plan bound expected input) := by
  constructor
  · intro lane member
    obtain ⟨selected, _, rfl⟩ := List.mem_map.mp member
    let job := selected.val
    have valid : job.Valid plan bound expected input := (jobs_exact _ _ _ _ _).mp selected.property
    have fields : job.variant.site.focus = job.origin.site.focus ∧
        job.variant.site.focusBound = job.origin.site.focusBound ∧
        job.variant.site.focusType = job.origin.site.focusType := by
      obtain ⟨context, _, same⟩ := List.mem_map.mp valid.2
      rw [← same]
      exact ⟨rfl,rfl,rfl⟩
    have sorted : WellSorted.OpenPatternWellSorted
        (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
        job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus := by
      simpa only [fields.1, fields.2.1, fields.2.2] using valid.1.2.focus_sorted canonical
    have checked := WellSorted.checkOpenPatternWellSorted_complete sorted
    have target : CanonicalCompare.Covered names job.request.target := named.covered checked
    refine ⟨RecursiveCollectionMachine.start_covered names job.request target, target, ?_, ?_, sorted⟩
    · exact Complete.Footprint.sorted_within declared checked
    · exact admitted job.origin.declaration (List.fst_mem_of_mem_zipIdx valid.1.1)
  · intro frame member
    cases member

@[metta_head "gslt:occurrence-search:finish"]
theorem finish_returns (host : Effects.State) (footprint : List String) (packet : Publication)
    (ready : packet.FinishReady plan bound expected)
    (covered : ∀ name ∈ (packet.job.variant.site.context.fill packet.outcome.target).freeFvarNames,
      name ∈ footprint) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:finish"
        [encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
          encoded (CollectionOccurrenceBatchExecution.publicationTerm packet)])
      host (encoded (encodeOption ScopedRuleJobReadoutExecution.receiptTerm
        (packet.finish? plan bound expected))) := by
  let job := packet.job.preparedJob packet.prepared
  let firing : Complete.DeepRoot.Firing :=
    ⟨packet.prepared.ordinary.trace, packet.prepared.ordinary.assignment,
      packet.outcome.completed, packet.outcome.history, packet.outcome.target⟩
  have valid : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan)
      job.site.focusBound job.site.focusType job.site.focus job.ordinal firing.trace firing.captured
      firing.completed firing.history firing.target := ready.2
  have atDiscovery := discovery_from_complete% ["request", "result"]
    (CompleteExecution.complete_finish_root_returns plan host bound expected
      (packet.job.presentedSource packet.prepared) job ready.1 footprint firing valid covered)
  have finished := by metta_lift checked ["request", "result"] atDiscovery
  have filledAtDiscovery := discovery_from_complete% ["context", "pattern"]
    (CompleteExecution.complete_fill_returns host packet.job.variant.site.context packet.prepared.source)
  have filled := by metta_lift checked ["context", "pattern"] filledAtDiscovery
  have freeSame : (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free := rfl
  have matcherAnswer : RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm packet.prepared.ordinary =
      .application "ScopedMatcherAnswer"
        [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm packet.prepared.ordinary.assignment,
          RuleInstantiationExecution.GeneralExecution.traceTerm packet.prepared.ordinary.trace] := rfl
  rw [packet.finish_eq_lift ready]
  occurrence_search_eval [filled, finished] unfolding
    [CompletePlanWire.planTerm, CollectionOccurrenceBatchExecution.publicationTerm,
      CollectionOccurrenceBatchExecution.originTerm, CollectionContextExecution.variantTerm,
      RecursiveCollectionHandoffExecution.preparedTerm, CompleteExecution.firingTerm,
      ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.siteTerm,
      ScopedRuleJobReadoutExecution.requestProjectionTerm, CollectionOccurrenceHandoff.Job.preparedJob,
      CollectionOccurrenceHandoff.Job.presentedSource, CollectionSelection.refocus,
      PremiseOperationsExecution.GeneralExecution.resultTerm, firing, job,
      matcherAnswer, freeSame, CompleteExecution.environmentValue,
      GeneralRuleJobExecution.Request.environment, GeneralRuleJobExecution.Request.goal,
      PremiseOperationsExecution.GeneralExecution.goalTerm,
      PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
      encodeList, InferenceCettaWire.encodeList,
      CompleteExecution.DescentCodec.patternTerm, CompleteExecution.DescentCodec.assignmentTerm,
      PremiseOperationsExecution.GeneralExecution.traceTerm,
      RuleInstantiationExecution.GeneralExecution.traceTerm,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm]



def PacketReady (footprint : List String) (packet : Publication) : Prop :=
  packet.FinishReady plan bound expected ∧
    ∀ name ∈ (packet.job.variant.site.context.fill packet.outcome.target).freeFvarNames,
      name ∈ footprint

@[metta_head "gslt:occurrence-search:read-log"]
theorem read_log_returns (host : Effects.State) (footprint : List String) :
    ∀ packets : List Publication,
    (∀ packet ∈ packets, PacketReady (plan := plan) (bound := bound) (expected := expected) footprint packet) →
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:read-log"
        [encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
          encoded (encodeList CollectionOccurrenceBatchExecution.publicationTerm packets)])
      host (encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
        (packets.filterMap fun packet => packet.finish? plan bound expected)))
  | [], _ => by occurrence_search_eval unfolding [encodeList]
  | packet :: packets, ready => by
    have first := finish_returns host footprint packet (ready packet List.mem_cons_self).1
      (ready packet List.mem_cons_self).2
    have later := read_log_returns host footprint packets
      (fun next member => ready next (List.mem_cons_of_mem _ member))
    cases finished : packet.finish? plan bound expected <;>
      occurrence_search_eval [first, later] unfolding
        [List.filterMap_cons, finished, encodeList, encodeOption]

theorem run_state_ready (names footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth work : Nat) (input : Pattern)
    (state : CollectionOccurrenceMachine.State plan bound expected input)
    (ready : CollectionOccurrenceMachineExecution.Ready names footprint state) :
    CollectionOccurrenceMachineExecution.Ready names footprint
      (CollectionOccurrenceMachine.run depth work state) := by
  induction work generalizing state with
  | zero => exact ready
  | succ work ih => exact ih _ (CollectionOccurrenceMachineExecution.round_ready
      names footprint finite provider depth state ready)

def Ready (names footprint : List String) (depth : Nat)
    (run : CollectionOccurrenceSearch.Run plan bound expected) : Prop :=
  CollectionOccurrenceMachineExecution.Ready names footprint run.state ∧
    CollectionOccurrenceMachine.Invariant depth run.state

theorem resume_ready (names footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth : Nat) (run : CollectionOccurrenceSearch.Run plan bound expected)
    (ready : Ready names footprint depth run) (work : Nat) :
    Ready names footprint depth
      ((CollectionOccurrenceSearch.search plan bound expected depth).resume run work) := by
  exact ⟨run_state_ready names footprint finite provider depth work _ run.state ready.1,
    CollectionOccurrenceMachine.run_invariant depth work ready.2⟩

theorem ready_packet (names footprint : List String) (depth : Nat)
    (declared : Complete.Footprint.Declared plan footprint)
    (run : CollectionOccurrenceSearch.Run plan bound expected) (ready : Ready names footprint depth run)
    {packet : CollectionOccurrenceBatch.Publication} (member : packet ∈ run.state.batch.log) :
    packet.FinishReady plan bound expected ∧
      ∀ name ∈ (packet.job.variant.site.context.fill packet.outcome.target).freeFvarNames,
        name ∈ footprint := by
  have finished := run.state.batch.publication_finish_ready ready.2.1 member
  exact ⟨finished, packet.finish_target_free_within footprint declared finished⟩

theorem run_ready (names : List String) (named : StandardWire.TableFor plan names)
    (footprint : List String) (scope : Complete.Footprint.Scope plan footprint)
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (depth : Nat) (input : Pattern) (checked : Complete.Classes.Checked plan bound expected input)
    (work : Nat) : Ready names footprint depth
      ((CollectionOccurrenceSearch.search plan bound expected depth).run input work) := by
  have typed := CanonicalBags.openPatternWellSorted_canon
    (WellSorted.checkOpenPatternWellSorted_sound checked)
  have begun := begin_ready (bound := bound) (expected := expected) names named footprint scope.declared admitted
    (CanonicalBags.canon input) typed.2.1
  exact ⟨run_state_ready names footprint scope.finite scope.provider depth work _ _ begun,
    CollectionOccurrenceMachine.run_invariant depth work (CollectionOccurrenceMachine.begin_invariant depth)⟩

theorem publication_checked (names footprint : List String) (depth : Nat)
    (run : CollectionOccurrenceSearch.Run plan bound expected) (ready : Ready names footprint depth run)
    {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ (CollectionOccurrenceSearch.search plan bound expected depth).publication run) :
    Complete.Classes.Checked plan bound expected receipt.target := by
  obtain ⟨packet, logged, finished⟩ := List.mem_filterMap.mp member
  have packetReady := run.state.batch.publication_finish_ready ready.2.1 logged
  have valid := packet.finished_valid packetReady finished
  exact WellSorted.checkOpenPatternWellSorted_complete valid.2.2.2.2


@[metta_head "gslt:occurrence-search:with-state"]
theorem with_state_returns (host : Effects.State) (footprint : List String)
    (run : CollectionOccurrenceSearch.Run plan bound expected)
    (ready : ∀ packet ∈ run.state.batch.log,
      PacketReady (plan := plan) (bound := bound) (expected := expected) footprint packet) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:with-state"
        [encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
          encoded (InferenceCettaWire.encodePattern run.source),
          encoded (CollectionOccurrenceMachineExecution.stateTerm run.state)])
      host (encoded (runTerm (plan.snapshot.free.entriesOn footprint) run)) := by
  have observed := read_log_returns host footprint run.state.batch.log ready
  occurrence_search_eval [observed] unfolding
    [runTerm, CollectionOccurrenceMachineExecution.stateTerm, CollectionOccurrenceBatchExecution.stateTerm]

@[metta_head "gslt:occurrence-search:publication"]
theorem publication_returns (host : Effects.State) (table : List (String × TypeExpr))
    (run : CollectionOccurrenceSearch.Run plan bound expected) (depth : Nat) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:publication" [encoded (runTerm table run)])
      host (encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
        ((CollectionOccurrenceSearch.search plan bound expected depth).publication run))) := by
  occurrence_search_eval unfolding [runTerm, CollectionOccurrenceSearch.search]

@[metta_head "gslt:occurrence-search:resume"]
theorem resume_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (declared : Complete.Footprint.Declared plan footprint)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth work : Nat)
    (run : CollectionOccurrenceSearch.Run plan bound expected) (ready : Ready names footprint depth run) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:resume"
        [encoded (encodeList Term.string names), number depth,
          encoded (runTerm (plan.snapshot.free.entriesOn footprint) run), number work])
      host (encoded (runTerm (plan.snapshot.free.entriesOn footprint)
        ((CollectionOccurrenceSearch.search plan bound expected depth).resume run work))) := by
  have advanced := search_from_machine% ["names", "environment", "depth", "work", "state"]
    (CollectionOccurrenceMachineExecution.run_returns host names ordered footprint finite provider depth
      work run.state ready.1)
  have resumedReady := resume_ready names footprint finite provider depth run ready work
  have observed := with_state_returns host footprint
    ((CollectionOccurrenceSearch.search plan bound expected depth).resume run work)
    (fun packet member => ready_packet names footprint depth declared _ resumedReady member)
  have freeSame : (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free := rfl
  occurrence_search_eval [advanced, observed] unfolding
    [runTerm, CompletePlanWire.planTerm, CollectionOccurrenceSearch.search,
      CompleteExecution.environmentValue, freeSame]

@[metta_head "gslt:occurrence-search:run"]
theorem run_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (declared : Complete.Footprint.Declared plan footprint)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth work : Nat) (input : Pattern) (covered : Covered names input)
    (free : ∀ name ∈ (CanonicalBags.canon input).freeFvarNames, name ∈ footprint)
    (ready : CollectionOccurrenceMachineExecution.Ready names footprint
      (CollectionOccurrenceMachine.begin plan bound expected (CanonicalBags.canon input))) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:run"
        [encoded (encodeList Term.string names), number depth,
          encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
          encoded (InferenceCettaWire.encodePattern input), number work])
      host (encoded (runTerm (plan.snapshot.free.entriesOn footprint)
        ((CollectionOccurrenceSearch.search plan bound expected depth).run input work))) := by
  have canonical := search_from_canonical% ["names", "pattern"]
    (CompleteExecution.canon_returns host ordered input covered)
  have discovered := by
    metta_lift checked ["declarations", "free", "permissions", "bound", "expected", "source", "rules"]
      (CollectionOccurrenceDiscoveryExecution.begin_returns host plan bound expected
        (CanonicalBags.canon input) footprint free)
  have advanced := search_from_machine% ["names", "environment", "depth", "work", "state"]
    (CollectionOccurrenceMachineExecution.run_returns host names ordered footprint finite provider depth work
      (CollectionOccurrenceMachine.begin plan bound expected (CanonicalBags.canon input)) ready)
  have runReady : Ready names footprint depth
      ((CollectionOccurrenceSearch.search plan bound expected depth).run input work) :=
    ⟨run_state_ready names footprint finite provider depth work _ _ ready,
      CollectionOccurrenceMachine.run_invariant depth work (CollectionOccurrenceMachine.begin_invariant depth)⟩
  have observed := with_state_returns host footprint
    ((CollectionOccurrenceSearch.search plan bound expected depth).run input work)
    (fun packet member => ready_packet names footprint depth declared _ runReady member)
  have freeSame : (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free := rfl
  occurrence_search_eval [canonical, discovered, advanced, observed] unfolding
    [runTerm, CompletePlanWire.planTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      CollectionOccurrenceSearch.search, CompleteExecution.environmentValue, freeSame,
      PremiseOperationsExecution.DeclarationTyping.declarationsTerm,
      PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
      PremiseOperationsExecution.DeclarationTyping.boundContextTerm, encodeList, InferenceCettaWire.encodeList,
      CompleteExecution.patternValue]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution
