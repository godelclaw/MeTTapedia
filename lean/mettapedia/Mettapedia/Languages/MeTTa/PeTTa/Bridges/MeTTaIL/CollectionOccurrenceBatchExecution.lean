import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContextExecution
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch

/-!
# Native chronological batches of prepared collection occurrences

The native batch retains each full occurrence and recursive allocation. Its
per-frame suffix drain realizes the proved receipt-permutation account.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionOccurrenceBatch
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_occurrences.metta"
    sha256 "1a1cfbef65f6a0320ea0fa2e1a067665f14b950ea2f6fedcdc6e573839b2d352"

def library : BridgeKit.Library :=
  ⟨RecursiveCollectionContinuationExecution.library.runtime, source.program,
    ["gslt:occurrence-batch:"]⟩

theorem checked : library.check = true := by decide +kernel

def originTerm (job : CollectionOccurrenceHandoff.Job)
    (answer : RecursiveCollectionMachine.Answer) : Term :=
  .application "RecursiveCollectionOrigin"
    [ScopedRuleJobReadoutExecution.jobTerm job.origin,
      CollectionContextExecution.variantTerm job.variant,
      RecursiveCollectionExecution.answerTerm answer]

def frameTerm (frame : Frame plan bound expected sourcePattern) : Term :=
  .application "RecursiveOccurrenceFrame"
    [originTerm frame.allocation.job frame.allocation.answer,
      RecursiveCollectionContinuationExecution.frameTerm frame.allocation.request frame.state]

def publicationTerm (packet : Publication) : Term :=
  .application "RecursiveOccurrencePublication"
    [originTerm packet.job packet.answer,
      .application "RecursiveCollectionContinued"
        [RecursiveCollectionHandoffExecution.preparedTerm packet.prepared,
          CompleteExecution.firingTerm packet.outcome]]

def stateTerm (batch : State plan bound expected sourcePattern) : Term :=
  .application "RecursiveOccurrenceBatch"
    [encodeList frameTerm batch.frames, encodeList publicationTerm batch.log]

syntax "occurrence_batch_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| occurrence_batch_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        frameTerm, publicationTerm, stateTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        $extra,*]))

def FrameReady (footprint : List String) (frame : Frame plan bound expected sourcePattern) : Prop :=
  StructuralDescent.Scheduled.stateFreeWithin footprint frame.allocation.request.environment
    frame.allocation.request.goal frame.state

theorem run_ready (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (frame : Frame plan bound expected sourcePattern) (work : Nat)
    (covered : FrameReady footprint frame) : FrameReady footprint (Frame.run work frame) := by
  have same := frame.allocation.request_origin.1
  have rows := GeneralPremise.provider_coverage_mono _ footprint
    frame.allocation.request.environment.provider (by simpa only [same] using provider)
    (GeneralPremise.provider_covered_by_own_names frame.allocation.request.environment.provider)
  have dynamic := GeneralPremise.Query.DynamicOutputsFreeWithin.of_unregistered footprint
    frame.allocation.request.environment (by simpa only [same] using finite)
  exact StructuralDescent.Scheduled.run_free_within footprint frame.allocation.request.environment
    _ rows dynamic work frame.state covered

@[metta_head "gslt:occurrence-batch:frame-begin"]
theorem frame_begin_returns (host : Effects.State)
    (allocation : Allocation plan bound expected sourcePattern) (footprint : List String)
    (inside : ∀ name ∈ allocation.request.source.freeFvarNames, name ∈ footprint) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:frame-begin"
        [encoded (originTerm allocation.job allocation.answer),
          CompleteExecution.environmentValue allocation.request.environment
            (allocation.request.environment.free.entriesOn footprint),
          number allocation.request.depth,
          encoded (CompleteExecution.DescentCodec.typesTerm allocation.request.bound),
          encoded (CompleteExecution.DescentCodec.typeTerm allocation.request.type),
          number allocation.request.index,
          encoded (InferenceCettaWire.AuthoredRule.rewriteTerm allocation.request.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm allocation.request.spec),
          encoded (RecursiveCollectionHandoffExecution.preparedTerm allocation.request.prepared)])
      host (encoded (frameTerm (Frame.initial allocation))) := by
  have native := RecursiveCollectionContinuationExecution.begin_returns host allocation.request footprint inside
  have begun := by
    metta_lift checked ["environment", "depth", "bound", "type", "index", "rule", "spec", "prepared"] native
  occurrence_batch_eval [begun] unfolding [Frame.initial]

@[metta_head "gslt:occurrence-batch:frame-run"]
theorem frame_run_returns (host : Effects.State) (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (frame : Frame plan bound expected sourcePattern) (work : Nat)
    (covered : FrameReady footprint frame) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:frame-run"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
          ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number work, encoded (frameTerm frame)])
      host (encoded (frameTerm (Frame.run work frame))) := by
  have same := frame.allocation.request_origin.1
  have native := RecursiveCollectionContinuationExecution.run_returns host frame.allocation.request
    footprint (by simpa only [same] using finite) (by simpa only [same] using provider)
    frame.state work covered
  have advanced := by metta_lift checked ["environment", "work", "frame"] native
  simp only [same] at advanced
  occurrence_batch_eval [advanced] unfolding [Frame.run]

@[metta_head "gslt:occurrence-batch:tag"]
theorem tag_returns (host : Effects.State) (allocation : Allocation plan bound expected sourcePattern) :
    ∀ packets : List Complete.DeepRoot.Firing,
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:tag"
        [encoded (originTerm allocation.job allocation.answer),
          encoded (encodeList (RecursiveCollectionContinuationExecution.publicationTerm allocation.request) packets)])
      host (encoded (encodeList publicationTerm (packets.map (tag allocation))))
  | [] => by occurrence_batch_eval
  | packet :: packets => by
    have later := tag_returns host allocation packets
    have same := allocation.request_origin.2
    occurrence_batch_eval [later] unfolding
      [tag, RecursiveCollectionContinuationExecution.publicationTerm, same]

@[metta_head "gslt:occurrence-batch:frame-publication"]
theorem frame_publication_returns (host : Effects.State)
    (frame : Frame plan bound expected sourcePattern) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:frame-publication" [encoded (frameTerm frame)])
      host (encoded (encodeList publicationTerm frame.publication)) := by
  have native := RecursiveCollectionContinuationExecution.publication_returns host
    frame.allocation.request frame.state
  have published := by metta_lift checked ["frame"] native
  have tagged := tag_returns host frame.allocation
    (RecursiveCollectionContinuation.publication frame.allocation.request frame.state)
  occurrence_batch_eval [published, tagged] unfolding [Frame.publication]

private theorem append_returns {α : Type} (encoder : α → Term) (host : Effects.State) (left right : List α) :
    PureReturns library.runtime [] host
      (apply "gslt:automata:append" [encoded (encodeList encoder left), encoded (encodeList encoder right)]) host (encoded (encodeList encoder (left ++ right))) := by
  have atBase := by
    metta_lift CollectionMatcherBackendExecution.collectionBase_checked ["left", "right"] (CompleteExecution.complete_append_returns encoder host left right)
  have atBackend := by
    metta_lift CollectionMatcherBackendExecution.checked ["left", "right"] atBase
  have atContinuation := by
    metta_lift RecursiveCollectionContinuationExecution.checked ["left", "right"] atBackend
  metta_lift checked ["left", "right"] atContinuation

private theorem length_returns {α : Type} (encoder : α → Term) (host : Effects.State) (items : List α) :
    PureReturns library.runtime [] host
      (apply "gslt:automata:length" [encoded (encodeList encoder items)]) host (number items.length) := by
  have atBase := by
    metta_lift CollectionMatcherBackendExecution.collectionBase_checked ["items"] (CompleteExecution.complete_length_returns encoder host items)
  have atBackend := by
    metta_lift CollectionMatcherBackendExecution.checked ["items"] atBase
  have atContinuation := by
    metta_lift RecursiveCollectionContinuationExecution.checked ["items"] atBackend
  metta_lift checked ["items"] atContinuation

private theorem drop_returns {α : Type} (encoder : α → Term) (host : Effects.State) (count : Nat) (items : List α) :
    PureReturns library.runtime [] host
      (apply "gslt:complete:drop" [number count, encoded (encodeList encoder items)]) host (encoded (encodeList encoder (items.drop count))) := by
  have atBase := by
    metta_lift CollectionMatcherBackendExecution.collectionBase_checked ["count", "items"] (CompleteExecution.drop_list_returns encoder host count items)
  have atBackend := by
    metta_lift CollectionMatcherBackendExecution.checked ["count", "items"] atBase
  have atContinuation := by
    metta_lift RecursiveCollectionContinuationExecution.checked ["count", "items"] atBackend
  metta_lift checked ["count", "items"] atContinuation

def advancedFramesTerm (frames : List (Frame plan bound expected sourcePattern)) : Term :=
  .application "RecursiveOccurrenceAdvanced"
    [encodeList frameTerm (frames.map (Frame.run 1)),
      encodeList publicationTerm (frames.flatMap Frame.fresh)]

@[metta_head "gslt:occurrence-batch:advance-frames"]
theorem advance_frames_returns (host : Effects.State) (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) :
    ∀ frames : List (Frame plan bound expected sourcePattern),
    (∀ frame ∈ frames, FrameReady footprint frame) →
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:advance-frames"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
          ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          encoded (encodeList frameTerm frames)])
      host (encoded (advancedFramesTerm frames))
  | [], _ => by occurrence_batch_eval unfolding [advancedFramesTerm]
  | frame :: frames, covered => by
    have previous := frame_publication_returns host frame
    have count := length_returns publicationTerm host frame.publication
    have advanced := frame_run_returns host footprint finite provider frame 1
      (covered frame List.mem_cons_self)
    have published := frame_publication_returns host (Frame.run 1 frame)
    have fresh := drop_returns publicationTerm host frame.publication.length
      (Frame.run 1 frame).publication
    have later := advance_frames_returns host footprint finite provider frames
      (fun child member => covered child (List.mem_cons_of_mem _ member))
    have joined := append_returns publicationTerm host frame.fresh (frames.flatMap Frame.fresh)
    simp only [advancedFramesTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] at later
    occurrence_batch_eval [previous, count, advanced, published, fresh, later, joined]
      unfolding [advancedFramesTerm, Frame.fresh, List.flatMap_cons]

@[metta_head "gslt:occurrence-batch:begin"]
theorem begin_returns (host : Effects.State)
    (allocations : List (Allocation plan bound expected sourcePattern)) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:begin" [encoded (encodeList frameTerm (allocations.map Frame.initial))])
      host (encoded (stateTerm (State.begin allocations))) := by
  occurrence_batch_eval unfolding [State.begin]

def StateReady (footprint : List String) (batch : State plan bound expected sourcePattern) : Prop :=
  ∀ frame ∈ batch.frames, FrameReady footprint frame

theorem round_ready (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (batch : State plan bound expected sourcePattern)
    (covered : StateReady footprint batch) : StateReady footprint batch.round := by
  intro frame member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact run_ready footprint finite provider original 1 (covered original present)

@[metta_head "gslt:occurrence-batch:resume"]
theorem resume_returns (host : Effects.State) (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) :
    ∀ (work : Nat) (batch : State plan bound expected sourcePattern), StateReady footprint batch →
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:resume"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
          ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number work, encoded (encodeList frameTerm batch.frames), encoded (encodeList publicationTerm batch.log)])
      host (encoded (stateTerm (State.run work batch)))
  | 0, batch, _ => by occurrence_batch_eval unfolding [State.run]
  | work + 1, batch, covered => by
    have advanced := advance_frames_returns host footprint finite provider batch.frames covered
    have joined := append_returns publicationTerm host batch.log (batch.frames.flatMap Frame.fresh)
    have later := resume_returns host footprint finite provider work batch.round
      (round_ready footprint finite provider batch covered)
    simp only [advancedFramesTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] at advanced
    occurrence_batch_eval [advanced, joined, later] unfolding [State.run, State.round]

@[metta_head "gslt:occurrence-batch:run"]
theorem run_returns (host : Effects.State) (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (work : Nat) (batch : State plan bound expected sourcePattern)
    (covered : StateReady footprint batch) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:run"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
          ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number work, encoded (stateTerm batch)])
      host (encoded (stateTerm (State.run work batch))) := by
  have native := resume_returns host footprint finite provider work batch covered
  occurrence_batch_eval [native]

@[metta_head "gslt:occurrence-batch:publication"]
theorem publication_returns (host : Effects.State) (batch : State plan bound expected sourcePattern) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:publication" [encoded (stateTerm batch)])
      host (encoded (encodeList publicationTerm batch.log)) := by
  occurrence_batch_eval

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution
