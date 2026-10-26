import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RootFamily

/-!
# Retained native collection continuations

Raw allocation origins own the existing typed/premise states. The native
operations below compute those states and their chronological publication;
they do not introduce another explorer or an admission authority.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionMatcherBackend
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open CollectionMatcherBackendExecution (library)

variable {plan : GeneralExecutionAdmission.Plan}
    {certificate : CollectionExecutionAdmission.Certificate plan}
    {source : Pattern} {type : TypeExpr}

def publicationTerm (publication : Retained.Publication) : Term :=
  .application "CollectionContinued"
    [.natural publication.matched.ordinal,
      ScopedCollectionExecution.requestTerm publication.matched.request,
      ScopedCollectionExecution.receiptTerm publication.matched.receipt,
      CompleteExecution.firingTerm publication.outcome]

def frameTerm (frame : Retained.Frame plan certificate source type) : Term :=
  .application "CollectionContinuation"
    [.natural frame.matched.ordinal, ScopedCollectionExecution.requestTerm frame.matched.request,
      ScopedCollectionExecution.receiptTerm frame.matched.receipt, .natural frame.depth,
      CompleteExecution.DescentCodec.stateTerm frame.state]

def stateTerm (search : Retained.State plan certificate source type) : Term :=
  .application "CollectionContinuedState"
    [encodeList frameTerm search.frames, encodeList publicationTerm search.log]

def FrameReady (footprint : List String) (frame : Retained.Frame plan certificate source type) : Prop :=
  StructuralDescent.Scheduled.stateFreeWithin footprint (GeneralPlanEnvironment.environment plan)
    (.root (frame.depth + 1) [] type
      (CollectionMatcherCompatibility.ordinaryTarget frame.matched.request frame.matched.receipt)
      frame.matched.ordinal) frame.state

theorem initial_ready (matched : Retained.Match)
    (authority : MatchAuthority plan certificate source matched.ordinal matched.request matched.receipt)
    (typed : WellSorted.OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source)
    (depth : Nat) (footprint : List String)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    FrameReady footprint (Retained.Frame.initial matched authority typed depth) :=
  startMatch_free_within plan certificate source depth type matched.ordinal matched.request
    matched.receipt authority typed footprint inside

theorem run_ready (footprint : List String)
    (finiteProvider : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint)
    (frame : Retained.Frame plan certificate source type) (work : Nat)
    (covered : FrameReady footprint frame) : FrameReady footprint (Retained.Frame.run work frame) := by
  have rows := GeneralPremise.provider_coverage_mono _ footprint
    (GeneralPlanEnvironment.environment plan).provider provider
    (GeneralPremise.provider_covered_by_own_names (GeneralPlanEnvironment.environment plan).provider)
  have dynamic := GeneralPremise.Query.DynamicOutputsFreeWithin.of_unregistered footprint
    (GeneralPlanEnvironment.environment plan) finiteProvider
  exact StructuralDescent.Scheduled.run_free_within Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.ordinary_preservesFreeNames footprint
    (GeneralPlanEnvironment.environment plan) _ rows dynamic work frame.state covered

private theorem append_returns {α : Type} (encoder : α → Term)
    (state : Effects.State) (left right : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:append"
        [encoded (encodeList encoder left), encoded (encodeList encoder right)])
      state (encoded (encodeList encoder (left ++ right))) := by
  exact CompleteExecution.complete_append_returns encoder state left right

private theorem length_returns {α : Type} (encoder : α → Term)
    (state : Effects.State) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:length" [encoded (encodeList encoder items)])
      state (number items.length) := by
  exact CompleteExecution.complete_length_returns encoder state items

private theorem drop_returns {α : Type} (encoder : α → Term)
    (state : Effects.State) (count : Nat) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:complete:drop" [number count, encoded (encodeList encoder items)])
      state (encoded (encodeList encoder (items.drop count))) := by
  exact CompleteExecution.drop_list_returns encoder state count items

@[metta_head "gslt:collection-backend:frame-begin"]
theorem frame_begin_returns (state : Effects.State) (footprint : List String)
    (matched : Retained.Match)
    (authority : MatchAuthority plan certificate source matched.ordinal matched.request matched.receipt)
    (typed : WellSorted.OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] type source)
    (depth : Nat) (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:frame-begin"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (InferenceCettaWire.AuthoredRule.typeTerm type), number matched.ordinal,
          encoded (ScopedCollectionExecution.requestTerm matched.request),
          encoded (ScopedCollectionExecution.receiptTerm matched.receipt)])
      state (encoded (frameTerm (Retained.Frame.initial matched authority typed depth))) := by
  have begun := CollectionMatcherBackendExecution.begin_match_returns state
    (GeneralPlanEnvironment.environment plan) footprint depth type matched.ordinal matched.request
    matched.receipt authority.ready authority.fixed authority.valid authority.declared authority.specified
    authority.admitted (authority.source_typed typed) (authority.captures_free_within footprint inside)
  collection_backend_eval [begun] unfolding [frameTerm, Retained.Frame.initial]

private theorem descent_returns (state : Effects.State) (footprint : List String)
    (finiteProvider : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint)
    (frame : Retained.Frame plan certificate source type) (work : Nat)
    (covered : FrameReady footprint frame) :
    PureReturns library.runtime [] state
      (apply "gslt:descent:run"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number work, encoded (CompleteExecution.DescentCodec.stateTerm frame.state)])
      state (encoded (CompleteExecution.DescentCodec.stateTerm (Retained.Frame.run work frame).state)) := by
  exact CompleteExecution.descent_run_returns state (GeneralPlanEnvironment.environment plan)
    finiteProvider footprint provider _ work frame.state covered

@[metta_head "gslt:collection-backend:frame-run"]
theorem frame_run_returns (state : Effects.State) (footprint : List String)
    (finiteProvider : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint)
    (frame : Retained.Frame plan certificate source type) (work : Nat)
    (covered : FrameReady footprint frame) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:frame-run"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number work, encoded (frameTerm frame)])
      state (encoded (frameTerm (Retained.Frame.run work frame))) := by
  have native := descent_returns state footprint finiteProvider provider frame work covered
  collection_backend_eval [native] unfolding [frameTerm, Retained.Frame.run]

@[metta_head "gslt:collection-backend:frame-results"]
theorem frame_results_returns (state : Effects.State)
    (frame : Retained.Frame plan certificate source type) :
    ∀ results : List (StructuralDescent.Scheduled.Result (GeneralPlanEnvironment.environment plan)
      (.root (frame.depth + 1) [] type
        (CollectionMatcherCompatibility.ordinaryTarget frame.matched.request frame.matched.receipt)
        frame.matched.ordinal)),
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:frame-results"
        [number frame.matched.ordinal, encoded (ScopedCollectionExecution.requestTerm frame.matched.request),
          encoded (ScopedCollectionExecution.receiptTerm frame.matched.receipt),
          encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
            frame.matched.receipt.matching.assignment),
          encoded (encodeList CompleteExecution.DescentCodec.resultTerm results)])
      state (encoded (encodeList publicationTerm (results.filterMap frame.read)))
  | [] => by collection_backend_eval
  | result :: rest => by
    have later := frame_results_returns state frame rest
    cases result with
    | root trace captured completed history target held =>
      by_cases same : captured = frame.matched.receipt.matching.assignment
      · collection_backend_eval [later] unfolding [Retained.Frame.read, Complete.DeepRoot.read,
          publicationTerm, CompleteExecution.firingTerm, CompleteExecution.DescentCodec.resultTerm,
          CompleteExecution.DescentCodec.answerTerm, same,
          RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective.eq_iff, encodeList]
      · have wire_ne : RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm captured ≠
            RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.matched.receipt.matching.assignment :=
          fun equal => same (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective equal)
        collection_backend_eval [later] unfolding [Retained.Frame.read, Complete.DeepRoot.read,
          publicationTerm, CompleteExecution.firingTerm, CompleteExecution.DescentCodec.resultTerm,
          CompleteExecution.DescentCodec.answerTerm, same, wire_ne,
          RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective.eq_iff, encodeList]

@[metta_head "gslt:collection-backend:frame-publication"]
theorem frame_publication_returns (state : Effects.State)
    (frame : Retained.Frame plan certificate source type) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:frame-publication" [encoded (frameTerm frame)])
      state (encoded (encodeList publicationTerm frame.publication)) := by
  have published := frame_results_returns state frame frame.state.answers
  collection_backend_eval [published] unfolding [frameTerm, Retained.Frame.publication,
    CompleteExecution.DescentCodec.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
    ScopedCollectionExecution.receiptTerm, CollectionSelectionExecution.allocationTerm,
    RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm]

@[metta_head "gslt:collection-backend:frame-settled"]
theorem frame_settled_returns (state : Effects.State)
    (frame : Retained.Frame plan certificate source type) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:frame-settled" [encoded (frameTerm frame)])
      state (encoded (CollectionSelectionExecution.booleanTerm frame.state.agenda.isEmpty)) := by
  cases agenda : frame.state.agenda with
  | nil | cons =>
    collection_backend_eval unfolding [frameTerm, CompleteExecution.DescentCodec.stateTerm,
      PremiseSchedulerExecution.schedulerStateTerm, agenda, CollectionSelectionExecution.booleanTerm,
      encodeList]

@[metta_head "gslt:collection-backend:frames-publication"]
theorem frames_publication_returns (state : Effects.State) :
    ∀ frames : List (Retained.Frame plan certificate source type),
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:frames-publication" [encoded (encodeList frameTerm frames)])
      state (encoded (encodeList publicationTerm (frames.flatMap Retained.Frame.publication)))
  | [] => by collection_backend_eval
  | frame :: frames => by
    have first := frame_publication_returns state frame
    have later := frames_publication_returns state frames
    have joined := append_returns publicationTerm state frame.publication
      (frames.flatMap Retained.Frame.publication)
    collection_backend_eval [first, later, joined] unfolding [List.flatMap_cons]

def advancedFramesTerm (frames : List (Retained.Frame plan certificate source type)) : Term :=
  .application "CollectionContinuedAdvanced"
    [encodeList frameTerm (frames.map (Retained.Frame.run 1)),
      encodeList publicationTerm (frames.flatMap Retained.Frame.fresh)]

@[metta_head "gslt:collection-backend:advance-frames"]
theorem advance_frames_returns (state : Effects.State) (footprint : List String)
    (finiteProvider : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) :
    ∀ frames : List (Retained.Frame plan certificate source type),
      (∀ frame ∈ frames, FrameReady footprint frame) →
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:advance-frames"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          encoded (encodeList frameTerm frames)])
      state (encoded (advancedFramesTerm frames))
  | [], _ => by collection_backend_eval unfolding [advancedFramesTerm]
  | frame :: frames, covered => by
    have previous := frame_publication_returns state frame
    have count := length_returns publicationTerm state frame.publication
    have advanced := frame_run_returns state footprint finiteProvider provider frame 1
      (covered frame List.mem_cons_self)
    have published := frame_publication_returns state (Retained.Frame.run 1 frame)
    have fresh := drop_returns publicationTerm state frame.publication.length
      (Retained.Frame.run 1 frame).publication
    have later := advance_frames_returns state footprint finiteProvider provider frames
      (fun child present => covered child (List.mem_cons_of_mem _ present))
    have joined := append_returns publicationTerm state frame.fresh
      (frames.flatMap Retained.Frame.fresh)
    simp only [advancedFramesTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] at later
    collection_backend_eval [previous, count, advanced, published, fresh, later, joined]
      unfolding [advancedFramesTerm, Retained.Frame.fresh, List.flatMap_cons]

@[metta_head "gslt:collection-backend:state-begin"]
theorem state_begin_returns (state : Effects.State)
    (frames : List (Retained.Frame plan certificate source type)) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:state-begin" [encoded (encodeList frameTerm frames)])
      state (encoded (stateTerm (Retained.State.begin frames))) := by
  have published := frames_publication_returns state frames
  collection_backend_eval [published] unfolding [stateTerm, Retained.State.begin]

def StateReady (footprint : List String) (search : Retained.State plan certificate source type) : Prop :=
  ∀ frame ∈ search.frames, FrameReady footprint frame

theorem round_ready (footprint : List String)
    (finiteProvider : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint)
    (search : Retained.State plan certificate source type) (covered : StateReady footprint search) :
    StateReady footprint search.round := by
  intro frame member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact run_ready footprint finiteProvider provider original 1 (covered original present)

@[metta_head "gslt:collection-backend:state-resume"]
theorem state_resume_returns (state : Effects.State) (footprint : List String)
    (finiteProvider : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) :
    ∀ (work : Nat) (search : Retained.State plan certificate source type), StateReady footprint search →
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:state-resume"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number work, encoded (encodeList frameTerm search.frames),
          encoded (encodeList publicationTerm search.log)])
      state (encoded (stateTerm (Retained.State.run work search)))
  | 0, search, _ => by
    collection_backend_eval unfolding [stateTerm, Retained.State.run]
  | work + 1, search, covered => by
    have advanced := advance_frames_returns state footprint finiteProvider provider search.frames covered
    have joined := append_returns publicationTerm state search.log
      (search.frames.flatMap Retained.Frame.fresh)
    have later := state_resume_returns state footprint finiteProvider provider work search.round
      (round_ready footprint finiteProvider provider search covered)
    simp only [advancedFramesTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] at advanced
    collection_backend_eval [advanced, joined, later]
      unfolding [stateTerm, Retained.State.run, Retained.State.round]

@[metta_head "gslt:collection-backend:state-run"]
theorem state_run_returns (state : Effects.State) (footprint : List String)
    (finiteProvider : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint)
    (work : Nat) (search : Retained.State plan certificate source type) (covered : StateReady footprint search) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:state-run"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number work, encoded (stateTerm search)])
      state (encoded (stateTerm (Retained.State.run work search))) := by
  have native := state_resume_returns state footprint finiteProvider provider work search covered
  collection_backend_eval [native] unfolding [stateTerm]

@[metta_head "gslt:collection-backend:frames-settled"]
theorem frames_settled_returns (state : Effects.State) :
    ∀ frames : List (Retained.Frame plan certificate source type),
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:frames-settled" [encoded (encodeList frameTerm frames)])
      state (encoded (CollectionSelectionExecution.booleanTerm
        (frames.all fun frame => frame.state.agenda.isEmpty)))
  | [] => by collection_backend_eval
  | frame :: frames => by
    have first := frame_settled_returns state frame
    have later := frames_settled_returns state frames
    cases finished : frame.state.agenda.isEmpty <;>
      simp only [List.all_cons, finished, Bool.true_and, Bool.false_and] <;>
      collection_backend_eval [first, later] unfolding [finished, CollectionSelectionExecution.booleanTerm]

@[metta_head "gslt:collection-backend:state-settled"]
theorem state_settled_returns (state : Effects.State)
    (search : Retained.State plan certificate source type) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:state-settled" [encoded (stateTerm search)])
      state (encoded (CollectionSelectionExecution.booleanTerm search.complete)) := by
  have native := frames_settled_returns state search.frames
  collection_backend_eval [native] unfolding [stateTerm, Retained.State.complete]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.initial_ready
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.run_ready
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.frame_begin_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.frame_run_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.frame_results_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.frame_publication_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.frame_settled_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.frames_publication_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.advance_frames_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.state_begin_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.state_resume_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.state_run_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.frames_settled_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution.state_settled_returns
