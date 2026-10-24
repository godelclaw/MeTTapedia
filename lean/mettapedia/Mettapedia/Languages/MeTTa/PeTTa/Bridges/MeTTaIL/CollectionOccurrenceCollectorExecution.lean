import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceRuntime
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceReadout

/-!
# Native preparation and installation of newly matched occurrence allocations

The collector applies the existing local checks and presentation replay,
retains the original occurrence/allocation packet, and starts the existing
conditional continuation. It grants no new source admission authority.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceBatch CollectionOccurrenceMatcher CanonicalCompare
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open CollectionOccurrenceRuntime
open scoped ProgramQuotation

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_collector.metta"
    sha256 "3d2b3b9a27806ba08536065927c3fc24c8e306443c3cd955325a36e105be063d"

def library : Library :=
  ⟨CollectionOccurrenceRuntime.runtime, source.program, ["gslt:occurrence-collector:"]⟩

theorem checked : library.check = true := by decide +kernel

syntax "collector_from_descent% " "[" str,* "] " term:max : term
macro_rules
  | `(collector_from_descent% [$names,*] $fact) =>
    `(by
      have atComplete := by metta_lift CompleteExecution.complete_checked [$names,*] $fact
      have atBase := by metta_lift CollectionMatcherBackendExecution.collectionBase_checked [$names,*] atComplete
      have atBackend := by metta_lift CollectionMatcherBackendExecution.checked [$names,*] atBase
      have atContinuation := by metta_lift RecursiveCollectionContinuationExecution.checked [$names,*] atBackend
      have atBatch := by metta_lift CollectionOccurrenceBatchExecution.checked [$names,*] atContinuation
      have atInstallation := by metta_lift CollectionOccurrenceInstallationExecution.checked [$names,*] atBatch
      have atRuntime := occurrence_from_publication% [$names,*] atInstallation
      metta_lift checked [$names,*] atRuntime)

syntax "collector_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| collector_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

/-- Every successful mathematical allocation is realized by the native
collector. `made` is the actual producer computation, not a supplied target
execution or source-completeness premise. -/
@[metta_head "gslt:occurrence-collector:allocate"]
theorem allocated_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected sourcePattern)
    (work depth : Nat) (answer : RecursiveCollectionMachine.Answer)
    (published : Published job work answer)
    (covered : Covered names job.request.target)
    (inside : ∀ name ∈ job.variant.site.focus.freeFvarNames, name ∈ footprint)
    (allocation : Allocation plan bound expected sourcePattern)
    (made : allocate? job licensed work answer published depth = some allocation) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-collector:allocate"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (CollectionOccurrenceMatcherExecution.originTerm job),
          encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request),
          encoded (RecursiveCollectionExecution.answerTerm answer)])
      host (encoded (.application "Some" [CollectionOccurrenceBatchExecution.frameTerm (Frame.initial allocation)])) := by
  obtain ⟨sameJob, sameAnswer, sameDepth, computed⟩ :=
    allocate_readout job licensed work depth answer published made
  have checkedLocal := allocation.static_checked
  rw [sameJob] at checkedLocal
  have nativePreparation := RecursiveCollectionHandoffExecution.prepare_returns host names ordered
    job.request answer (RecursiveCollectionMachine.published_trace_valid job.request work published) covered
  rw [computed] at nativePreparation
  have prepared := by
    metta_lift checked ["names", "request", "answer"]
      (occurrence_from_preparation% ["names", "request", "answer"] nativePreparation)
  have admission := collector_from_descent% ["rule", "spec"]
    (CompleteExecution.descent_binding_admitted_returns host job.origin.declaration.rule
      job.origin.declaration.binding.spec)
  have snapshot := WellSorted.check_open_pattern_snapshot (GeneralPlanEnvironment.environment plan).language
    (GeneralPlanEnvironment.environment plan).free job.variant.site.focusBound job.variant.site.focusType
    job.variant.site.focus footprint inside
  have sorting := collector_from_descent% ["declarations", "free", "bound", "type", "pattern"]
    (CompleteExecution.Lowered.sorted host (GeneralPlanEnvironment.environment plan).language
      ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint)
      job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus)
  have begun := CollectionOccurrenceBatchExecution.frame_begin_returns host allocation footprint (by
    rw [allocation.request_fields.2.2.2.1, sameJob]
    exact inside)
  have atInstallation := by
    metta_lift CollectionOccurrenceInstallationExecution.checked
      ["origin", "environment", "depth", "bound", "type", "index", "rule", "spec", "prepared"] begun
  have atRuntime := occurrence_from_publication%
    ["origin", "environment", "depth", "bound", "type", "index", "rule", "spec", "prepared"] atInstallation
  have continued := by
    metta_lift checked
      ["origin", "environment", "depth", "bound", "type", "index", "rule", "spec", "prepared"] atRuntime
  obtain ⟨requestDepth, requestBound, requestType, requestSource, requestIndex,
    requestRule, requestSpec, requestAnswer⟩ := allocation.request_fields
  simp only [allocation.request_origin.1, allocation.request_origin.2, requestDepth, requestBound,
    requestType, requestIndex, requestRule, requestSpec, sameJob, sameAnswer, sameDepth] at continued
  collector_eval [admission, sorting, prepared, continued] unfolding
    [checkedLocal.1, checkedLocal.2, snapshot, CollectionOccurrenceMatcherExecution.originTerm,
      CollectionOccurrenceHandoff.Job.request,
      CollectionOccurrenceBatchExecution.originTerm, CollectionContextExecution.variantTerm,
      ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.siteTerm,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
      CompleteExecution.environmentValue, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      CompleteExecution.DescentCodec.typesTerm, CompleteExecution.DescentCodec.typeTerm, encodeOption]

/-- Collecting a published answer suffix realizes the mathematical account
in its original order. Local source admission guarantees that every valid
answer enters its own retained continuation. -/
@[metta_head "gslt:occurrence-collector:collect"]
theorem collected_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected sourcePattern)
    (work depth : Nat) (answers : List RecursiveCollectionMachine.Answer)
    (published : ∀ answer ∈ answers, Published job work answer)
    (covered : Covered names job.request.target)
    (inside : ∀ name ∈ job.variant.site.focus.freeFvarNames, name ∈ footprint)
    (admitted : RuleBinding.admittedFor job.origin.declaration.rule
      job.origin.declaration.binding.spec = true)
    (sorted : WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
      job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-collector:collect"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (CollectionOccurrenceMatcherExecution.originTerm job),
          encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request),
          encoded (encodeList RecursiveCollectionExecution.answerTerm answers)])
      host (encoded (encodeList CollectionOccurrenceBatchExecution.frameTerm
        ((collect job licensed work depth answers published).map Frame.initial))) := by
  induction answers with
  | nil => collector_eval unfolding [collect, encodeList]
  | cons answer answers ih =>
    have firstPublished := published answer List.mem_cons_self
    obtain ⟨allocation, made, _, _⟩ := allocate_published_exists job licensed work depth
      answer firstPublished admitted sorted
    have first := allocated_returns host names ordered footprint job licensed work depth
      answer firstPublished covered inside allocation made
    have rest := ih (fun next member => published next (List.mem_cons_of_mem _ member))
    collector_eval [first, rest] unfolding
      [collect, made, Option.toList_some, List.singleton_append, List.map_cons, encodeList]

/-- One native matching quantum returns the resumed lane and precisely the
fresh allocation frames. Existing continuation states are not reconstructed. -/
@[metta_head "gslt:occurrence-collector:advance-lane"]
theorem advance_lane_returns (host : Effects.State) (names : List String)
    (ordered : NameOrdered names) (footprint : List String)
    (lane : Lane plan bound expected sourcePattern) (depth : Nat)
    (stateCovered : RecursiveCollectionMachine.StateCovered names lane.state)
    (targetCovered : Covered names lane.job.request.target)
    (inside : ∀ name ∈ lane.job.variant.site.focus.freeFvarNames, name ∈ footprint)
    (admitted : RuleBinding.admittedFor lane.job.origin.declaration.rule
      lane.job.origin.declaration.binding.spec = true)
    (sorted : WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
      lane.job.variant.site.focusBound lane.job.variant.site.focusType lane.job.variant.site.focus) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-collector:advance-lane"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (CollectionOccurrenceMatcherExecution.laneTerm lane)])
      host (encoded (.application "RecursiveOccurrenceLaneAllocations"
        [CollectionOccurrenceMatcherExecution.laneTerm (lane.resume 1),
          encodeList CollectionOccurrenceBatchExecution.frameTerm
            ((lane.allocations depth).map Frame.initial)])) := by
  have advanced := by
    metta_lift checked ["names", "lane"]
      (occurrence_from_matcher% ["names", "lane"]
        (CollectionOccurrenceMatcherExecution.advance_returns host names ordered lane stateCovered))
  have collected := collected_returns host names ordered footprint lane.job lane.licensed
    (lane.spent + 1) depth lane.fresh
    (fun answer member => (lane.resume 1).published answer (List.mem_of_mem_drop member))
    targetCovered inside admitted sorted
  collector_eval [advanced, collected] unfolding
    [CollectionOccurrenceMatcherExecution.laneTerm,
      CollectionOccurrenceMatcherExecution.advancedTerm, Lane.allocations]

/-- Finite codec coverage and the same local checks used by allocation.
These are representation preconditions, not successor-coverage assumptions. -/
structure LaneReady (names footprint : List String)
    (lane : Lane plan bound expected sourcePattern) : Prop where
  state : RecursiveCollectionMachine.StateCovered names lane.state
  target : Covered names lane.job.request.target
  free : ∀ name ∈ lane.job.variant.site.focus.freeFvarNames, name ∈ footprint
  admitted : RuleBinding.admittedFor lane.job.origin.declaration.rule
    lane.job.origin.declaration.binding.spec = true
  sorted : WellSorted.OpenPatternWellSorted
    (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
    lane.job.variant.site.focusBound lane.job.variant.site.focusType lane.job.variant.site.focus

private theorem append_returns {α : Type} (encoder : α → Term) (host : Effects.State)
    (left right : List α) :
    PureReturns library.runtime [] host
      (apply "gslt:automata:append"
        [encoded (encodeList encoder left), encoded (encodeList encoder right)])
      host (encoded (encodeList encoder (left ++ right))) := by
  have atBase := by
    metta_lift CollectionMatcherBackendExecution.collectionBase_checked ["left", "right"]
      (CompleteExecution.complete_append_returns encoder host left right)
  have atBackend := by metta_lift CollectionMatcherBackendExecution.checked ["left", "right"] atBase
  have atContinuation := by
    metta_lift RecursiveCollectionContinuationExecution.checked ["left", "right"] atBackend
  have atBatch := by metta_lift CollectionOccurrenceBatchExecution.checked ["left", "right"] atContinuation
  have atInstallation := by
    metta_lift CollectionOccurrenceInstallationExecution.checked ["left", "right"] atBatch
  have atRuntime := occurrence_from_publication% ["left", "right"] atInstallation
  metta_lift checked ["left", "right"] atRuntime

def advancedLanesTerm (depth : Nat) (lanes : List (Lane plan bound expected sourcePattern)) : Term :=
  .application "RecursiveOccurrenceLanesAllocations"
    [encodeList CollectionOccurrenceMatcherExecution.laneTerm (lanes.map (Lane.resume 1)),
      encodeList CollectionOccurrenceBatchExecution.frameTerm
        ((lanes.flatMap (Lane.allocations depth)).map Frame.initial)]

/-- The native list traversal preserves the authored lane order and the
complete fresh allocation account before installation into retained work. -/
@[metta_head "gslt:occurrence-collector:advance-lanes"]
theorem advance_lanes_returns (host : Effects.State) (names : List String)
    (ordered : NameOrdered names) (footprint : List String) (depth : Nat) :
    ∀ lanes : List (Lane plan bound expected sourcePattern),
      (∀ lane ∈ lanes, LaneReady names footprint lane) →
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-collector:advance-lanes"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (encodeList CollectionOccurrenceMatcherExecution.laneTerm lanes)])
      host (encoded (advancedLanesTerm depth lanes))
  | [], _ => by collector_eval unfolding [advancedLanesTerm, encodeList]
  | lane :: lanes, ready => by
    have firstReady := ready lane List.mem_cons_self
    have first := advance_lane_returns host names ordered footprint lane depth
      firstReady.state firstReady.target firstReady.free firstReady.admitted firstReady.sorted
    have rest := advance_lanes_returns host names ordered footprint depth lanes
      (fun next member => ready next (List.mem_cons_of_mem _ member))
    have joined := append_returns CollectionOccurrenceBatchExecution.frameTerm host
      ((lane.allocations depth).map Frame.initial)
      ((lanes.flatMap (Lane.allocations depth)).map Frame.initial)
    collector_eval [first, rest, joined] unfolding
      [advancedLanesTerm, List.flatMap_cons, List.map_append, List.map_cons, encodeList]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution
