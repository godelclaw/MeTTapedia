import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionRequestExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionPostMatch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchRunner
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Canonical
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.EquationLanes
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire
import Mettapedia.OSLF.MeTTaIL.CollectionRootSearch
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesFootprint

/-!
# Root collections in the shared native runner

The native controller retains the existing plan matcher, then starts one
shared continuation for each raw allocation. The generic runner and explorer
keep their existing search interface. These execution comparisons do not
grant admission or equational coherence by themselves.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RootCollection

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionMatcherBackend
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit

variable {plan : GeneralExecutionAdmission.Plan} {profile : CollectionRootSearch.Profile plan}
    {expected : TypeExpr}

def matchTerm (matched : Retained.Match) : Term :=
  .application "CollectionPlanMatch"
    [.natural matched.ordinal, ScopedCollectionExecution.requestTerm matched.request,
      ScopedCollectionExecution.receiptTerm matched.receipt]

def receiptTerm (receipt : CollectionRootSearch.Receipt) : Term :=
  .application "CollectionRootReceipt"
    [.natural receipt.matched.ordinal, ScopedCollectionExecution.requestTerm receipt.matched.request,
      ScopedCollectionExecution.receiptTerm receipt.matched.receipt,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm receipt.completed,
      PremiseOperationsExecution.GeneralExecution.eventsTerm receipt.history,
      InferenceCettaWire.encodePattern receipt.target]

def runTerm (run : CollectionRootSearch.Run (profile := profile) expected) : Term :=
  match run.phase with
  | .rejected => .application "CollectionRootRejected" [InferenceCettaWire.encodePattern run.source]
  | .matching _ matcher => .application "CollectionRootMatching"
      [InferenceCettaWire.encodePattern run.source, .natural matcher.spent,
        CollectionPlanExecution.planStateTerm matcher.state]
  | .continuing _ current _ => .application "CollectionRootContinuing"
      [InferenceCettaWire.encodePattern run.source, CollectionContinuationExecution.stateTerm current]

def backendTerm (names : List String) : Term :=
  .application "CollectionRootSearch" [encodeList Term.string names]

inductive PhaseReady (footprint : List String) {source : Pattern} :
    CollectionRootSearch.Phase (profile := profile) expected source → Prop where
  | rejected : PhaseReady footprint .rejected
  | matching (typed) (matcher) : PhaseReady footprint (.matching typed matcher)
  | continuing (typed) (current) (balanced)
      (covered : CollectionContinuationExecution.StateReady footprint current) :
      PhaseReady footprint (.continuing typed current balanced)

def Ready (footprint : List String)
    (run : CollectionRootSearch.Run (profile := profile) expected) : Prop :=
  (∀ name ∈ run.source.freeFvarNames, name ∈ footprint) ∧
    CollectionRequestExecution.ArrangedRoot run.source ∧ PhaseReady footprint run.phase

theorem begin_ready (footprint : List String) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint)
    (arranged : CollectionRequestExecution.ArrangedRoot source) :
    Ready footprint (CollectionRootSearch.begin (profile := profile) expected source) := by
  unfold CollectionRootSearch.begin
  split
  · exact ⟨inside, arranged, .matching _ _⟩
  · exact ⟨inside, arranged, .rejected⟩

theorem tick_ready (footprint : List String)
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint)
    (run : CollectionRootSearch.Run (profile := profile) expected) (ready : Ready footprint run) :
    Ready footprint (CollectionRootSearch.tick expected run) := by
  obtain ⟨source, phase⟩ := run
  obtain ⟨inside, arranged, holds⟩ := ready
  cases phase with
  | rejected => exact ⟨inside, arranged, .rejected⟩
  | matching typed matcher =>
    simp only [CollectionRootSearch.tick]
    split
    · refine ⟨inside, arranged, .continuing _ _ _ ?_⟩
      intro frame member
      obtain ⟨matched, _, rfl⟩ := List.mem_map.mp member
      exact CollectionContinuationExecution.initial_ready matched.val matched.property typed _ footprint inside
    · exact ⟨inside, arranged, .matching _ _⟩
  | continuing typed current balanced =>
    have covered : CollectionContinuationExecution.StateReady footprint current := by
      cases holds
      assumption
    exact ⟨inside, arranged, .continuing _ _ _
      (CollectionContinuationExecution.round_ready footprint profile.finiteProvider provider current covered)⟩

theorem rounds_ready (footprint : List String)
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (work : Nat)
    (run : CollectionRootSearch.Run (profile := profile) expected) (ready : Ready footprint run) :
    Ready footprint (CollectionRootSearch.rounds expected work run) := by
  induction work generalizing run with
  | zero => exact ready
  | succ work ih => exact ih _ (tick_ready footprint provider run ready)

syntax "root_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| root_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (metta_call runner_checked
       metta_eval [$facts,*] with runner_checked unfolding [
         Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
         Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
         Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
         pattern_symbol_unmatched, $extra,*]))

@[metta_head "gslt:collection-root:raw-tag"]
theorem raw_tag_returns (state : Effects.State) (index : Nat)
    (query : ScopedCollectionMachine.Request) : ∀ receipts : List ScopedCollectionMachine.Receipt,
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-root:raw-tag"
        [number index, encoded (ScopedCollectionExecution.requestTerm query),
          encoded (encodeList ScopedCollectionExecution.receiptTerm receipts)])
      state (encoded (encodeList matchTerm
        (receipts.map fun receipt => Retained.Match.mk index query receipt)))
  | [] => by root_eval
  | receipt :: receipts => by
    have later := raw_tag_returns state index query receipts
    root_eval [later] unfolding [matchTerm]

@[metta_head "gslt:collection-root:raw-publication"]
theorem raw_publication_returns (state : Effects.State) : ∀ jobs : CollectionPlanMachine.State,
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-root:raw-publication" [encoded (CollectionPlanExecution.planStateTerm jobs)])
      state (encoded (encodeList matchTerm (CollectionRootSearch.rawPublication jobs)))
  | [] => by root_eval unfolding [CollectionPlanExecution.planStateTerm, CollectionRootSearch.rawPublication]
  | job :: jobs => by
    have atSource := ScopedCollectionExecution.publication_returns state job.state
    have atLogged := by
      metta_lift CollectionLoggedSearchExecution.checked ["jobs"] atSource
    have published := collection_runner_lifted% ["jobs"] atLogged
    have tagged := raw_tag_returns state job.ordinal job.request
      (ScopedCollectionMachine.publication job.state)
    have later := raw_publication_returns state jobs
    have joined := complete_runner_lifted% ["left", "right"]
      (complete_append_returns matchTerm state
        ((ScopedCollectionMachine.publication job.state).map fun receipt =>
          Retained.Match.mk job.ordinal job.request receipt)
        (CollectionRootSearch.rawPublication jobs))
    root_eval [published, tagged, later, joined] unfolding [CollectionPlanExecution.planStateTerm,
      CollectionPlanExecution.jobTerm, CollectionRootSearch.rawPublication, List.flatMap_cons]

@[metta_head "gslt:collection-root:frames-begin"]
theorem frames_begin_returns (state : Effects.State) (footprint : List String)
    {source : Pattern}
    (typed : WellSorted.OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    ∀ matchedOrigins : List (Retained.CheckedMatch plan profile.collection source),
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-root:frames-begin"
        [environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          encoded (InferenceCettaWire.AuthoredRule.typeTerm expected),
          encoded (encodeList (fun matched => matchTerm matched.val) matchedOrigins)])
      state (encoded (encodeList CollectionContinuationExecution.frameTerm
        (Retained.State.initial matchedOrigins typed CollectionRootSearch.depth).frames))
  | [] => by root_eval unfolding [Retained.State.initial, Retained.State.begin]
  | matched :: matchedOrigins => by
    have targetAtBase := CollectionMatcherBackendExecution.ordinary_target_returns state
      matched.val.request matched.val.receipt
    rw [CollectionMatcherBackendExecution.rawOrdinaryTarget_eq_of_valid
      matched.property.fixed matched.property.valid] at targetAtBase
    have presented := postmatch_lifted% ["kind", "values", "residual"] targetAtBase
    have size := complete_runner_lifted% ["pattern"]
      (nodes_returns state (CollectionMatcherCompatibility.ordinaryTarget matched.val.request matched.val.receipt))
    have begun := postmatch_lifted% ["environment", "depth", "type", "index", "query", "receipt"]
      (CollectionContinuationExecution.frame_begin_returns state footprint matched.val matched.property
        typed (CollectionRootSearch.depth matched.val) inside)
    have later := frames_begin_returns state footprint typed inside matchedOrigins
    root_eval [presented, size, begun, later] unfolding [matchTerm, Retained.State.initial, Retained.State.begin,
      CollectionRootSearch.depth, ScopedCollectionExecution.requestTerm, ScopedCollectionMachine.Request.machine,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
      ScopedCollectionExecution.receiptTerm, CollectionSelectionExecution.allocationTerm,
      RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
      InferenceCettaWire.encodePattern, InferenceCettaWire.encodeCollectionType,
      InferenceCettaWire.encodeRest, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList]

@[metta_head "gslt:collection-root:begin"]
theorem begin_returns (state : Effects.State) (footprint : List String)
    (declared : Complete.Footprint.Declared plan footprint)
    (source : Pattern) (arranged : CollectionRequestExecution.ArrangedRoot source) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-root:begin"
        [planValue plan (plan.snapshot.free.entriesOn footprint) [] expected, patternValue source])
      state (encoded (runTerm (CollectionRootSearch.begin (profile := profile) expected source))) := by
  have checkedAtSource := complete_sorted_returns state (GeneralPlanEnvironment.environment plan).language
    (plan.snapshot.free.entriesOn footprint) [] expected source
  have sorted := complete_runner_lifted% ["declarations", "free", "bound", "type", "pattern"] checkedAtSource
  rw [Complete.Footprint.full_table declared] at sorted
  have requestedAtSource := CollectionRequestExecution.requests_for_source_admitted_returns state plan
    profile.collection (plan.snapshot.free.entriesOn footprint) [] expected source arranged
  have requested := collection_runner_lifted% ["plan", "source"] requestedAtSource
  have begunAtSource := CollectionPlanExecution.start_returns state
    (CollectionRootSearch.requests plan profile source) (fun entry member =>
      CollectionExecutionAdmission.requestForSource?_fixed
        (CollectionExecutionAdmission.requestsForSource_selected member))
  have begunAtLogged := by
    metta_lift CollectionLoggedSearchExecution.checked ["requests"] begunAtSource
  have begun := collection_runner_lifted% ["requests"] begunAtLogged
  cases checked : WellSorted.checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source with
  | false =>
    have rejected : CollectionRootSearch.begin (profile := profile) expected source =
        ⟨source, .rejected⟩ := by simp [CollectionRootSearch.begin, checked]
    rw [rejected]
    change WellSorted.checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free [] expected source = false at checked
    rw [checked] at sorted
    root_eval [sorted] unfolding [planValue, CompletePlanWire.planTerm,
      PremiseOperationsExecution.GeneralExecution.environmentTerm, runTerm, Effects.boolean, encodeList]
  | true =>
    rw [CollectionRootSearch.begin_typed expected source
      (WellSorted.checkOpenPatternWellSorted_sound checked)]
    change WellSorted.checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free [] expected source = true at checked
    rw [checked] at sorted
    root_eval [sorted, requested, begun] unfolding [planValue, CompletePlanWire.planTerm,
      PremiseOperationsExecution.GeneralExecution.environmentTerm, runTerm,
      CollectionRootSearch.Matching.begin, CollectionPlanExecution.planStateTerm,
      Effects.boolean, encodeList]

private theorem matching_encoding {source : Pattern}
    (matching : CollectionRootSearch.Matching plan profile source) :
    encodeList (fun matched => matchTerm matched.val) matching.matches =
      encodeList matchTerm (CollectionRootSearch.rawPublication matching.state) := by
  have erased : matching.matches.map Subtype.val = CollectionRootSearch.rawPublication matching.state := by
    simp only [CollectionRootSearch.Matching.matches, List.map_map, Function.comp_def]
    exact List.attach_map_subtype_val _
  calc
    _ = encodeList matchTerm (matching.matches.map Subtype.val) :=
      (encodeList_map matchTerm Subtype.val matching.matches).symm
    _ = _ := congrArg (encodeList matchTerm) erased

@[metta_head "gslt:collection-root:tick"]
theorem tick_returns (state : Effects.State) (footprint : List String)
    (scope : Complete.Footprint.Scope plan footprint)
    (run : CollectionRootSearch.Run (profile := profile) expected) (ready : Ready footprint run) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-root:tick"
        [planValue plan (plan.snapshot.free.entriesOn footprint) [] expected, encoded (runTerm run)])
      state (encoded (runTerm (CollectionRootSearch.tick expected run))) := by
  obtain ⟨source, phase⟩ := run
  obtain ⟨inside, arranged, ready⟩ := ready
  cases phase with
  | rejected =>
    root_eval unfolding [runTerm, CollectionRootSearch.tick, planValue, CompletePlanWire.planTerm]
  | matching typed matcher =>
    have completeAtSource := CollectionPlanExecution.complete_returns state matcher.state
    have completeAtLogged := by
      metta_lift CollectionLoggedSearchExecution.checked ["jobs"] completeAtSource
    have complete := collection_runner_lifted% ["jobs"] completeAtLogged
    cases done : CollectionPlanMachine.complete matcher.state with
    | true =>
      simp only [CollectionRootSearch.tick, done, ↓reduceIte]
      have published := raw_publication_returns state matcher.state
      have frames := frames_begin_returns state footprint typed inside matcher.matches
      rw [matching_encoding] at frames
      rw [show (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free from rfl] at frames
      have begun := postmatch_lifted% ["frames"]
        (CollectionContinuationExecution.state_begin_returns state
          (Retained.State.initial matcher.matches typed CollectionRootSearch.depth).frames)
      root_eval [complete, published, frames, begun] unfolding [planValue, CompletePlanWire.planTerm,
        runTerm, CollectionRootSearch.tick, done, CollectionSelectionExecution.booleanTerm,
        Retained.State.initial]
    | false =>
      simp only [CollectionRootSearch.tick, done, Bool.false_eq_true, ↓reduceIte]
      have resumedAtSource := CollectionPlanExecution.resume_returns state 1 matcher.state
      have resumedAtLogged := by
        metta_lift CollectionLoggedSearchExecution.checked ["fuel", "jobs"] resumedAtSource
      have resumed := collection_runner_lifted% ["fuel", "jobs"] resumedAtLogged
      root_eval [complete, resumed] unfolding [planValue, CompletePlanWire.planTerm, runTerm,
        CollectionRootSearch.tick, CollectionRootSearch.Matching.resume, done,
        CollectionSelectionExecution.booleanTerm]
  | continuing typed current balanced =>
    have covered : CollectionContinuationExecution.StateReady footprint current := by
      cases ready
      assumption
    have advanced := postmatch_lifted% ["environment", "work", "state"]
      (CollectionContinuationExecution.state_run_returns state footprint profile.finiteProvider
        scope.provider 1 current covered)
    rw [show (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free from rfl] at advanced
    root_eval [advanced] unfolding [planValue, CompletePlanWire.planTerm, runTerm,
      CollectionRootSearch.tick]

@[metta_head "gslt:collection-root:rounds"]
theorem rounds_returns (state : Effects.State) (footprint : List String)
    (scope : Complete.Footprint.Scope plan footprint) :
    ∀ (work : Nat) (run : CollectionRootSearch.Run (profile := profile) expected), Ready footprint run →
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-root:rounds"
        [planValue plan (plan.snapshot.free.entriesOn footprint) [] expected,
          number work, encoded (runTerm run)])
      state (encoded (runTerm (CollectionRootSearch.rounds expected work run)))
  | 0, run, _ => by root_eval unfolding [CollectionRootSearch.rounds]
  | work + 1, run, ready => by
    have ticked := tick_returns state footprint scope run ready
    have later := rounds_returns state footprint scope work (CollectionRootSearch.tick expected run)
      (tick_ready footprint scope.provider run ready)
    root_eval [ticked, later] unfolding [CollectionRootSearch.rounds]

@[metta_head "gslt:collection-root:run"]
theorem run_returns (state : Effects.State) (footprint : List String)
    (scope : Complete.Footprint.Scope plan footprint)
    (source : Pattern) (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint)
    (arranged : CollectionRequestExecution.ArrangedRoot source) (work : Nat) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-root:run"
        [planValue plan (plan.snapshot.free.entriesOn footprint) [] expected, patternValue source, number work])
      state (encoded (runTerm ((CollectionRootSearch.search (profile := profile) expected).run source work))) := by
  have begun := begin_returns (profile := profile) (expected := expected)
    state footprint scope.declared source arranged
  have continued := rounds_returns state footprint scope work
    (CollectionRootSearch.begin (profile := profile) expected source) (begin_ready footprint source inside arranged)
  root_eval [begun, continued] unfolding [CollectionRootSearch.search]

@[metta_head "gslt:collection-root:observations"]
theorem observations_returns (state : Effects.State) : ∀ log : List Retained.Publication,
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-root:observations"
        [encoded (encodeList CollectionContinuationExecution.publicationTerm log)])
      state (encoded (encodeList receiptTerm (log.map CollectionRootSearch.observe)))
  | [] => by root_eval
  | publication :: log => by
    have later := observations_returns state log
    root_eval [later] unfolding [CollectionContinuationExecution.publicationTerm,
      firingTerm, receiptTerm, CollectionRootSearch.observe]

@[metta_head "gslt:collection-root:publication"]
theorem publication_returns (state : Effects.State)
    (run : CollectionRootSearch.Run (profile := profile) expected) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-root:publication" [encoded (runTerm run)])
      state (encoded (encodeList receiptTerm (CollectionRootSearch.publication expected run))) := by
  obtain ⟨source, phase⟩ := run
  cases phase with
  | rejected => root_eval unfolding [runTerm, CollectionRootSearch.publication]
  | matching => root_eval unfolding [runTerm, CollectionRootSearch.publication]
  | continuing typed current balanced =>
    have observed := observations_returns state current.log
    root_eval [observed] unfolding [runTerm, CollectionRootSearch.publication,
      CollectionContinuationExecution.stateTerm]

@[metta_head "gslt:collection-root:status"]
theorem status_returns (state : Effects.State)
    (run : CollectionRootSearch.Run (profile := profile) expected) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-root:status" [encoded (runTerm run)])
      state (SearchRunner.statusAtom (CollectionRootSearch.status expected run)) := by
  obtain ⟨source, phase⟩ := run
  cases phase with
  | rejected => root_eval unfolding [runTerm, CollectionRootSearch.status, SearchRunner.statusAtom]
  | matching => root_eval unfolding [runTerm, CollectionRootSearch.status, SearchRunner.statusAtom]
  | continuing typed current balanced =>
    have settled := postmatch_lifted% ["state"]
      (CollectionContinuationExecution.state_settled_returns state current)
    cases done : current.complete <;>
      root_eval [settled] unfolding [runTerm, CollectionRootSearch.status, done,
        CollectionSelectionExecution.booleanTerm, SearchRunner.statusAtom]

@[metta_head "gslt:search:run"]
theorem search_run_returns (state : Effects.State) (names : List String) (footprint : List String)
    (scope : Complete.Footprint.Scope plan footprint)
    (source : Pattern) (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint)
    (arranged : CollectionRequestExecution.ArrangedRoot source) (work : Nat) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:run"
        [encoded (backendTerm names), planValue plan (plan.snapshot.free.entriesOn footprint) [] expected,
          patternValue source, number work])
      state (encoded (runTerm ((CollectionRootSearch.search (profile := profile) expected).run source work))) := by
  have native := run_returns (profile := profile) (expected := expected)
    state footprint scope source inside arranged work
  root_eval [native] unfolding [backendTerm]

@[metta_head "gslt:search:resume"]
theorem search_resume_returns (state : Effects.State) (names : List String) (footprint : List String)
    (scope : Complete.Footprint.Scope plan footprint)
    (run : CollectionRootSearch.Run (profile := profile) expected) (ready : Ready footprint run) (work : Nat) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:resume"
        [encoded (backendTerm names), planValue plan (plan.snapshot.free.entriesOn footprint) [] expected,
          encoded (runTerm run), number work])
      state (encoded (runTerm ((CollectionRootSearch.search (profile := profile) expected).resume run work))) := by
  have native := rounds_returns state footprint scope work run ready
  root_eval [native] unfolding [backendTerm, CollectionRootSearch.search]

@[metta_head "gslt:search:publication"]
theorem search_publication_returns (state : Effects.State) (names : List String)
    (run : CollectionRootSearch.Run (profile := profile) expected) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:publication" [encoded (backendTerm names), encoded (runTerm run)])
      state (encoded (encodeList receiptTerm (CollectionRootSearch.publication expected run))) := by
  have native := publication_returns state run
  root_eval [native] unfolding [backendTerm]

@[metta_head "gslt:search:status"]
theorem search_status_returns (state : Effects.State) (names : List String) (planData : Atom)
    (run : CollectionRootSearch.Run (profile := profile) expected) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:status" [encoded (backendTerm names), planData, encoded (runTerm run)])
      state (SearchRunner.statusAtom (CollectionRootSearch.status expected run)) := by
  have native := status_returns state run
  root_eval [native] unfolding [backendTerm]

@[metta_head "gslt:search:target"]
theorem search_target_returns (state : Effects.State) (names : List String)
    (named : StandardWire.TableFor plan names) (standard : Atom) (receipt : CollectionRootSearch.Receipt)
    (checked : Complete.Classes.Checked plan [] expected receipt.target) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:target" [encoded (backendTerm names), standard, encoded (receiptTerm receipt)])
      state (patternValue (CanonicalBags.canon receipt.target)) := by
  have native := canonical_runner_lifted% ["names", "pattern"]
    (canon_returns state named.ordered receipt.target (named.covered checked))
  root_eval [native] unfolding [backendTerm, receiptTerm]

theorem publication_checked (run : CollectionRootSearch.Run (profile := profile) expected)
    {receipt : CollectionRootSearch.Receipt}
    (published : receipt ∈ CollectionRootSearch.publication expected run) :
    Complete.Classes.Checked plan [] expected receipt.target := by
  obtain ⟨_, trace, held⟩ := CollectionRootSearch.publication_sound expected run published
  apply WellSorted.checkOpenPatternWellSorted_complete
  cases held with
  | fire _ _ _ _ _ _ _ _ sorted => exact sorted

/-- The root strategy fills the same five-operation realization consumed by
the existing generic native runner and explorer. Source-law coverage remains
separate from these representation and readiness obligations. -/
def realization (names : List String) (named : StandardWire.TableFor plan names)
    (footprint : List String) (scope : Complete.Footprint.Scope plan footprint) :
    SearchRunner.Realization (CollectionRootSearch.search (profile := profile) expected) where
  lawful := CollectionRootSearch.search_lawful expected
  stable := CollectionRootSearch.search_stable expected
  backend := encoded (backendTerm names)
  plan := planValue plan (plan.snapshot.free.entriesOn footprint) [] expected
  standard := encoded (.application "Canonical" [.symbol "LNil", .symbol "LNil", encodeList Term.string names])
  runTerm := runTerm
  receiptTerm := receiptTerm
  SourceReady source := (∀ name ∈ source.freeFvarNames, name ∈ footprint) ∧
    CollectionRequestExecution.ArrangedRoot source
  RunReady := Ready footprint
  ReceiptReady receipt := Complete.Classes.Checked plan [] expected receipt.target
  run_ready source ready work := rounds_ready footprint scope.provider work _
    (begin_ready footprint source ready.1 ready.2)
  resume_ready run ready work := rounds_ready footprint scope.provider work run ready
  publication_ready run _ receipt member := publication_checked run member
  target_ready receipt checked := by
    constructor
    · intro name member
      exact Complete.Footprint.sorted_within scope.declared checked name
        ((CanonicalBags.canon_freeFvarNames receipt.target name).mp member)
    · exact CollectionRequestExecution.arrangedRoot_canon _
  run_returns state source ready work := search_run_returns state names footprint scope source ready.1 ready.2 work
  resume_returns state run ready work := search_resume_returns state names footprint scope run ready work
  publication_returns state run := search_publication_returns state names run
  status_returns state run _ := search_status_returns state names _ run
  target_returns state receipt checked := search_target_returns state names named _ receipt checked

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RootCollection
