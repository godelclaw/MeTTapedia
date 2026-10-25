import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPlanExecution
import Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearch

/-!
# Native append-only collection search

The retained MeTTa state carries every collection lane, its consumed cursor,
and one chronological firing log. This module proves the state operations
against `CollectionLoggedSearch`; choosing the source-derived request list and
connecting the backend to the generic runner remain separate joins.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionLoggedSearchExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionLoggedSearch
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open ScopedCollectionExecution
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_logged_search.metta"
    sha256 "5a7619553f9217e7a984cf38845db3aa270bdc8674539235c7501b2201a97362"

def library : BridgeKit.Library :=
  ⟨ScopedCollectionExecution.library.runtime, source.program,
    ["gslt:collection-search:"]⟩

set_option maxRecDepth 100000 in
theorem checked : library.check = true := by decide +kernel

def loggedLaneTerm (lane : Lane) : Term :=
  .application "CollectionLoggedLane"
    [.natural lane.ordinal, requestTerm lane.request, ScopedCollectionExecution.stateTerm lane.state,
      .natural lane.spent, .natural lane.consumed]

def loggedStateTerm (search : CollectionLoggedSearch.State) : Term :=
  .application "CollectionLoggedState"
    [encodeList loggedLaneTerm search.lanes,
      encodeList CollectionPlanExecution.planFiringTerm search.log]

def loggedRunTerm (run : Run) : Term :=
  .application "CollectionLoggedRun"
    [InferenceCettaWire.encodePattern run.source, loggedStateTerm run.state]

def advancedLaneTerm (advanced : Lane × List CollectionPlanMachine.Firing) : Term :=
  .application "CollectionLoggedAdvanced"
    [loggedLaneTerm advanced.1,
      encodeList CollectionPlanExecution.planFiringTerm advanced.2]

def advancedLanesTerm
    (advanced : List Lane × List CollectionPlanMachine.Firing) : Term :=
  .application "CollectionLoggedAdvanced"
    [encodeList loggedLaneTerm advanced.1,
      encodeList CollectionPlanExecution.planFiringTerm advanced.2]

/-- Selection of the logged-state wire binds its two fields and retains the
caller's binding. This isolates the generic selector computation from the
particular lane and receipt encoders. -/
theorem select_logged_state (lanes log branch : Atom) :
    SpaceSemantics.selectCase
      [("state", .expression [.symbol "CollectionLoggedState", lanes, log])]
      (.expression [.symbol "CollectionLoggedState", lanes, log])
      [(.expression [.symbol "CollectionLoggedState", .var "lanes", .var "log"], branch)] =
    some ([ ("log", log), ("lanes", lanes),
      ("state", .expression [.symbol "CollectionLoggedState", lanes, log]) ], branch) := by
  simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem select_logged_advanced_round
    (nextLanes fresh log lanes branch : Atom) :
    let advanced := .expression [.symbol "CollectionLoggedAdvanced", nextLanes, fresh]
    SpaceSemantics.selectCase
      [("advanced", advanced), ("log", log), ("lanes", lanes)] advanced
      [(.expression [.symbol "CollectionLoggedAdvanced", .var "next-lanes", .var "fresh"], branch)] =
    some ([ ("fresh", fresh), ("next-lanes", nextLanes),
      ("advanced", advanced), ("log", log), ("lanes", lanes) ], branch) := by
  simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem select_logged_advanced_resume
    (nextLanes fresh log lanes fuel branch : Atom) :
    let advanced := .expression [.symbol "CollectionLoggedAdvanced", nextLanes, fresh]
    SpaceSemantics.selectCase
      [("advanced", advanced), ("log", log), ("lanes", lanes), ("fuel", fuel)] advanced
      [(.expression [.symbol "CollectionLoggedAdvanced", .var "next-lanes", .var "fresh"], branch)] =
    some ([ ("fresh", fresh), ("next-lanes", nextLanes),
      ("advanced", advanced), ("log", log), ("lanes", lanes), ("fuel", fuel) ], branch) := by
  simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

syntax "collection_search_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| collection_search_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (metta_call checked
       try simp only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil,
         Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil.applySubstList_nil,
         Library.bind, List.zip, List.zipWith, List.reverse_cons, List.reverse_nil,
         List.nil_append, List.cons_append]
       metta_eval [$facts,*] with checked
         unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
           Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
           SpaceSemantics.selectCase, SpaceSemantics.matchValue,
           Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
           Mettapedia.Languages.ProcessCalculi.MORK.matchAtom.matchAtomList,
           select_logged_state, select_logged_advanced_round,
           select_logged_advanced_resume,
           loggedLaneTerm, loggedStateTerm, loggedRunTerm, advancedLaneTerm,
           advancedLanesTerm, encodeList, $extra,*]))

@[metta_head "gslt:collection-search:drop"]
theorem drop_returns {α : Type} (element : α → Term) (state : Effects.State) :
    ∀ (count : Nat) (items : List α),
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:drop"
        [number count, encoded (encodeList element items)])
      state (encoded (encodeList element (items.drop count)))
  | 0, items => by
      collection_search_eval unfolding [List.drop]
  | count + 1, [] => by
      collection_search_eval unfolding [List.drop]
  | count + 1, item :: rest => by
      have later := drop_returns element state count rest
      collection_search_eval [later] unfolding [List.drop]

@[metta_head "gslt:collection-search:lane-begin"]
theorem lane_begin_returns (state : Effects.State)
    (entry : Nat × ScopedCollectionMachine.Request)
    (fixed : CanonicalBags.arrange entry.2.kind entry.2.targets = entry.2.targets) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:lane-begin"
        [encoded (CollectionPlanExecution.requestEntryTerm entry)])
      state (encoded (loggedLaneTerm (Lane.begin entry))) := by
  have startedAtBase := ScopedCollectionExecution.start_returns state entry.2 fixed
  have started := by
    metta_lift checked ["request"] startedAtBase
  collection_search_eval [started]
    unfolding [Lane.begin, CollectionPlanExecution.requestEntryTerm]

@[metta_head "gslt:collection-search:lanes-begin"]
theorem lanes_begin_returns (state : Effects.State) :
    ∀ requests : List (Nat × ScopedCollectionMachine.Request),
    (∀ entry ∈ requests,
      CanonicalBags.arrange entry.2.kind entry.2.targets = entry.2.targets) →
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:lanes-begin"
        [encoded (encodeList CollectionPlanExecution.requestEntryTerm requests)])
      state (encoded (encodeList loggedLaneTerm (requests.map Lane.begin)))
  | [], _ => by
      collection_search_eval
  | entry :: requests, fixed => by
      have first := lane_begin_returns state entry (fixed entry (by simp))
      have later := lanes_begin_returns state requests fun request member =>
        fixed request (by simp [member])
      collection_search_eval [first, later] unfolding [List.map_cons]

@[metta_head "gslt:collection-search:begin"]
theorem begin_returns (state : Effects.State)
    (requests : List (Nat × ScopedCollectionMachine.Request))
    (fixed : ∀ entry ∈ requests,
      CanonicalBags.arrange entry.2.kind entry.2.targets = entry.2.targets) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:begin"
        [encoded (encodeList CollectionPlanExecution.requestEntryTerm requests)])
      state (encoded (loggedStateTerm (CollectionLoggedSearch.begin requests))) := by
  have lanes := lanes_begin_returns state requests fixed
  collection_search_eval [lanes] unfolding [CollectionLoggedSearch.begin]

def cursorTerm (paid remaining : Nat) : Term :=
  .application "CollectionLoggedCursor" [.natural paid, .natural remaining]

def advancedJobsTerm
    (advanced : ScopedCollectionMachine.State × List ScopedCollectionMachine.FiringReceipt) : Term :=
  .application "CollectionLoggedJobsAdvanced"
    [ScopedCollectionExecution.stateTerm advanced.1,
      encodeList ScopedCollectionExecution.firingTerm advanced.2]

@[metta_head "gslt:collection-search:split-cursor"]
theorem split_cursor_returns {α : Type} (element : α → Term) (state : Effects.State) :
    ∀ (count : Nat) (items : List α),
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:split-cursor"
        [number count, encoded (encodeList element items)])
      state (encoded (cursorTerm (min count items.length) (count - items.length)))
  | 0, items => by
      collection_search_eval unfolding [cursorTerm]
  | count + 1, [] => by
      collection_search_eval unfolding [cursorTerm]
  | count + 1, item :: rest => by
      have later := split_cursor_returns element state count rest
      simp only [List.length_cons, Nat.add_min_add_right, Nat.succ_sub_succ_eq_sub]
      collection_search_eval [later] unfolding [cursorTerm]
      all_goals
        try simp only [← Nat.cast_min (α := Int)]
        metta_eval [later] with checked unfolding [cursorTerm, encodeList]

@[metta_head "gslt:collection-search:advance-jobs"]
theorem advance_jobs_returns (state : Effects.State)
    (request : ScopedCollectionMachine.Request) :
    ∀ (consumed : Nat) (jobs : ScopedCollectionMachine.State),
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:advance-jobs"
        [encoded (requestTerm request), number consumed, encoded (ScopedCollectionExecution.stateTerm jobs)])
      state (encoded (advancedJobsTerm (advanceJobs request consumed jobs)))
  | consumed, [] => by
      collection_search_eval unfolding [advanceJobs, advancedJobsTerm,
        ScopedCollectionExecution.stateTerm]
  | consumed, job :: jobs => by
      let next := { job with state := GeneralScopedMatchMachine.run request.machine 1 job.state }
      let previous := ScopedCollectionMachine.firings request [job]
      let published := ScopedCollectionMachine.firings request [next]
      have resumedBase := ScopedCollectionExecution.resume_returns state request 1 [job]
      have resumed := by metta_lift checked ["request", "fuel", "jobs"] resumedBase
      have oldBase := ScopedCollectionExecution.publication_returns state [job]
      have old := by metta_lift checked ["jobs"] oldBase
      have previousBase := ScopedCollectionFiringExecution.firings_returns state request
        (ScopedCollectionMachine.publication [job])
      have before := by metta_lift checked ["request", "receipts"] previousBase
      have split := split_cursor_returns ScopedCollectionExecution.firingTerm state consumed previous
      have newBase := ScopedCollectionExecution.publication_returns state [next]
      have new := by metta_lift checked ["jobs"] newBase
      have publishedBase := ScopedCollectionFiringExecution.firings_returns state request
        (ScopedCollectionMachine.publication [next])
      have after := by metta_lift checked ["request", "receipts"] publishedBase
      have fresh := drop_returns ScopedCollectionExecution.firingTerm state
        (min consumed previous.length) published
      simp only [number, encoded, CettaWireAtom.encode, Nat.cast_min] at fresh
      have later := advance_jobs_returns state request (consumed - previous.length) jobs
      simp only [advancedJobsTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] at later
      have appendBase := ScopedCollectionExecution.append_returns ScopedCollectionExecution.firingTerm
        state (published.drop (min consumed previous.length))
          (advanceJobs request (consumed - previous.length) jobs).2
      have joined := by metta_lift checked ["left", "right"] appendBase
      collection_search_eval [resumed, old, before, split, new, after, fresh, later, joined]
        unfolding [advanceJobs, advancedJobsTerm, cursorTerm, next, previous, published,
          ScopedCollectionExecution.stateTerm, ScopedCollectionMachine.resume]

@[metta_head "gslt:collection-search:advance-lane"]
theorem advance_lane_returns (state : Effects.State) (lane : Lane) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:advance-lane"
        [encoded (loggedLaneTerm lane)])
      state (encoded (advancedLaneTerm (advanceLane lane))) := by
  let advanced := advanceJobs lane.request lane.consumed lane.state
  let nextState := advanced.1
  let firings := ScopedCollectionMachine.firings lane.request nextState
  have advancedReturns := advance_jobs_returns state lane.request lane.consumed lane.state
  simp only [advancedJobsTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] at advancedReturns
  have receiptsAtBase := ScopedCollectionExecution.publication_returns state nextState
  have receipts := by metta_lift checked ["jobs"] receiptsAtBase
  have firingsAtBase := ScopedCollectionFiringExecution.firings_returns state
    lane.request (ScopedCollectionMachine.publication nextState)
  have fired := by metta_lift checked ["request", "receipts"] firingsAtBase
  have taggedAtBase := CollectionPlanExecution.tag_returns state lane.ordinal lane.request advanced.2
  have tagged := by metta_lift checked ["ordinal", "request", "firings"] taggedAtBase
  have countAtBase := ScopedCollectionExecution.length_returns
    ScopedCollectionExecution.firingTerm state firings
  have count := by metta_lift checked ["items"] countAtBase
  dsimp [firings, ScopedCollectionMachine.firings] at count
  collection_search_eval [advancedReturns, receipts, fired, tagged, count]
    unfolding [advanceLane, advancedJobsTerm, advanced, nextState, firings, tag]

/-- The simultaneous lane update used by one logged-search round. -/
def advanceLanes (lanes : List Lane) :
    List Lane × List CollectionPlanMachine.Firing :=
  let advanced := lanes.map advanceLane
  (advanced.map Prod.fst, advanced.flatMap Prod.snd)

@[metta_head "gslt:collection-search:advance-lanes"]
theorem advance_lanes_returns (state : Effects.State) : ∀ lanes : List Lane,
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:advance-lanes"
        [encoded (encodeList loggedLaneTerm lanes)])
      state (encoded (advancedLanesTerm (advanceLanes lanes)))
  | [] => by
      collection_search_eval unfolding [advanceLanes]
  | lane :: lanes => by
      have first := advance_lane_returns state lane
      have later := advance_lanes_returns state lanes
      have joinedAtBase := ScopedCollectionExecution.append_returns
        CollectionPlanExecution.planFiringTerm state
        (advanceLane lane).2 (advanceLanes lanes).2
      have joined := by
        metta_lift checked ["left", "right"] joinedAtBase
      collection_search_eval [first, later, joined]
        unfolding [advanceLanes, List.map_cons, List.flatMap_cons]

@[metta_head "gslt:collection-search:round"]
theorem round_returns (state : Effects.State)
    (lanes : List Lane) (log : List CollectionPlanMachine.Firing) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:round"
        [encoded (encodeList loggedLaneTerm lanes),
          encoded (encodeList CollectionPlanExecution.planFiringTerm log)])
      state (encoded (loggedStateTerm (round ⟨lanes, log⟩))) := by
  have advanced := advance_lanes_returns state lanes
  simp only [advancedLanesTerm, encoded, CettaWireAtom.encode,
    CettaWireAtom.encodeMany] at advanced
  have joinedAtBase := ScopedCollectionExecution.append_returns
    CollectionPlanExecution.planFiringTerm state log
    (advanceLanes lanes).2
  have joined := by
    metta_lift checked ["left", "right"] joinedAtBase
  simp only [encoded] at joined
  collection_search_eval [advanced, joined]
    unfolding [round, advanceLanes]
  all_goals first
    | (simp [select_logged_advanced_round]; done)
    | (intro selected body selection
       metta_select [advancedLanesTerm, encoded, CettaWireAtom.encode,
         CettaWireAtom.encodeMany, select_logged_advanced_round] at selection
       obtain ⟨bindings, branch⟩ := selection
       subst bindings
       subst branch
       apply pure_let_returns _ _ _ _ _ _ _ _ (by simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup])
       · metta_capture_any joined
       · metta_eval with checked
           unfolding [round, advanceLanes, loggedStateTerm, advancedLanesTerm])

@[metta_head "gslt:collection-search:resume"]
theorem resume_returns (state : Effects.State) :
    ∀ (fuel : Nat) (search : CollectionLoggedSearch.State),
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:resume"
        [number fuel, encoded (encodeList loggedLaneTerm search.lanes),
          encoded (encodeList CollectionPlanExecution.planFiringTerm search.log)])
      state (encoded (loggedStateTerm (resume fuel search)))
  | 0, search => by
      collection_search_eval unfolding [resume]
  | fuel + 1, search => by
      obtain ⟨lanes, log⟩ := search
      have advanced := advance_lanes_returns state lanes
      simp only [advancedLanesTerm, encoded, CettaWireAtom.encode,
        CettaWireAtom.encodeMany] at advanced
      have joinedAtBase := ScopedCollectionExecution.append_returns
        CollectionPlanExecution.planFiringTerm state log (advanceLanes lanes).2
      have joined := by
        metta_lift checked ["left", "right"] joinedAtBase
      simp only [encoded] at joined
      have later := resume_returns state fuel (round ⟨lanes, log⟩)
      collection_search_eval [advanced, joined, later]
        unfolding [resume, round, advanceLanes]
      all_goals first
        | (simp [select_logged_advanced_resume]; done)
        | (intro selected body selection
           metta_select [advancedLanesTerm, encoded, CettaWireAtom.encode,
             CettaWireAtom.encodeMany, select_logged_advanced_resume] at selection
           obtain ⟨bindings, branch⟩ := selection
           subst bindings
           subst branch
           apply pure_let_star_returns _ _ _ _ _ _ _ rfl
           apply pure_let_returns _ _ _ _ _ _ _ _
             (by simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup])
           · metta_capture_any joined
           · metta_eval [later] with checked
               unfolding [resume, round, advanceLanes, loggedStateTerm,
                 advancedLanesTerm])

def statusAtom : Mettapedia.Machines.ResumableSearchRunner.Status → Atom
  | .complete => .symbol "SearchComplete"
  | .blocked => .symbol "SearchBlocked"
  | .pending => .symbol "SearchPending"

@[metta_head "gslt:collection-search:lanes-complete"]
theorem lanes_complete_returns (state : Effects.State) : ∀ lanes : List Lane,
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:lanes-complete"
        [encoded (encodeList loggedLaneTerm lanes)])
      state (encoded (CollectionSelectionExecution.booleanTerm
        (lanes.all Lane.complete)))
  | [] => by
      collection_search_eval
  | lane :: lanes => by
      have firstAtBase := ScopedCollectionExecution.complete_returns state lane.state
      have first := by
        metta_lift checked ["jobs"] firstAtBase
      have later := lanes_complete_returns state lanes
      cases finished : ScopedCollectionMachine.complete lane.state with
      | false =>
          rw [finished] at first
          collection_search_eval [first]
            unfolding [List.all_cons, Lane.complete, finished,
              CollectionSelectionExecution.booleanTerm]
      | true =>
          rw [finished] at first
          have receiptsAtBase := ScopedCollectionExecution.publication_returns state lane.state
          have receipts := by
            metta_lift checked ["jobs"] receiptsAtBase
          have firingsAtBase := ScopedCollectionFiringExecution.firings_returns state
            lane.request (ScopedCollectionMachine.publication lane.state)
          have fired := by
            metta_lift checked ["request", "receipts"] firingsAtBase
          have countAtBase := ScopedCollectionExecution.length_returns
            ScopedCollectionExecution.firingTerm state
            (ScopedCollectionMachine.firings lane.request lane.state)
          have count := by
            metta_lift checked ["items"] countAtBase
          dsimp [ScopedCollectionMachine.firings] at count
          by_cases drained : lane.consumed =
              (ScopedCollectionMachine.firings lane.request lane.state).length
          · dsimp [ScopedCollectionMachine.firings] at drained
            collection_search_eval [first, receipts, fired, count, later]
              unfolding [List.all_cons, Lane.complete, finished, drained,
                ScopedCollectionMachine.firings, CollectionSelectionExecution.booleanTerm]
          · dsimp [ScopedCollectionMachine.firings] at drained
            collection_search_eval [first, receipts, fired, count]
              unfolding [List.all_cons, Lane.complete, finished, drained,
                ScopedCollectionMachine.firings, CollectionSelectionExecution.booleanTerm]

@[metta_head "gslt:collection-search:publication-log"]
theorem publication_log_returns (state : Effects.State)
    (log : List CollectionPlanMachine.Firing) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:publication-log"
        [encoded (encodeList CollectionPlanExecution.planFiringTerm log)])
      state (encoded (encodeList CollectionPlanExecution.planFiringTerm log)) := by
  collection_search_eval

@[metta_head "gslt:collection-search:complete"]
theorem complete_returns (state : Effects.State)
    (search : CollectionLoggedSearch.State) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:complete" [encoded (loggedStateTerm search)])
      state (encoded (CollectionSelectionExecution.booleanTerm
        (CollectionLoggedSearch.complete search))) := by
  obtain ⟨lanes, log⟩ := search
  have complete := lanes_complete_returns state lanes
  collection_search_eval [complete]
    unfolding [loggedStateTerm, CollectionLoggedSearch.complete]

@[metta_head "gslt:collection-search:status-lanes"]
theorem status_lanes_returns (state : Effects.State) (lanes : List Lane) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:status-lanes"
        [encoded (encodeList loggedLaneTerm lanes)])
      state (statusAtom (if lanes.all Lane.complete then .complete else .pending)) := by
  have complete := lanes_complete_returns state lanes
  cases finished : lanes.all Lane.complete <;>
    rw [finished] at complete <;>
    collection_search_eval [complete]
      unfolding [CollectionSelectionExecution.booleanTerm, statusAtom, finished]

@[metta_head "gslt:collection-search:publication"]
theorem publication_returns (state : Effects.State) (run : Run) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:publication" [encoded (loggedRunTerm run)])
      state (encoded (encodeList CollectionPlanExecution.planFiringTerm run.state.log)) := by
  obtain ⟨sourcePattern, ⟨lanes, log⟩⟩ := run
  have published := publication_log_returns state log
  collection_search_eval [published] unfolding [loggedRunTerm, loggedStateTerm]

@[metta_head "gslt:collection-search:status"]
theorem status_returns (state : Effects.State) (run : Run) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:status" [encoded (loggedRunTerm run)])
      state (statusAtom (if CollectionLoggedSearch.complete run.state then
        .complete else .pending)) := by
  obtain ⟨sourcePattern, ⟨lanes, log⟩⟩ := run
  have status := status_lanes_returns state lanes
  collection_search_eval [status]
    unfolding [loggedRunTerm, loggedStateTerm, CollectionLoggedSearch.complete]

@[metta_head "gslt:collection-search:run"]
theorem run_returns (state : Effects.State)
    (requests : List (Nat × ScopedCollectionMachine.Request))
    (fixed : ∀ entry ∈ requests,
      CanonicalBags.arrange entry.2.kind entry.2.targets = entry.2.targets)
    (sourcePattern : Pattern) (work : Nat) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:run"
        [encoded (encodeList CollectionPlanExecution.requestEntryTerm requests),
          encoded (InferenceCettaWire.encodePattern sourcePattern), number work])
      state (encoded (loggedRunTerm
        ⟨sourcePattern, resume work (CollectionLoggedSearch.begin requests)⟩)) := by
  have lanes := lanes_begin_returns state requests fixed
  have resumed := resume_returns state work (CollectionLoggedSearch.begin requests)
  collection_search_eval [lanes, resumed]
    unfolding [CollectionLoggedSearch.begin, loggedRunTerm]

@[metta_head "gslt:collection-search:resume-run"]
theorem resume_run_returns (state : Effects.State) (run : Run) (extra : Nat) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:resume-run"
        [encoded (loggedRunTerm run), number extra])
      state (encoded (loggedRunTerm
        ⟨run.source, CollectionLoggedSearch.resume extra run.state⟩)) := by
  obtain ⟨sourcePattern, ⟨lanes, log⟩⟩ := run
  have resumed := resume_returns state extra ⟨lanes, log⟩
  collection_search_eval [resumed]
    unfolding [loggedRunTerm, loggedStateTerm]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionLoggedSearchExecution
