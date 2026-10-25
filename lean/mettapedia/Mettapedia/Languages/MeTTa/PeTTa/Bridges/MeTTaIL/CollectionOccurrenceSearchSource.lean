import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceDiscoveryExecution
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch

/-!
# Native retained occurrence search operations

The search stores the plan needed by the original rule-job receipt readout.
Matching and premise continuations remain in the existing retained machine.
The wire keeps that complete machine beside its derived finished receipt view;
reading publication does not replay validation or change the raw packet log.
Completion checks matcher work, continuation agendas and unresolved obligations
separately. These operations do not select an emission profile.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceBatch CollectionOccurrenceMatcher CanonicalCompare
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ResumableSearchRunner (Status)
open SpaceSemantics Eval BridgeKit WireKit
open scoped ProgramQuotation

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_occurrence_search.metta"
    sha256 "a3288d04780aa15ff63e44d38f3ecdc4a8691e28f12cf244b4dac159e32a3d6c"

def library : Library :=
  ⟨CollectionOccurrenceDiscoveryExecution.library.runtime, source.program,
    ["gslt:occurrence-search:"]⟩

theorem checked : library.check = true := by decide +kernel

def runTerm (table : List (String × TypeExpr))
    (run : CollectionOccurrenceSearch.Run plan bound expected) : Term :=
  .application "RecursiveOccurrenceRun"
    [CompletePlanWire.planTerm plan table bound expected,
      InferenceCettaWire.encodePattern run.source,
      CollectionOccurrenceMachineExecution.stateTerm run.state,
      encodeList ScopedRuleJobReadoutExecution.receiptTerm
        (run.state.batch.log.filterMap fun packet => packet.finish? plan bound expected)]

def statusAtom : Status → Atom
  | .complete => .symbol "SearchComplete"
  | .blocked => .symbol "SearchBlocked"
  | .pending => .symbol "SearchPending"

syntax "occurrence_search_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| occurrence_search_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

syntax "search_from_machine% " "[" str,* "] " term:max : term
macro_rules
  | `(search_from_machine% [$names,*] $fact) =>
    `(by
      have atContexts := by
        metta_lift CollectionOccurrenceDiscoveryExecution.contexts_checked [$names,*] $fact
      have atDiscovery := by
        metta_lift CollectionOccurrenceDiscoveryExecution.checked [$names,*] atContexts
      metta_lift checked [$names,*] atDiscovery)

syntax "search_from_canonical% " "[" str,* "] " term:max : term
macro_rules
  | `(search_from_canonical% [$names,*] $fact) =>
    `(by
      have atBase := by metta_lift CompleteExecution.collection_base_checked [$names,*] $fact
      have atRecursive := by metta_lift RecursiveCollectionExecution.checked [$names,*] atBase
      have atMatcher := by metta_lift CollectionOccurrenceMatcherExecution.checked [$names,*] atRecursive
      have atDiscovery := discovery_from_matcher% [$names,*] atMatcher
      metta_lift checked [$names,*] atDiscovery)

@[metta_head "gslt:occurrence-search:lanes-complete"]
theorem lanes_complete_returns (host : Effects.State) :
    ∀ lanes : List (Lane plan bound expected sourcePattern),
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:lanes-complete"
        [encoded (encodeList CollectionOccurrenceMatcherExecution.laneTerm lanes)])
      host (Effects.boolean (lanes.all fun lane => RecursiveCollectionMachine.complete lane.state))
  | [] => by occurrence_search_eval unfolding [encodeList]
  | lane :: lanes => by
    have atMatcher := by
      metta_lift CollectionOccurrenceMatcherExecution.checked ["state"]
        (RecursiveCollectionExecution.complete_returns host lane.state)
    have atDiscovery := discovery_from_matcher% ["state"] atMatcher
    have complete := by metta_lift checked ["state"] atDiscovery
    have later := lanes_complete_returns host lanes
    cases done : RecursiveCollectionMachine.complete lane.state <;>
      occurrence_search_eval [complete, later] unfolding
        [CollectionOccurrenceMatcherExecution.laneTerm, encodeList, List.all_cons, done]

@[metta_head "gslt:occurrence-search:frames-idle"]
theorem frames_idle_returns (host : Effects.State) :
    ∀ frames : List (Frame plan bound expected sourcePattern),
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:frames-idle"
        [encoded (encodeList CollectionOccurrenceBatchExecution.frameTerm frames)])
      host (Effects.boolean (frames.all fun frame => frame.state.agenda.isEmpty))
  | [] => by occurrence_search_eval unfolding [encodeList]
  | frame :: frames => by
    have later := frames_idle_returns host frames
    cases agenda : frame.state.agenda <;>
      simp only [List.all_cons, agenda, List.isEmpty_nil, List.isEmpty_cons, Bool.true_and, Bool.false_and] <;>
      occurrence_search_eval [later] unfolding
        [CollectionOccurrenceBatchExecution.frameTerm, RecursiveCollectionContinuationExecution.frameTerm,
          CompleteExecution.DescentCodec.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
          encodeList, List.all_cons, agenda]

@[metta_head "gslt:occurrence-search:frames-resolved"]
theorem frames_resolved_returns (host : Effects.State) :
    ∀ frames : List (Frame plan bound expected sourcePattern),
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:frames-resolved"
        [encoded (encodeList CollectionOccurrenceBatchExecution.frameTerm frames)])
      host (Effects.boolean (frames.all fun frame => frame.state.unresolved.isEmpty))
  | [] => by occurrence_search_eval unfolding [encodeList]
  | frame :: frames => by
    have later := frames_resolved_returns host frames
    cases unresolved : frame.state.unresolved <;>
      simp only [List.all_cons, unresolved, List.isEmpty_nil, List.isEmpty_cons, Bool.true_and, Bool.false_and] <;>
      occurrence_search_eval [later] unfolding
        [CollectionOccurrenceBatchExecution.frameTerm, RecursiveCollectionContinuationExecution.frameTerm,
          CompleteExecution.DescentCodec.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
          encodeList, List.all_cons, unresolved]

@[metta_head "gslt:occurrence-search:status"]
theorem status_returns (host : Effects.State) (table : List (String × TypeExpr))
    (run : CollectionOccurrenceSearch.Run plan bound expected) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:status" [encoded (runTerm table run)])
      host (statusAtom (CollectionOccurrenceSearch.status run)) := by
  have matchers := lanes_complete_returns host run.state.matchers
  have idle := frames_idle_returns host run.state.batch.frames
  have resolved := frames_resolved_returns host run.state.batch.frames
  cases matching : run.state.matchers.all (fun lane => RecursiveCollectionMachine.complete lane.state) <;>
    cases agendas : run.state.batch.frames.all (fun frame => frame.state.agenda.isEmpty) <;>
    cases obligations : run.state.batch.frames.all (fun frame => frame.state.unresolved.isEmpty) <;>
    occurrence_search_eval [matchers, idle, resolved] unfolding
      [runTerm, CollectionOccurrenceMachineExecution.stateTerm, CollectionOccurrenceBatchExecution.stateTerm,
        CollectionOccurrenceSearch.status, matching, agendas, obligations, statusAtom]

@[metta_head "gslt:occurrence-search:target"]
theorem target_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (receipt : GeneralRuleJobs.Receipt) (covered : Covered names receipt.target) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:target"
        [encoded (encodeList Term.string names), encoded (ScopedRuleJobReadoutExecution.receiptTerm receipt)])
      host (encoded (InferenceCettaWire.encodePattern (CanonicalBags.canon receipt.target))) := by
  have canonical := search_from_canonical% ["names", "pattern"]
    (CompleteExecution.canon_returns host ordered receipt.target covered)
  occurrence_search_eval [canonical] unfolding [ScopedRuleJobReadoutExecution.receiptTerm]


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution
