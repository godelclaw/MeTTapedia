import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionStateExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContextExecution
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMatcher

/-!
# Native retained matcher lanes at licensed collection occurrences

The native lane retains the original typed job, actual matcher request,
unfinished matching state and accumulated work. Advancing exposes only the
new answer suffix, including complete nested allocation histories.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMatcherExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax CollectionOccurrenceMatcher
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_match_lanes.metta"
    sha256 "e03684e60d567dd54beecd15074f74a4c9a8eb25ac36038112f6f1ff638e077c"

def library : BridgeKit.Library :=
  ⟨RecursiveCollectionExecution.library.runtime, source.program,
    ["gslt:occurrence-matcher:"]⟩

theorem checked : library.check = true := by decide +kernel

def originTerm (job : CollectionOccurrenceHandoff.Job) : Term :=
  .application "RecursiveOccurrenceJob"
    [ScopedRuleJobReadoutExecution.jobTerm job.origin, CollectionContextExecution.variantTerm job.variant]

def laneTerm (lane : Lane plan bound expected sourcePattern) : Term :=
  .application "RecursiveOccurrenceLane"
    [originTerm lane.job,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm lane.job.request,
      RecursiveCollectionExecution.stateTerm lane.state, .natural lane.spent]

def advancedTerm (lane : Lane plan bound expected sourcePattern) : Term :=
  .application "RecursiveOccurrenceMatches"
    [laneTerm (lane.resume 1), encodeList RecursiveCollectionExecution.answerTerm lane.fresh]

syntax "occurrence_matcher_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| occurrence_matcher_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        laneTerm, advancedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

@[metta_head "gslt:occurrence-matcher:begin"]
theorem begin_returns (host : Effects.State) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected sourcePattern) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-matcher:begin"
        [encoded (originTerm job), encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request)])
      host (encoded (laneTerm (Lane.begin job licensed))) := by
  have native := RecursiveCollectionExecution.start_returns host job.request
  have begun := by metta_lift checked ["request"] native
  occurrence_matcher_eval [begun] unfolding [Lane.begin]

@[metta_head "gslt:occurrence-matcher:resume"]
theorem resume_returns (host : Effects.State) (names : List String)
    (ordered : CanonicalCompare.NameOrdered names) (work : Nat)
    (lane : Lane plan bound expected sourcePattern)
    (covered : RecursiveCollectionMachine.StateCovered names lane.state) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-matcher:resume"
        [encoded (encodeList Term.string names), number work, encoded (laneTerm lane)])
      host (encoded (laneTerm (lane.resume work))) := by
  have native := RecursiveCollectionExecution.run_returns host names ordered lane.job.request work lane.state covered
  have resumed := by metta_lift checked ["names", "request", "fuel", "state"] native
  occurrence_matcher_eval [resumed] unfolding [Lane.resume]

private theorem drop_returns {α : Type} (encoder : α → Term) (host : Effects.State)
    (count : Nat) (items : List α) :
    PureReturns library.runtime [] host
      (apply "gslt:complete:drop" [number count, encoded (encodeList encoder items)])
      host (encoded (encodeList encoder (items.drop count))) := by
  have atLaws := by
    metta_lift CompleteExecution.laws_checked ["count", "items"]
      (CompleteExecution.drop_list_returns encoder host count items)
  have atCanonical := by metta_lift CompleteExecution.canonical_checked ["count", "items"] atLaws
  have atCollection := by metta_lift CompleteExecution.collection_base_checked ["count", "items"] atCanonical
  have atRecursive := by metta_lift RecursiveCollectionExecution.checked ["count", "items"] atCollection
  metta_lift checked ["count", "items"] atRecursive

@[metta_head "gslt:occurrence-matcher:advance"]
theorem advance_returns (host : Effects.State) (names : List String)
    (ordered : CanonicalCompare.NameOrdered names) (lane : Lane plan bound expected sourcePattern)
    (covered : RecursiveCollectionMachine.StateCovered names lane.state) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-matcher:advance"
        [encoded (encodeList Term.string names), encoded (laneTerm lane)])
      host (encoded (advancedTerm lane)) := by
  have count := by metta_lift checked ["items"]
    (RecursiveCollectionExecution.length_returns RecursiveCollectionExecution.answerTerm host lane.state.answers)
  have resumed := resume_returns host names ordered 1 lane covered
  have fresh := drop_returns RecursiveCollectionExecution.answerTerm host lane.state.answers.length
    (lane.resume 1).state.answers
  occurrence_matcher_eval [count, resumed, fresh] unfolding
    [Lane.resume, Lane.fresh, RecursiveCollectionExecution.stateTerm]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMatcherExecution
