import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionRequestExecution
import Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearchStable
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Canonical
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RunnerSource

/-!
# The logged collection search behind the shared native search dictionary

The runner's `CollectionSearch` descriptor carries the name order used to
canonicalize receipt targets. Requests are reconstructed from the current
source and plan on every fresh search. All five operations run in the same
checked runtime as the established class backend. Backend selection remains
an admission and emission decision.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearch
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open LibraryCheck

syntax "collection_runner_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| collection_runner_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (metta_call_in runnerProof_checked using runnerProof_agreement
       metta_eval [$facts,*] with runnerProof_checked in runnerProof_agreement
         unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
           Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
           pattern_symbol_unmatched, $extra,*]))

def collectionSearchBackendTerm (names : List String) : Term :=
  .application "CollectionSearch"
    [encodeList Term.string names]

abbrev collectionSearchBackend (names : List String) : Atom :=
  encoded (collectionSearchBackendTerm names)

@[metta_head "gslt:search:run"]
theorem collection_search_run_returns (state : Effects.State)
    (names : List String) (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern)
    (arranged : CollectionRequestExecution.ArrangedRoot source) (work : Nat) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:run"
        [collectionSearchBackend names,
          encoded (CompletePlanWire.planTerm plan table bound expected),
          patternValue source, number work])
      state (encoded (CollectionLoggedSearchExecution.loggedRunTerm
        (CollectionLoggedSearch.run plan certificate source work))) := by
  have nativeAtSource := CollectionRequestExecution.run_plan_returns state plan
    certificate table bound expected source arranged work
  have native := collection_runner_lifted% ["plan", "source", "work"] nativeAtSource
  collection_runner_eval [native]
    unfolding [collectionSearchBackend, collectionSearchBackendTerm]

/-- The actual native dictionary call reaches a finite complete collection
frontier with exact independent receipt coverage. This is the collection
matching/provisional-reduct profile; typed and premise execution is the
separate shared continuation, not an admission consequence of this theorem. -/
theorem collection_search_finite_exact (state : Effects.State)
    (names : List String) (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern)
    (arranged : CollectionRequestExecution.ArrangedRoot source) :
    ∃ work,
      PureReturns runnerLibrary.runtime [] state
        (apply "gslt:search:run"
          [collectionSearchBackend names,
            encoded (CompletePlanWire.planTerm plan table bound expected),
            patternValue source, number work])
        state (encoded (CollectionLoggedSearchExecution.loggedRunTerm
          (CollectionLoggedSearch.run plan certificate source work))) ∧
      complete (CollectionLoggedSearch.run plan certificate source work).state = true ∧
      ∀ firing, firing ∈ (CollectionLoggedSearch.run plan certificate source work).state.log ↔
        CollectionLoggedSearch.Valid
          (CollectionLoggedSearch.requests plan certificate source) firing := by
  obtain ⟨work, finished⟩ := CollectionLoggedSearch.eventually_complete
    (CollectionLoggedSearch.begin (CollectionLoggedSearch.requests plan certificate source))
  exact ⟨work, collection_search_run_returns state names plan certificate table bound expected
    source arranged work, finished,
    CollectionLoggedSearch.completed_log_exact _ work finished⟩

@[metta_head "gslt:search:resume"]
theorem collection_search_resume_returns (state : Effects.State)
    (names : List String) (planValue : Atom) (run : Run) (work : Nat) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:resume"
        [collectionSearchBackend names, planValue,
          encoded (CollectionLoggedSearchExecution.loggedRunTerm run), number work])
      state (encoded (CollectionLoggedSearchExecution.loggedRunTerm
        ⟨run.source, resume work run.state⟩)) := by
  have nativeAtSource := CollectionLoggedSearchExecution.resume_run_returns
    state run work
  have native := collection_runner_lifted% ["run", "extra"] nativeAtSource
  collection_runner_eval [native]
    unfolding [collectionSearchBackend, collectionSearchBackendTerm]

@[metta_head "gslt:search:publication"]
theorem collection_search_publication_returns (state : Effects.State)
    (names : List String) (run : Run) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:publication"
        [collectionSearchBackend names,
          encoded (CollectionLoggedSearchExecution.loggedRunTerm run)])
      state (encoded (encodeList CollectionPlanExecution.planFiringTerm run.state.log)) := by
  have nativeAtSource := CollectionLoggedSearchExecution.publication_returns state run
  have native := collection_runner_lifted% ["run"] nativeAtSource
  collection_runner_eval [native]
    unfolding [collectionSearchBackend, collectionSearchBackendTerm]

@[metta_head "gslt:search:status"]
theorem collection_search_status_returns (state : Effects.State)
    (names : List String) (planValue : Atom) (run : Run) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:status"
        [collectionSearchBackend names, planValue,
          encoded (CollectionLoggedSearchExecution.loggedRunTerm run)])
      state (CollectionLoggedSearchExecution.statusAtom
        (if complete run.state then .complete else .pending)) := by
  have nativeAtSource := CollectionLoggedSearchExecution.status_returns state run
  have native := collection_runner_lifted% ["run"] nativeAtSource
  collection_runner_eval [native]
    unfolding [collectionSearchBackend, collectionSearchBackendTerm]

/-- Canonical targets are selected in the same runtime as the retained search. -/
@[metta_head "gslt:search:target"]
theorem collection_search_target_returns (state : Effects.State)
    (names : List String) (ordered : CanonicalCompare.NameOrdered names)
    (standard : Atom) (firing : CollectionPlanMachine.Firing)
    (covered : CanonicalCompare.Covered names firing.receipt.target) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:target"
        [collectionSearchBackend names, standard,
          encoded (CollectionPlanExecution.planFiringTerm firing)])
      state (patternValue (CanonicalBags.canon firing.receipt.target)) := by
  have canonicalAtSource := canon_returns state ordered firing.receipt.target covered
  have canonical := canonical_runner_lifted% ["names", "pattern"] canonicalAtSource
  obtain ⟨ordinal, request, receipt⟩ := firing
  obtain ⟨sourceReceipt, target⟩ := receipt
  collection_runner_eval [canonical]
    unfolding [collectionSearchBackend, collectionSearchBackendTerm,
      CollectionPlanExecution.planFiringTerm, ScopedCollectionExecution.firingTerm]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
