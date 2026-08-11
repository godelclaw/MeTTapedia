import Mettapedia.Logic.Prolog.RuntimeControlRegression
import Mettapedia.Logic.Prolog.SourceRuntimeRegression

/-!
Executable side of the shared-runtime control differential.  The fixtures use
the canonical `Logic.Prolog.RuntimeControl` entrypoint; this driver only renders
their ordered answers for comparison with pinned SWI-Prolog.
-/

open Mettapedia.Logic.LP.RuntimeQueryRegression
open Mettapedia.Logic.Prolog
open Mettapedia.Logic.Prolog.RuntimeControlRegression

def renderConstant : QConst -> String
  | .a => "a"
  | .b => "b"
  | .c => "c"

def renderAnswers (label : String) :
    Option (List QConst × Nat × Nat) -> IO Unit
  | some (answers, 0, 0) =>
      IO.println s!"{label}={String.intercalate "," (answers.map renderConstant)}"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

def renderStringAnswers (label : String) :
    Option (List String × Nat × Nat) -> IO Unit
  | some (answers, 0, 0) =>
      IO.println s!"{label}={String.intercalate "," answers}"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

def renderCount (label : String) : Option (Nat × Nat × Nat) -> IO Unit
  | some (count, 0, 0) => IO.println s!"{label}={count}"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

def renderRaisedAtom (label : String) :
    Option (String × Nat × Nat) -> IO Unit
  | some (name, 0, 0) => IO.println s!"{label}=raised({name})"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not raise"

def renderAtomBag (bag : List String) : String :=
  s!"[{String.intercalate "," bag}]"

def renderAtomBags (label : String) :
    Option (List (List String) × Nat × Nat) → IO Unit
  | some (bags, 0, 0) =>
      IO.println s!"{label}={String.intercalate ";" (bags.map renderAtomBag)}"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

def renderBool (label : String) (value : Bool) : IO Unit :=
  IO.println s!"{label}={if value then 1 else 0}"

def main : IO Unit := do
  renderAnswers "source_order" (runTyped [] disjSourceOrder)
  renderAnswers "restore_before_right" (runTyped [] disjRestoresBeforeRight)
  renderAnswers "cut_prunes_right" (runTyped [] disjCutPrunesRight)
  renderAnswers "callee_cut_retains_caller"
    (runTyped calleeCutRetainsCallerDisjProgram calleeCutRetainsCallerDisj)
  renderAnswers "if_first_success" (runTyped [] hardIfFirstConditionSuccess)
  renderAnswers "if_then_failure" (runTyped [] hardIfThenFailureDoesNotRetry)
  renderAnswers "if_false_else" (runTyped [] hardIfFalseUsesElse)
  renderAnswers "if_condition_cut_else"
    (runTyped [] hardIfConditionCutPreservesElse)
  renderAnswers "if_then_cut_outer"
    (runTyped [] hardIfThenCutPrunesOuterDisj)
  renderAnswers "soft_if_condition_answers"
    (runTyped [] softIfKeepsConditionAnswers)
  renderAnswers "soft_if_then_retry"
    (runTyped [] softIfThenFailureRetriesCondition)
  renderAnswers "soft_if_false_else" (runTyped [] softIfFalseUsesElse)
  renderAnswers "soft_if_condition_cut_else"
    (runTyped [] softIfConditionCutPreservesElse)
  renderAnswers "soft_if_then_cut_outer"
    (runTyped [] softIfThenCutPrunesOuterDisj)
  renderAnswers "once_first" (runTyped [] onceKeepsFirstAnswer)
  renderAnswers "once_failure" (runTyped [] onceFailureHasNoAnswer)
  renderAnswers "once_cut_caller"
    (runTyped [] onceCutPreservesCallerDisj)
  renderAnswers "once_then_cut_outer"
    (runTyped [] onceThenCutPrunesCallerDisj)
  renderAnswers "once_restore_caller"
    (runTyped [] onceFailureRestoresCallerAlternative)
  renderStringAnswers "meta_dynamic_disj"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.dynamicDisjunction)
  renderStringAnswers "meta_cut_retains_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaCutRetainsCaller)
  renderCount "call_three"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.binaryFactProgram
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.callThree)
  renderCount "heap_built_callable"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.binaryFactProgram
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.heapBuiltCallable)
  renderStringAnswers "catch_ground"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.caughtGround)
  renderRaisedAtom "catch_throw_time_reject"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runRaisedAtom []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.throwTimeBoundCatcherRejects)
  renderRaisedAtom "catch_recovery_rethrow"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runRaisedAtom []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.recoveryRethrowEscapes)
  renderStringAnswers "catch_guard_cut_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.guardedCutRetainsCaller)
  renderStringAnswers "catch_recovery_cut_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.recoveryCutRetainsCaller)
  renderStringAnswers "catch_guard_answers"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.catchRetainsGuardedAnswers)
  renderRaisedAtom "catch_nested_throw_time_reject"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runRaisedAtom []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.nestedMismatchRetainsThrowTimeBinding)
  renderCount "catch_copy_separates_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.packetCopySeparatesCaller)
  renderCount "catch_copy_preserves_sharing"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.packetCopyPreservesSharing)
  renderCount "catch_copy_preserves_separation"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.packetCopyPreservesSeparation)
  renderCount "throw_variable_instantiation_error"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.throwVariableRaisesInstantiationError)
  renderAtomBags "findall_order_multiplicity"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomBagsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.findallOrderMultiplicity
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.bagIdentity)
  renderAtomBags "findall_binding_isolation"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomBagsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.findallIsolatesGeneratorBindings
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.bagIdentity)
  renderAtomBags "findall_empty"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomBagsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.findallEmpty
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.bagIdentity)
  renderAtomBags "findall_cut_retains_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomBagsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.findallCutRetainsCaller
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.bagIdentity)
  renderAtomBags "findall_exception_discards_partial"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomBagsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.findallExceptionDiscardsPartialBag
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.bagIdentity)
  renderBool "findall_copy_fresh_shared"
    Mettapedia.Logic.Prolog.SourceRuntimeRegression.copiedSolutionsAreFreshAndShared
  renderBool "findall_copy_separation"
    Mettapedia.Logic.Prolog.SourceRuntimeRegression.copiedSolutionPreservesSeparation
  renderStringAnswers "db_assertz_then_call"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertzThenCall)
  renderStringAnswers "db_failed_branch_persists"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.failedBranchAssertionPersists)
  renderStringAnswers "db_asserta_assertz_order"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertaAndAssertzOrder)
  renderCount "db_assertz_ref_bound"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertzReferenceIsBound)
  renderCount "db_asserta_ref_bound"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertaReferenceIsBound)
  renderCount "db_assert_refs_distinct"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertedReferencesAreDistinct)
  renderCount "db_assert_ref_roundtrip"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertedReferenceRoundTrip)
  renderStringAnswers "db_retract_source_order"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.retractFactsInOrder)
  renderStringAnswers "db_retract_cut_prunes_later"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.retractCutPrunesLater)
  renderStringAnswers "db_retract_fact_skips_rule"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.retractFactSkipsRule)
  renderStringAnswers "db_retract_failed_branch_persists"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.failedBranchRetractionPersists)
  renderBool "db_retract_snapshot_no_drift"
    Mettapedia.Logic.Prolog.SourceRuntimeRegression.retractSnapshotDoesNotDrift
  renderStringAnswers "db_retract_snapshot_retains_erased"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.retractSnapshotRetainsErasedCandidate)
  renderBool "db_snapshot_no_drift"
    Mettapedia.Logic.Prolog.SourceRuntimeRegression.snapshotDoesNotDrift
  renderStringAnswers "db_snapshot_later_call"
    Mettapedia.Logic.Prolog.SourceRuntimeRegression.laterCallSeesAssertion
