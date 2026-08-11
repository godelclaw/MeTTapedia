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
