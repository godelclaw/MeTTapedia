import Mettapedia.Logic.Prolog.RuntimeControlRegression

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
