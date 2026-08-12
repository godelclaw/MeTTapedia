import Mettapedia.Logic.Prolog.SingleSidedRuleRegression

/-! Render the source-shaped Lean SSU fixtures for exact comparison with the
pinned SWI oracle. -/

open Mettapedia.Logic.Prolog.SingleSidedRuleRegression

private def render (label : String) :
    Option (List String × Nat × Nat) → IO Unit
  | some (answers, 0, 0) =>
      IO.println s!"{label}=[{String.intercalate "," answers}]"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError
        s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

def main : IO Unit := do
  render "caller_binding_rejected" callerBindingAnswers
  render "ground_match_commits" groundMatchAnswers
  render "failed_guard_falls_through" failedGuardAnswers
  render "successful_guard_commits" successfulGuardAnswers
  render "fresh_head_bindings_allowed" freshHeadBindingAnswers
  render "ordinary_head_binds_caller" ordinaryHeadAnswers
