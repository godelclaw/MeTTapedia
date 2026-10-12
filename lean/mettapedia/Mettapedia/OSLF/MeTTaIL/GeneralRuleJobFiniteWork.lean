import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionTermination
import Mettapedia.OSLF.Framework.GeneralFiniteWorkReadout
import Mettapedia.OSLF.Framework.GeneralFiniteCursorWork

/-!
# Derived drainage of actual rule-occurrence jobs

The work tree is calculated from the real premise machine and its retained
answer cursor. It provides an executable completion budget without a supplied
rank, answer list or child oracle. Unresolved obligations survive drainage.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution

open Syntax

abbrev InnerForest (request : Request) (state : GeneralPremise.Execution.State request.environment request.goal) :=
  GeneralPremise.Scheduler.TaskForest (GeneralPremise.Execution.expand request.environment request.goal) state.agenda

def rootTree (request : Request) (frame : Frame request) (forest : InnerForest request frame.state) :
    GeneralPremise.Scheduler.TaskTree (expand request) (.root frame) := by
  apply GeneralPremise.Scheduler.TaskTree.branch
  simp only [expand]
  split
  · rename_i found
    split
    · exact .nil
    · rename_i pending
      have nonempty : frame.state.agenda ≠ [] := by
        intro empty
        simp only [GeneralPremise.Scheduler.settled, empty, List.isEmpty_nil, not_true_eq_false] at pending
      have decreased : (forest.advance frame.state).cost < forest.cost := by
        have equality := forest.advance_cost frame.state nonempty
        omega
      exact .cons (rootTree request { frame with
          state := GeneralPremise.Execution.tick request.environment request.goal frame.state }
        (forest.advance frame.state)) .nil
  · rename_i result found
    have within := (List.getElem?_eq_some_iff.mp found).1
    have decreased : frame.state.answers.length - (frame.cursor + 1) <
        frame.state.answers.length - frame.cursor := by omega
    cases result with
    | root trace captured completed history target valid =>
      exact .cons (rootTree request {frame with cursor := frame.cursor + 1} forest) .nil
termination_by (forest.cost, frame.state.answers.length - frame.cursor)
decreasing_by
  all_goals simp only [Prod.lex_def]
  · exact Or.inl decreased
  · exact Or.inr ⟨trivial, decreased⟩

def startForest (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) :
    GeneralPremise.Scheduler.TaskForest (expand request) (start request licensed).agenda :=
  .cons (rootTree request
    ⟨licensed, GeneralPremise.Execution.start request.environment request.goal, 0⟩
    (.cons (GeneralPremise.Execution.treeStart request.environment request.goal) .nil)) .nil

def workBound (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) : Nat :=
  (startForest request licensed).cost

def finishState (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) : State request :=
  run request (workBound request licensed) (start request licensed)

theorem finishState_reachable (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) :
    Reachable request licensed (finishState request licensed) := reachable_run .start _

theorem finishState_settled (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) :
    (finishState request licensed).agenda = [] :=
  GeneralPremise.Scheduler.finiteWork_drains (expand request) _ _ (startForest request licensed) (Nat.le_refl _)

theorem finishState_readouts (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) :
    (finishState request licensed).answers = (startForest request licensed).answers ∧
      (finishState request licensed).unresolved = (startForest request licensed).obligations := by
  have complete := GeneralPremise.Scheduler.finiteWork_readouts (expand request) _ _
    (startForest request licensed) (Nat.le_refl _)
  simpa only [finishState, workBound, run, start, List.nil_append] using complete

theorem reachable_finiteWork {request : Request}
    {licensed : request.job.Valid request.plan request.bound request.expected request.source}
    {state : State request} (reached : Reachable request licensed state) :
    Nonempty (GeneralPremise.Scheduler.TaskForest (expand request) state.agenda) := by
  induction reached with
  | start => exact ⟨startForest request licensed⟩
  | tick _ ih =>
      obtain ⟨forest⟩ := ih
      exact ⟨forest.advance _⟩

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution
