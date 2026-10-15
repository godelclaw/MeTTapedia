import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobFiniteWork
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFinishReadout

/-!
# Resolution readouts of actual rule-occurrence jobs

The outer rule job drains the actual root evaluator, preserving every inner
unresolved reason. A proved resolution theorem for that root computation
therefore gives the complete outer job without erasing withheld work.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution

open GeneralPremise.Scheduler

theorem root_tasks_found (request : Request) (frame : Frame request)
    (result : GeneralPremise.Execution.Result request.environment request.goal)
    (found : frame.state.answers[frame.cursor]? = some result) :
    (expand request (.root frame)).tasks = [Task.root {frame with cursor := frame.cursor + 1}] := by
  simp only [expand, found]
  cases result
  rfl

theorem root_unresolved_found (request : Request) (frame : Frame request)
    (result : GeneralPremise.Execution.Result request.environment request.goal)
    (found : frame.state.answers[frame.cursor]? = some result) :
    (expand request (.root frame)).unresolved = [] := by
  simp only [expand, found]
  cases result
  rfl

theorem root_tree_obligations (request : Request) (frame : Frame request)
    (forest : TaskForest (GeneralPremise.Execution.expand request.environment
      request.goal) frame.state.agenda)
    (tree : TaskTree (expand request) (.root frame)) :
    tree.obligations = (frame.state.unresolved ++ forest.obligations).map Obligation.premise := by
  cases treeEq : tree with
  | branch children =>
      have parentCost : tree.cost = children.cost + 1 := by rw [treeEq]; rfl
      cases found : frame.state.answers[frame.cursor]? with
      | none =>
          by_cases idle : GeneralPremise.Scheduler.settled frame.state = true
          · have empty : frame.state.agenda = [] := List.isEmpty_iff.mp idle
            have forestEmpty := forest.obligations_empty empty
            have tasks : (expand request (.root frame)).tasks = [] := by
              simp only [expand, found, idle, if_true]
            have same : children.obligations = [] := by
              rw [← TaskForest.obligations_cast tasks children]
              cases tasks ▸ children
              rfl
            change (expand request (.root frame)).unresolved ++ children.obligations = _
            rw [same, forestEmpty]
            simp only [expand, found, idle, if_true, List.append_nil]
          · have tasks : (expand request (.root frame)).tasks =
                [Task.root {frame with state :=
                  GeneralPremise.Execution.tick request.environment request.goal frame.state}] := by
              simp only [expand, found, Bool.eq_false_iff.mpr idle,
                Bool.false_eq_true, if_false]
            let selectedChildren := tasks ▸ children
            have sameObligations := TaskForest.obligations_cast tasks children
            have sameCost := TaskForest.cost_cast tasks children
            cases selectedChildrenEq : selectedChildren with
            | cons child tail =>
                cases tail
                have later := root_tree_obligations request {frame with
                    state := GeneralPremise.Execution.tick request.environment request.goal frame.state}
                  (forest.advance frame.state) child
                have pendingReadout :
                    (GeneralPremise.Execution.tick request.environment request.goal frame.state).unresolved ++
                      (forest.advance frame.state).obligations = frame.state.unresolved ++ forest.obligations :=
                  forest.advance_obligations frame.state
                change child.obligations = ((GeneralPremise.Execution.tick request.environment
                  request.goal frame.state).unresolved ++
                    (forest.advance frame.state).obligations).map Obligation.premise at later
                rw [pendingReadout] at later
                have forwarded : (expand request (.root frame)).unresolved = [] := by
                  simp only [expand, found, Bool.eq_false_iff.mpr idle,
                    Bool.false_eq_true, if_false]
                change (expand request (.root frame)).unresolved ++ children.obligations = _
                rw [forwarded, List.nil_append]
                rw [← sameObligations]
                change selectedChildren.obligations = _
                rw [selectedChildrenEq]
                simpa only [TaskForest.obligations, List.append_nil] using later
      | some result =>
          have tasks := root_tasks_found request frame result found
          let selectedChildren := tasks ▸ children
          have sameObligations := TaskForest.obligations_cast tasks children
          have sameCost := TaskForest.cost_cast tasks children
          cases selectedChildrenEq : selectedChildren with
          | cons child tail =>
              cases tail
              have later := root_tree_obligations request {frame with cursor := frame.cursor + 1}
                forest child
              change (expand request (.root frame)).unresolved ++ children.obligations = _
              rw [root_unresolved_found request frame result found, List.nil_append]
              rw [← sameObligations]
              change selectedChildren.obligations = _
              rw [selectedChildrenEq]
              simpa only [TaskForest.obligations, List.append_nil] using later
termination_by tree.cost
decreasing_by
  all_goals
    try simp only [TaskTree.cost]
    change selectedChildren.cost = children.cost at sameCost
    rw [selectedChildrenEq] at sameCost
    try simp only [TaskForest.cost] at sameCost
    omega


theorem finishState_resolved (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (resolved : (GeneralPremise.Execution.finish request.environment request.goal).unresolved = []) :
    (finishState request licensed).unresolved = [] := by
  let frame : Frame request :=
    ⟨licensed, GeneralPremise.Execution.start request.environment request.goal, 0⟩
  let forest : InnerForest request frame.state :=
    .cons (GeneralPremise.Execution.treeStart request.environment request.goal) .nil
  let tree := rootTree request frame forest
  have innerResolved : frame.state.unresolved ++ forest.obligations = [] := by
    simp only [frame, GeneralPremise.Execution.start, forest, TaskForest.obligations,
      List.nil_append, List.append_nil]
    rw [← GeneralPremise.Execution.finish_obligations, resolved]
  rw [(finishState_readouts request licensed).2]
  change tree.obligations ++ [] = []
  rw [List.append_nil, root_tree_obligations request frame forest tree, innerResolved, List.map_nil]

theorem finishState_complete_of_resolved (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (resolved : (GeneralPremise.Execution.finish request.environment request.goal).unresolved = []) :
    complete (finishState request licensed) = true :=
  (complete_iff _).mpr ⟨finishState_settled request licensed, finishState_resolved request licensed resolved⟩

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution
