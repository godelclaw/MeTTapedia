import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobCoverage

/-!
# Preserved unresolved premise work in equation jobs

Reading a published premise result does not discard the inner scheduler's
obligations. An equation continuation drains that scheduler and forwards
every unresolved item with its original reason.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution

open GeneralPremise.Scheduler GeneralEquationJobs

theorem expandPremises_tasks_found (request : Request) (frame : PremiseFrame request)
    (result : GeneralPremise.Execution.Result request.environment (request.premises frame.captured))
    (found : frame.state.answers[frame.cursor]? = some result) :
    (expand request (.premises frame)).tasks =
      [Task.premises {frame with cursor := frame.cursor + 1}] := by
  simp only [expand, expandPremises, found]
  split
  all_goals repeat' split
  all_goals rfl

theorem expandPremises_unresolved_found (request : Request) (frame : PremiseFrame request)
    (result : GeneralPremise.Execution.Result request.environment (request.premises frame.captured))
    (found : frame.state.answers[frame.cursor]? = some result) :
    (expand request (.premises frame)).unresolved = [] := by
  simp only [expand, expandPremises, found]
  split
  all_goals repeat' split
  all_goals rfl

theorem premise_tree_obligations (request : Request) (frame : PremiseFrame request)
    (forest : TaskForest (GeneralPremise.Execution.expand request.environment
      (request.premises frame.captured)) frame.state.agenda)
    (tree : TaskTree (expand request) (.premises frame)) :
    tree.obligations = (frame.state.unresolved ++ forest.obligations).map Obligation.premise := by
  cases treeEq : tree with
  | branch children =>
      have parentCost : tree.cost = children.cost + 1 := by rw [treeEq]; rfl
      cases found : frame.state.answers[frame.cursor]? with
      | none =>
          by_cases idle : GeneralPremise.Scheduler.settled frame.state = true
          · have empty : frame.state.agenda = [] := List.isEmpty_iff.mp idle
            have forestEmpty := forest.obligations_empty empty
            have tasks : (expand request (.premises frame)).tasks = [] := by
              simp only [expand, expandPremises, found, idle, if_true]
            have same : children.obligations = [] := by
              rw [← TaskForest.obligations_cast tasks children]
              cases tasks ▸ children
              rfl
            change (expand request (.premises frame)).unresolved ++ children.obligations = _
            rw [same, forestEmpty]
            simp only [expand, expandPremises, found, idle, if_true, List.append_nil]
          · have tasks : (expand request (.premises frame)).tasks =
                [Task.premises {frame with state :=
                  GeneralPremise.Execution.tick request.environment (request.premises frame.captured) frame.state}] := by
              simp only [expand, expandPremises, found, Bool.eq_false_iff.mpr idle,
                Bool.false_eq_true, if_false]
            let selectedChildren := tasks ▸ children
            have sameObligations := TaskForest.obligations_cast tasks children
            have sameCost := TaskForest.cost_cast tasks children
            cases selectedChildrenEq : selectedChildren with
            | cons child tail =>
                cases tail
                have later := premise_tree_obligations request {frame with
                    state := GeneralPremise.Execution.tick request.environment (request.premises frame.captured) frame.state}
                  (forest.advance frame.state) child
                have pendingReadout :
                    (GeneralPremise.Execution.tick request.environment (request.premises frame.captured) frame.state).unresolved ++
                      (forest.advance frame.state).obligations = frame.state.unresolved ++ forest.obligations :=
                  forest.advance_obligations frame.state
                change child.obligations = ((GeneralPremise.Execution.tick request.environment
                  (request.premises frame.captured) frame.state).unresolved ++
                    (forest.advance frame.state).obligations).map Obligation.premise at later
                rw [pendingReadout] at later
                have forwarded : (expand request (.premises frame)).unresolved = [] := by
                  simp only [expand, expandPremises, found, Bool.eq_false_iff.mpr idle,
                    Bool.false_eq_true, if_false]
                change (expand request (.premises frame)).unresolved ++ children.obligations = _
                rw [forwarded, List.nil_append]
                rw [← sameObligations]
                change selectedChildren.obligations = _
                rw [selectedChildrenEq]
                simpa only [TaskForest.obligations, List.append_nil] using later
      | some result =>
          have tasks := expandPremises_tasks_found request frame result found
          let selectedChildren := tasks ▸ children
          have sameObligations := TaskForest.obligations_cast tasks children
          have sameCost := TaskForest.cost_cast tasks children
          cases selectedChildrenEq : selectedChildren with
          | cons child tail =>
              cases tail
              have later := premise_tree_obligations request {frame with cursor := frame.cursor + 1}
                forest child
              change (expand request (.premises frame)).unresolved ++ children.obligations = _
              rw [expandPremises_unresolved_found request frame result found, List.nil_append]
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

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
