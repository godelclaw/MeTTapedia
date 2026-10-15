import Mettapedia.OSLF.MeTTaIL.GeneralEquationMatcherWork
import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobCertifiedWork
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseOrderedAdmission

/-!
# Independent receipt coverage of the actual authored equation job

The matcher cursor preserves each scoped alternative. Each accepted capture
starts the real ordered premise scheduler, whose independently justified
answers are read without collapsing their traces or authored origins.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution

open GeneralPremise.Scheduler GeneralEquationJobs

theorem matching_tree_receipts (request : Request) (frame : MatchFrame request)
    (tree : TaskTree (expand request) (.matching frame))
    (answer : GeneralScopedMatchMachine.Answer)
    (member : answer ∈ (finishMatcher request.matcher frame.state).answers.drop frame.cursor)
    (typed : GeneralPremise.TypedAssignment request.environment (request.job.context request.plan) answer.assignment)
    (result : GeneralPremise.Execution.Result request.environment (request.premises answer.assignment))
    (ordered : result.ordered = true) (receipt : Receipt)
    (finished : premiseProjection request answer.trace answer.assignment result = some receipt) :
    receipt ∈ tree.answers.map Subtype.val := by
  cases treeEq : tree with
  | branch children =>
      have parentCost : tree.cost = children.cost + 1 := by rw [treeEq]; rfl
      cases found : frame.state.answers[frame.cursor]? with
      | none =>
          by_cases idle : GeneralScopedMatchMachine.complete frame.state = true
          · rw [finishMatcher_finished request.matcher frame.state idle] at member
            have past := List.getElem?_eq_none_iff.mp found
            simp only [List.drop_eq_nil_of_le past, List.not_mem_nil] at member
          · have pending := Bool.eq_false_iff.mpr idle
            have tasks : (expand request (.matching frame)).tasks =
                [Task.matching {frame with
                  state := GeneralScopedMatchMachine.tick request.matcher frame.state
                  reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable}] := by
              simp only [expand, expandMatching]
              split
              next actualFound => simp only [pending, Bool.false_eq_true, if_false]
              next actual actualFound => cases actualFound.symm.trans found
            let selectedChildren := tasks ▸ children
            have sameAnswers := TaskForest.answers_cast tasks children
            have sameCost := TaskForest.cost_cast tasks children
            cases selectedChildrenEq : selectedChildren with
            | cons child tail =>
                cases tail
                have nextMember : answer ∈ (finishMatcher request.matcher
                    (GeneralScopedMatchMachine.tick request.matcher frame.state)).answers.drop frame.cursor := by
                  rw [finishMatcher_tick request.matcher frame.state pending]
                  exact member
                have later := matching_tree_receipts request {frame with
                    state := GeneralScopedMatchMachine.tick request.matcher frame.state
                    reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable}
                  child answer nextMember typed result ordered receipt finished
                simp only [TaskTree.answers, List.map_append, List.mem_append]
                right
                rw [← sameAnswers]
                change receipt ∈ selectedChildren.answers.map Subtype.val
                rw [selectedChildrenEq]
                simpa only [TaskForest.answers, List.append_nil] using later
      | some current =>
          rw [GeneralScopedMatchMachine.mem_drop_cursor_iff] at member
          rcases member with same | remaining
          · have actualFound := finishMatcher_answer_at request.matcher frame.state frame.cursor current found
            have actualSame : current = answer := Option.some.inj (actualFound.symm.trans same)
            subst answer
            have checked := GeneralPremise.checkTypedAssignment_complete typed
            let branch : PremiseFrame request :=
              ⟨frame.licensed, frame.sourceTyped, current.trace, current.assignment,
                GeneralScopedMatchMachine.answers_sound frame.reachable (List.mem_of_getElem? found),
                GeneralPremise.checkTypedAssignment_sound checked,
                GeneralPremise.Execution.start request.environment (request.premises current.assignment), 0⟩
            have tasks : (expand request (.matching frame)).tasks =
                [Task.premises branch, Task.matching {frame with cursor := frame.cursor + 1}] := by
              simp only [expand, expandMatching]
              split
              next unavailable => cases unavailable.symm.trans found
              next actual actualFound =>
                have same : actual = current := Option.some.inj (actualFound.symm.trans found)
                subst actual
                rw [dif_pos checked]
            let selectedChildren := tasks ▸ children
            have sameAnswers := TaskForest.answers_cast tasks children
            have sameCost := TaskForest.cost_cast tasks children
            cases selectedChildrenEq : selectedChildren with
            | cons child tail =>
                cases tail with
                | cons later tail =>
                    cases tail
                    let forest := authoredPremiseForests request current.assignment
                    have actualResult := GeneralPremise.Execution.finish_contains request.environment
                      (request.premises current.assignment) result ordered
                    have readout := finiteWork_readouts (GeneralPremise.Execution.expand request.environment
                      (request.premises current.assignment))
                      (GeneralPremise.Execution.treeStart request.environment (request.premises current.assignment)).cost
                      (GeneralPremise.Execution.start request.environment (request.premises current.assignment)) forest
                      (by simp only [forest, authoredPremiseForests, TaskForest.cost, Nat.add_zero]; exact Nat.le_refl _)
                    have actualReadout :
                        (GeneralPremise.Execution.finish request.environment (request.premises current.assignment)).answers =
                          (GeneralPremise.Execution.start request.environment (request.premises current.assignment)).answers ++
                            forest.answers := readout.1
                    rw [actualReadout] at actualResult
                    have emitted := premise_tree_receipts request branch forest child result receipt actualResult finished
                    simp only [TaskTree.answers, List.map_append, List.mem_append]
                    right
                    rw [← sameAnswers]
                    change receipt ∈ selectedChildren.answers.map Subtype.val
                    rw [selectedChildrenEq]
                    simp only [TaskForest.answers, List.append_nil, List.map_append, List.mem_append]
                    exact .inl emitted
          · by_cases checked : GeneralPremise.checkTypedAssignment request.environment
                (request.job.context request.plan) current.assignment = true
            · let branch : PremiseFrame request :=
                ⟨frame.licensed, frame.sourceTyped, current.trace, current.assignment,
                  GeneralScopedMatchMachine.answers_sound frame.reachable (List.mem_of_getElem? found),
                  GeneralPremise.checkTypedAssignment_sound checked,
                  GeneralPremise.Execution.start request.environment (request.premises current.assignment), 0⟩
              have tasks : (expand request (.matching frame)).tasks =
                  [Task.premises branch, Task.matching {frame with cursor := frame.cursor + 1}] := by
                simp only [expand, expandMatching]
                split
                next unavailable => cases unavailable.symm.trans found
                next actual actualFound =>
                  have same : actual = current := Option.some.inj (actualFound.symm.trans found)
                  subst actual
                  rw [dif_pos checked]
              let selectedChildren := tasks ▸ children
              have sameAnswers := TaskForest.answers_cast tasks children
              have sameCost := TaskForest.cost_cast tasks children
              cases selectedChildrenEq : selectedChildren with
              | cons child tail =>
                  cases tail with
                  | cons later tail =>
                      cases tail
                      have emitted := matching_tree_receipts request {frame with cursor := frame.cursor + 1}
                        later answer remaining typed result ordered receipt finished
                      simp only [TaskTree.answers, List.map_append, List.mem_append]
                      right
                      rw [← sameAnswers]
                      change receipt ∈ selectedChildren.answers.map Subtype.val
                      rw [selectedChildrenEq]
                      simp only [TaskForest.answers, List.append_nil, List.map_append, List.mem_append]
                      exact .inr emitted
            · have tasks : (expand request (.matching frame)).tasks =
                  [Task.matching {frame with cursor := frame.cursor + 1}] := by
                simp only [expand, expandMatching]
                split
                next unavailable => cases unavailable.symm.trans found
                next actual actualFound =>
                  have same : actual = current := Option.some.inj (actualFound.symm.trans found)
                  subst actual
                  rw [dif_neg checked]
              let selectedChildren := tasks ▸ children
              have sameAnswers := TaskForest.answers_cast tasks children
              have sameCost := TaskForest.cost_cast tasks children
              cases selectedChildrenEq : selectedChildren with
              | cons child tail =>
                  cases tail
                  have emitted := matching_tree_receipts request {frame with cursor := frame.cursor + 1}
                    child answer remaining typed result ordered receipt finished
                  simp only [TaskTree.answers, List.map_append, List.mem_append]
                  right
                  rw [← sameAnswers]
                  change receipt ∈ selectedChildren.answers.map Subtype.val
                  rw [selectedChildrenEq]
                  simpa only [TaskForest.answers, List.append_nil] using emitted
termination_by tree.cost
decreasing_by
  all_goals
    try simp only [TaskTree.cost]
    change selectedChildren.cost = children.cost at sameCost
    rw [selectedChildrenEq] at sameCost
    try simp only [TaskForest.cost] at sameCost
    omega

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
