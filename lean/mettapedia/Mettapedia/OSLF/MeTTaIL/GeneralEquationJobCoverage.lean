import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobReadout

/-!
# Exact branch coverage of the authored equation cursor

The continuation wrapper reads every actual premise result and retains its
original trace, assignment and ordered premise history. This is separate
from the proof that the inner premise evaluator enumerates all semantic
derivations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution

open GeneralPremise.Scheduler GeneralEquationJobs

theorem append_drop_cons {A : Type} (answers future : List A) (cursor : Nat) (answer : A)
    (found : answers[cursor]? = some answer) :
    (answers ++ future).drop cursor = answer :: (answers ++ future).drop (cursor + 1) := by
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp found
  have appended : cursor < (answers ++ future).length := by simp only [List.length_append]; omega
  rw [List.drop_eq_getElem_cons appended, List.getElem_append_left within, same]

def premiseProjection (request : Request) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured : ScopedRuleMatching.Assignment)
    {goal : GeneralPremise.Execution.Goal}
    (result : GeneralPremise.Execution.Result request.environment goal) : Option Receipt :=
  match result with
  | .premises completed history _ => finish request.plan request.bound request.expected request.job
      trace captured completed history
  | _ => none

theorem expandPremises_emits (request : Request) (frame : PremiseFrame request)
    (result : GeneralPremise.Execution.Result request.environment (request.premises frame.captured))
    (receipt : Receipt) (found : frame.state.answers[frame.cursor]? = some result)
    (finished : premiseProjection request frame.trace frame.captured result = some receipt) :
    receipt ∈ (expand request (.premises frame)).answers.map Subtype.val := by
  cases result with
  | premises completed history held =>
      simp only [premiseProjection] at finished
      simp only [expand, expandPremises, found]
      repeat' split
      all_goals
        have same : premiseProjection request frame.trace frame.captured
            (GeneralPremise.Execution.Result.premises completed history held) = _ :=
          congrArg (premiseProjection request frame.trace frame.captured) (by assumption)
        simp only [premiseProjection] at same
        simp_all only [Option.some.injEq, List.map_cons, List.map_nil,
          List.mem_singleton, List.not_mem_nil]
      all_goals cases finished

theorem premise_tree_receipts (request : Request) (frame : PremiseFrame request)
    (forest : TaskForest (GeneralPremise.Execution.expand request.environment
      (request.premises frame.captured)) frame.state.agenda)
    (tree : TaskTree (expand request) (.premises frame))
    (result : GeneralPremise.Execution.Result request.environment (request.premises frame.captured))
    (receipt : Receipt)
    (member : result ∈ (frame.state.answers ++ forest.answers).drop frame.cursor)
    (finished : premiseProjection request frame.trace frame.captured result = some receipt) :
    receipt ∈ tree.answers.map Subtype.val := by
  cases treeEq : tree with
  | branch children =>
      have parentCost : tree.cost = children.cost + 1 := by rw [treeEq]; rfl
      cases found : frame.state.answers[frame.cursor]? with
      | none =>
          by_cases idle : GeneralPremise.Scheduler.settled frame.state = true
          · have empty : frame.state.agenda = [] := List.isEmpty_iff.mp idle
            have forestEmpty := forest.answers_empty empty
            have past := List.getElem?_eq_none_iff.mp found
            simp only [forestEmpty, List.append_nil, List.drop_eq_nil_of_le past, List.not_mem_nil] at member
          · have unfinished : frame.state.agenda ≠ [] := by
              intro empty
              exact idle (List.isEmpty_iff.mpr empty)
            have tasks : (expand request (.premises frame)).tasks =
                [Task.premises {frame with
                  state := GeneralPremise.Execution.tick request.environment (request.premises frame.captured) frame.state}] := by
              simp only [expand, expandPremises, found, Bool.eq_false_iff.mpr idle,
                Bool.false_eq_true, if_false]
            let selectedChildren := tasks ▸ children
            have sameAnswers := TaskForest.answers_cast tasks children
            have sameCost := TaskForest.cost_cast tasks children
            cases selectedChildrenEq : selectedChildren with
            | cons child tail =>
                cases tail
                have nextMember : result ∈
                    ((GeneralPremise.Execution.tick request.environment (request.premises frame.captured) frame.state).answers ++
                      (forest.advance frame.state).answers).drop frame.cursor := by
                  simp only [GeneralPremise.Execution.tick]
                  rw [forest.advance_answers frame.state]
                  exact member
                have later := premise_tree_receipts request {frame with
                    state := GeneralPremise.Execution.tick request.environment (request.premises frame.captured) frame.state}
                  (forest.advance frame.state) child result receipt nextMember finished
                simp only [TaskTree.answers, List.map_append, List.mem_append]
                right
                rw [← sameAnswers]
                change receipt ∈ selectedChildren.answers.map Subtype.val
                rw [selectedChildrenEq]
                simpa only [TaskForest.answers, List.append_nil] using later
      | some current =>
          rw [append_drop_cons frame.state.answers forest.answers frame.cursor current found,
            List.mem_cons] at member
          rcases member with same | laterMember
          · subst result
            have emitted := expandPremises_emits request frame current receipt found finished
            simpa only [TaskTree.answers, List.map_append, List.mem_append] using Or.inl emitted
          · have tasks : (expand request (.premises frame)).tasks =
                [Task.premises {frame with cursor := frame.cursor + 1}] := by
              simp only [expand, expandPremises, found]
              split
              all_goals repeat' split
              all_goals rfl
            let selectedChildren := tasks ▸ children
            have sameAnswers := TaskForest.answers_cast tasks children
            have sameCost := TaskForest.cost_cast tasks children
            cases selectedChildrenEq : selectedChildren with
            | cons child tail =>
                cases tail
                have later := premise_tree_receipts request {frame with cursor := frame.cursor + 1}
                  forest child result receipt laterMember finished
                simp only [TaskTree.answers, List.map_append, List.mem_append]
                right
                rw [← sameAnswers]
                change receipt ∈ selectedChildren.answers.map Subtype.val
                rw [selectedChildrenEq]
                simpa only [TaskForest.answers, List.append_nil] using later
termination_by tree.cost
decreasing_by
  all_goals
    try simp only [TaskTree.cost]
    change selectedChildren.cost = children.cost at sameCost
    rw [selectedChildrenEq] at sameCost
    try simp only [TaskForest.cost] at sameCost
    omega

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
