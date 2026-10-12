import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseMachineDebt
import Mettapedia.OSLF.Framework.GeneralFiniteWorkReadout

/-!
# Finite continuation work for the actual equation job

Equation cursors read every emitted match and premise answer. Between answers
they advance the real inner machines by one tick. Their finite work trees use
the scoped matcher's structural work measure and the premise scheduler's
actual continuation forest; no precomputed answer batch replaces execution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution

open GeneralPremise.Scheduler GeneralEquationJobs

def premiseTree (request : Request) (frame : PremiseFrame request)
    (forest : TaskForest (GeneralPremise.Execution.expand request.environment
      (request.premises frame.captured)) frame.state.agenda) :
    TaskTree (expand request) (.premises frame) := by
  apply TaskTree.branch
  simp only [expand, expandPremises]
  split
  · rename_i found
    split
    · exact .nil
    · rename_i pending
      have unfinished : frame.state.agenda ≠ [] := by
        intro same
        simp only [GeneralPremise.Scheduler.settled, same, List.isEmpty_nil] at pending
        exact pending trivial
      have smaller := forest.advance_cost frame.state unfinished
      have decrease : Prod.Lex (· < ·) (· < ·)
          ((forest.advance frame.state).cost,
            (GeneralPremise.Execution.tick request.environment (request.premises frame.captured) frame.state).answers.length - frame.cursor)
          (forest.cost, frame.state.answers.length - frame.cursor) :=
        Prod.Lex.left _ _ (by omega)
      exact .cons (premiseTree request {frame with
        state := GeneralPremise.Execution.tick request.environment (request.premises frame.captured) frame.state}
        (forest.advance frame.state)) .nil
  · rename_i result found
    have within := (List.getElem?_eq_some_iff.mp found).1
    have decrease : Prod.Lex (· < ·) (· < ·)
        (forest.cost, frame.state.answers.length - (frame.cursor + 1))
        (forest.cost, frame.state.answers.length - frame.cursor) :=
      Prod.Lex.right _ (by omega)
    cases result with
    | premises completed history held =>
        repeat' split
        all_goals exact .cons (premiseTree request {frame with cursor := frame.cursor + 1} forest) .nil
termination_by (forest.cost, frame.state.answers.length - frame.cursor)
decreasing_by all_goals assumption

abbrev PremiseForests (request : Request) :=
  ∀ captured : ScopedRuleMatching.Assignment,
    TaskForest (GeneralPremise.Execution.expand request.environment (request.premises captured))
      (GeneralPremise.Execution.start request.environment (request.premises captured)).agenda

def matchingTree (request : Request) (premiseForests : PremiseForests request)
    (frame : MatchFrame request) : TaskTree (expand request) (.matching frame) := by
  apply TaskTree.branch
  simp only [expand, expandMatching]
  split
  · rename_i found
    split
    · exact .nil
    · rename_i pending
      have decrease := GeneralPremise.matcherDebt_tick request.matcher frame.state frame.cursor found
        (Bool.eq_false_iff.mpr pending)
      exact .cons (matchingTree request premiseForests {frame with
        state := GeneralScopedMatchMachine.tick request.matcher frame.state
        reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable}) .nil
  · rename_i answer found
    have decrease := GeneralPremise.matcherDebt_cursor request.matcher frame.state frame.cursor answer found
    split
    · apply TaskForest.cons
      · exact premiseTree request _ (premiseForests answer.assignment)
      · exact .cons (matchingTree request premiseForests {frame with cursor := frame.cursor + 1}) .nil
    · exact .cons (matchingTree request premiseForests {frame with cursor := frame.cursor + 1}) .nil
termination_by GeneralPremise.matcherDebt request.matcher frame.state frame.cursor
decreasing_by all_goals assumption

def startForest (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job)
    (premiseForests : PremiseForests request) : TaskForest (expand request) (start request licensed).agenda := by
  unfold start
  split
  next checked =>
    exact .cons (matchingTree request premiseForests _) .nil
  next => exact .nil

def workBound (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job)
    (premiseForests : PremiseForests request) : Nat := (startForest request licensed premiseForests).cost

def finishState (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job)
    (premiseForests : PremiseForests request) : State request :=
  run request (workBound request licensed premiseForests) (start request licensed)

theorem finishState_reachable (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job)
    (premiseForests : PremiseForests request) : Reachable request licensed (finishState request licensed premiseForests) :=
  reachable_run _ .start

theorem finishState_settled (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job)
    (premiseForests : PremiseForests request) : settled (finishState request licensed premiseForests) = true := by
  simp only [finishState, settled]
  apply List.isEmpty_iff.mpr
  exact finiteWork_drains (expand request) _ _ (startForest request licensed premiseForests) (Nat.le_refl _)

theorem finishState_readouts (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job)
    (premiseForests : PremiseForests request) :
    (finishState request licensed premiseForests).answers = (start request licensed).answers ++
      (startForest request licensed premiseForests).answers ∧
    (finishState request licensed premiseForests).unresolved = (start request licensed).unresolved ++
      (startForest request licensed premiseForests).obligations :=
  finiteWork_readouts (expand request) _ _ (startForest request licensed premiseForests) (Nat.le_refl _)

theorem settled_reachable_unique {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (reached : Reachable request licensed state) (idle : settled state = true)
    (premiseForests : PremiseForests request) : state = finishState request licensed premiseForests := by
  obtain ⟨fuel, same⟩ := reachable_from_start reached
  subst state
  apply settled_run_unique (expand request)
  · exact List.isEmpty_iff.mp idle
  · exact List.isEmpty_iff.mp (finishState_settled request licensed premiseForests)

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
