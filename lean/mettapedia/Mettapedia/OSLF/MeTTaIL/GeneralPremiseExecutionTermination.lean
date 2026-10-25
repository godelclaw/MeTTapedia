import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionTrees

/-!
# Declaration-derived termination of the full premise machine

Every evaluator constructs a finite tree of its actual continuation steps.
Child searches visit smaller declaration positions. At one position, ordered
premise tails, nested quantified bodies and remaining collection elements
decrease independently. No execution rank or complete child oracle is an
input to the machine.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

def premiseWorkWeight : Premise → Nat
  | .forAll _ _ body => premiseWorkWeight body + 2
  | _ => 1

def Goal.rank : Goal → Nat × (Nat × (Nat × Nat))
  | .root _ _ _ index => (index, 4, 0, 0)
  | .steps _ _ _ limit => (limit, 1, 0, 0)
  | .premises context ps _ => (context.ruleIndex, 3, ps.length, 0)
  | .premise context p _ => (context.ruleIndex, 2, premiseWorkWeight p, 0)
  | .quantified context _ body _ elements _ =>
      (context.ruleIndex, 2, premiseWorkWeight body + 1, elements.length)

def treeScan (environment : Environment) (outer : Goal) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (limit cursor : Nat)
    (tail : Continuation environment (.steps bound type source limit) outer)
    (continued : Continued environment outer _ tail)
    (roots : ∀ index, index < limit →
      ∀ childTail : Continuation environment (.root bound type source index) outer,
        Continued environment outer _ childTail →
        Tree environment outer (.evaluate (.root bound type source index) childTail)) :
    Tree environment outer (.scanChildren bound type source limit cursor tail) := by
  apply Scheduler.TaskTree.branch
  simp only [expand]
  split
  · rename_i earlier
    have decrease : limit - (cursor + 1) < limit - cursor := by omega
    refine .cons (roots cursor earlier _ ?_)
      (.cons (treeScan environment outer bound type source limit (cursor + 1) tail continued roots) .nil)
    intro result
    cases result with
    | root trace captured completed history target valid =>
      exact .branch (.cons (continued _) .nil)
  · exact .nil
termination_by limit - cursor
decreasing_by assumption

def treeEvaluate (environment : Environment) (outer : Goal) (goal : Goal)
    (tail : Continuation environment goal outer) (continued : Continued environment outer goal tail) :
    Tree environment outer (.evaluate goal tail) := by
  apply Scheduler.TaskTree.branch
  cases goal with
  | premises context premises initial =>
    cases premises with
    | nil =>
      exact .cons (continued (.premises initial [] .nil)) .nil
    | cons premise premises =>
      refine .cons (treeEvaluate environment outer (.premise context premise initial) _ ?_) .nil
      intro result
      cases result with
      | premise middle event head =>
        apply Scheduler.TaskTree.branch
        refine .cons (treeEvaluate environment outer (.premises context.next premises middle) _ ?_) .nil
        intro result
        cases result with
        | premises final history rest =>
          exact .branch (.cons (continued _) .nil)
  | quantified context parameter body index elements initial =>
    cases elements with
    | nil => exact .cons (continued (.quantified initial [] .nil)) .nil
    | cons element elements =>
      simp only [expand, evaluate]
      split
      · refine .cons (treeEvaluate environment outer
          (.premise context.quantified body
            (bindParameter parameter (localValue context.bound element) initial)) _ ?_) .nil
        intro result
        cases result with
        | premise middle event head =>
          apply Scheduler.TaskTree.branch
          refine .cons (treeEvaluate environment outer
            (.quantified context parameter body (index + 1) elements
              initial) _ ?_) .nil
          intro result
          cases result with
          | quantified final history rest =>
            exact .branch (.cons (continued _) .nil)
      · exact .nil
  | premise context premise initial =>
    cases premise with
    | relationQuery relation arguments =>
      let request : Query.Request := ⟨context, relation, arguments, initial⟩
      exact .cons (treeQuery environment outer request (Query.start environment request)
        0 tail continued) .nil
    | freshness condition =>
      simp only [expand, evaluate, evaluatePremise]
      split
      · exact .nil
      · split
        · exact .cons (continued _) .nil
        · exact .nil
    | forAll collection parameter body =>
      simp only [expand, evaluate, evaluatePremise]
      split
      · exact .nil
      · rename_i kind elements read
        refine .cons (treeEvaluate environment outer
          (.quantified context parameter body 0 elements initial) _ ?_) .nil
        intro result
        cases result with
        | quantified final history valid =>
          exact .branch (.cons (continued _) .nil)
    | congruence source target =>
      simp only [expand, evaluate, evaluatePremise]
      split
      · exact .nil
      · split
        · exact .nil
        · rename_i type typed actualSource interpreted
          refine .cons (treeEvaluate environment outer
            (.steps context.bound type actualSource context.ruleIndex) _ ?_) .nil
          intro result
          cases result with
          | steps index trace captured completed history actualTarget earlier valid =>
            apply Scheduler.TaskTree.branch
            exact .cons (treeTarget environment outer _ continued) .nil
    | scopedStep step =>
      simp only [expand, evaluate, evaluatePremise]
      split
      · exact .nil
      · rename_i actualSource interpreted
        refine .cons (treeEvaluate environment outer
          (.steps (step.binders ++ context.bound) step.resultType actualSource context.ruleIndex) _ ?_) .nil
        intro result
        cases result with
        | steps index trace captured completed history actualTarget earlier valid =>
          apply Scheduler.TaskTree.branch
          exact .cons (treeTarget environment outer _ continued) .nil
  | root bound type source index =>
    simp only [expand, evaluate, evaluateRoot]
    split
    · exact .nil
    · rename_i rule declared
      split
      · exact .nil
      · rename_i spec specified
        split
        · split
          · refine .cons (treeRootMatch environment outer _ ?_) .nil
            intro answer valid typed
            refine treeEvaluate environment outer
              (.premises ⟨index, rule, spec, bound, 0, 0⟩ rule.premises answer.assignment) _ ?_
            intro result
            cases result with
            | premises completed history held =>
              apply Scheduler.TaskTree.branch
              simp only [expand, delivered]
              split
              · exact .nil
              · split
                · exact .cons (continued _) .nil
                · exact .nil
          · exact .nil
        · exact .nil
  | steps bound type source limit =>
    refine .cons (treeScan environment outer bound type source limit 0 tail continued ?_) .nil
    intro index earlier childTail childContinued
    have decrease : index < limit := earlier
    exact treeEvaluate environment outer (.root bound type source index) childTail childContinued
termination_by goal.rank
decreasing_by
  all_goals subst_vars
  all_goals dsimp only [Goal.rank, premiseWorkWeight, Context.next, Context.quantified]
  all_goals simp only [Prod.lex_def]
  all_goals simp
  all_goals omega

def treeStart (environment : Environment) (goal : Goal) :
    Tree environment goal (.evaluate goal (.done goal)) :=
  treeEvaluate environment goal goal (.done goal) (doneTrees environment goal)

def finish (environment : Environment) (goal : Goal) : State environment goal :=
  run environment goal (treeStart environment goal).cost (start environment goal)

theorem finish_settled (environment : Environment) (goal : Goal) :
    (finish environment goal).agenda = [] := by
  exact Scheduler.finiteWork_drains (expand environment goal) _ (start environment goal)
    (.cons (treeStart environment goal) .nil) (by simp [Scheduler.TaskForest.cost])

/-- Any budget covering the original finite task tree returns the same
complete scheduler state. Extra budget does not duplicate answers or work. -/
theorem run_eq_finish_of_cost_le (environment : Environment) (goal : Goal)
    (fuel : Nat) (saturated : (treeStart environment goal).cost ≤ fuel) :
    run environment goal fuel (start environment goal) = finish environment goal := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le saturated
  rw [run_add]
  exact Scheduler.run_idle _ extra (finish environment goal) (finish_settled environment goal)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution
