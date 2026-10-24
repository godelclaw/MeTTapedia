import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledTrees

/-!
# Finite work for recursive scoped execution

The actual transition tree decreases the semantic depth at recursive calls.
At a fixed depth, ordered premise tails, quantified bodies and remaining
collection elements decrease independently. Matcher and provider frames
retain their separately earned structural work measures.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

def premiseWorkWeight : Premise → Nat
  | .forAll _ _ body => premiseWorkWeight body + 2
  | _ => 1

def Goal.rank : Goal → Nat × (Nat × (Nat × Nat))
  | .root depth _ _ _ _ => (depth, 4, 0, 0)
  | .steps depth _ _ _ _ => (depth, 5, 0, 0)
  | .premises depth _ ps _ => (depth + 1, 3, ps.length, 0)
  | .premise depth _ p _ => (depth + 1, 2, premiseWorkWeight p, 0)
  | .quantified depth _ _ body _ elements _ =>
      (depth + 1, 2, premiseWorkWeight body + 1, elements.length)

def treeScan (environment : Environment) (outer : Goal) (depth : Nat) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (limit cursor : Nat)
    (tail : Continuation environment (.steps depth bound type source limit) outer)
    (continued : Continued environment outer _ tail)
    (roots : ∀ index, index < limit →
      ∀ childTail : Continuation environment (.root depth bound type source index) outer,
        Continued environment outer _ childTail →
        Tree environment outer (.evaluate (.root depth bound type source index) childTail)) :
    Tree environment outer (.scanChildren depth bound type source limit cursor tail) := by
  apply Scheduler.TaskTree.branch
  simp only [expand]
  split
  · rename_i earlier
    have decrease : limit - (cursor + 1) < limit - cursor := by omega
    refine .cons (roots cursor earlier _ ?_)
      (.cons (treeScan environment outer depth bound type source limit (cursor + 1) tail continued roots) .nil)
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
  | premises depth context premises initial =>
    cases premises with
    | nil =>
      exact .cons (continued (.premises initial [] .nil)) .nil
    | cons premise premises =>
      refine .cons (treeEvaluate environment outer (.premise depth context premise initial) _ ?_) .nil
      intro result
      cases result with
      | premise middle event head =>
        apply Scheduler.TaskTree.branch
        refine .cons (treeEvaluate environment outer (.premises depth context.next premises middle) _ ?_) .nil
        intro result
        cases result with
        | premises final history rest =>
          exact .branch (.cons (continued _) .nil)
  | quantified depth context parameter body index elements initial =>
    cases elements with
    | nil => exact .cons (continued (.quantified initial [] .nil)) .nil
    | cons element elements =>
      simp only [expand, evaluate]
      split
      · refine .cons (treeEvaluate environment outer
          (.premise depth context.quantified body
            (bindParameter parameter (localValue context.bound element) initial)) _ ?_) .nil
        intro result
        cases result with
        | premise middle event head =>
          apply Scheduler.TaskTree.branch
          refine .cons (treeEvaluate environment outer
            (.quantified depth context parameter body (index + 1) elements
              initial) _ ?_) .nil
          intro result
          cases result with
          | quantified final history rest =>
            exact .branch (.cons (continued _) .nil)
      · exact .nil
  | premise depth context premise initial =>
    cases premise with
    | relationQuery relation arguments =>
      let request : Query.Request := ⟨context, relation, arguments, initial⟩
      exact .cons (treeQuery environment outer depth request (Query.start environment request)
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
          (.quantified depth context parameter body 0 elements initial) _ ?_) .nil
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
            (.steps depth context.bound type actualSource environment.language.rewrites.length) _ ?_) .nil
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
          (.steps depth (step.binders ++ context.bound) step.resultType actualSource environment.language.rewrites.length) _ ?_) .nil
        intro result
        cases result with
        | steps index trace captured completed history actualTarget earlier valid =>
          apply Scheduler.TaskTree.branch
          exact .cons (treeTarget environment outer _ continued) .nil
  | root depth bound type source index =>
    cases depth with
    | zero => exact .nil
    | succ depth =>
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
                (.premises depth ⟨index, rule, spec, bound, 0, 0⟩ rule.premises answer.assignment) _ ?_
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

  | steps depth bound type source limit =>
    refine .cons (treeScan environment outer depth bound type source limit 0 tail continued ?_) .nil
    intro index earlier childTail childContinued
    have decrease : index < limit := earlier
    exact treeEvaluate environment outer (.root depth bound type source index) childTail childContinued
termination_by goal.rank
decreasing_by
  all_goals subst_vars
  all_goals dsimp only [Goal.rank, premiseWorkWeight, Context.next, Context.quantified]
  all_goals simp only [Prod.lex_def]
  all_goals simp

def treeStart (environment : Environment) (goal : Goal) :
    Tree environment goal (.evaluate goal (.done goal)) :=
  treeEvaluate environment goal goal (.done goal) (doneTrees environment goal)

def finish (environment : Environment) (goal : Goal) : State environment goal :=
  run environment goal (treeStart environment goal).cost (start environment goal)

theorem finish_settled (environment : Environment) (goal : Goal) :
    (finish environment goal).agenda = [] := by
  exact Scheduler.finiteWork_drains (expand environment goal) _ (start environment goal)
    (.cons (treeStart environment goal) .nil) (by simp [Scheduler.TaskForest.cost])

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
