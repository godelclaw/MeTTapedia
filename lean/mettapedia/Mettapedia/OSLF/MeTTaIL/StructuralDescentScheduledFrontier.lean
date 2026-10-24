import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledCoverage

/-!
# Finite post-match frontiers in the shared scheduled executor

A matcher backend supplies checked answers. The existing root continuation
then checks captures, runs premises and checks the reduct. Its finite work
tree is constructed here for the actual frontier, without restarting the
root matcher. Drainage at a fixed depth is distinct from depth completeness
or fairness of an unbounded composition of searches.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

variable (environment : Environment) (outer : Goal)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
    (tail : Continuation environment (.root (depth + 1) bound type source index) outer)

/-- The existing premise evaluator and reduct checker have a finite tree for
each typed root answer, provided its final continuation has one. -/
def treeRootAnswer
    (answer : GeneralScopedMatchMachine.Answer)
    (valid : answer.Valid ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩)
    (typed : TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ answer.assignment)
    (continued : Continued environment outer _ tail) :
    Tree environment outer (.evaluate
      (.premises depth ⟨index, rule, spec, bound, 0, 0⟩ rule.premises answer.assignment)
      (.rootBody depth bound type source index rule spec declared specified admitted sorted
        answer.trace answer.assignment
        (by simpa only [GeneralScopedMatchMachine.Answer.Valid,
          MatchingExecution.ordinary, ordinaryInterpretation] using valid) typed tail)) := by
  apply treeEvaluate
  intro result
  cases result with
  | premises completed events held =>
      apply Scheduler.TaskTree.branch
      simp only [expand, delivered]
      split
      · exact .nil
      · split
        · exact .cons (continued _) .nil
        · exact .nil

/-- Construct finite work for the tasks actually selected by typed-capture
checking. Rejected answers contribute no task; accepted answers use the same
premise and reduct execution as the ordinary matcher. -/
def continueRootAnswers_forest
    (continued : Continued environment outer _ tail)
    (next : List (Task environment outer))
    (nextTrees : Scheduler.TaskForest (expand environment outer) next) :
    (answers : List {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩}) →
    Scheduler.TaskForest (expand environment outer)
      (continueRootAnswers environment outer depth bound type source index rule spec
        declared specified admitted sorted answers tail next).tasks
  | [] => nextTrees
  | answer :: rest => by
      have later := continueRootAnswers_forest continued next nextTrees rest
      simp only [continueRootAnswers, continueRootAnswer]
      split
      · rename_i checked
        exact .cons (treeRootAnswer environment outer depth bound type source index rule spec
          declared specified admitted sorted tail answer.val answer.property
          (checkTypedAssignment_sound checked) continued) later
      · exact later

/-- Every typed answer in the supplied frontier retains the independent
meaning of its premise/reduct continuation. Other answers cannot erase it. -/
theorem continueRootAnswers_covers :
    ∀ (answers : List {answer : GeneralScopedMatchMachine.Answer //
        answer.Valid ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩})
      (answer : {answer : GeneralScopedMatchMachine.Answer //
        answer.Valid ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩}),
      answer ∈ answers →
      ∀ (typed : TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩
          answer.val.assignment) (wanted : Result environment outer),
      EvaluatesTo (.rootBody depth bound type source index rule spec declared specified admitted
        sorted answer.val.trace answer.val.assignment answer.property typed tail) wanted →
      ExpansionAccepts (continueRootAnswers environment outer depth bound type source index rule spec
        declared specified admitted sorted answers tail []) wanted
  | [], _, member, _, _, _ => False.elim (List.not_mem_nil member)
  | head :: rest, answer, member, typed, wanted, meaning => by
      rcases List.mem_cons.mp member with same | remaining
      · subst answer
        simp only [continueRootAnswers, continueRootAnswer]
        simp only [checkTypedAssignment_complete typed, dite_true]
        exact .inr ⟨_, List.mem_cons_self, meaning⟩
      · have later := continueRootAnswers_covers rest answer remaining typed wanted meaning
        rcases later with emitted | ⟨task, present, denotes⟩
        · have empty := continueRootAnswers_answers environment outer depth bound type source index
            rule spec declared specified admitted sorted rest tail []
          rw [empty] at emitted
          exact False.elim (List.not_mem_nil emitted)
        · simp only [continueRootAnswers, continueRootAnswer]
          split
          · exact .inr ⟨task, List.mem_cons_of_mem _ present, denotes⟩
          · exact .inr ⟨task, present, denotes⟩

/-- The supplied frontier drains after a finite amount of retained work.
This says nothing about whether a depth cut or another unresolved obligation
was recorded: those remain in the resulting state. -/
theorem continueRootAnswers_eventually_settled
    (continued : Continued environment outer _ tail)
    (answers : List {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩}) :
    let expanded := continueRootAnswers environment outer depth bound type source index rule spec
      declared specified admitted sorted answers tail []
    let started : State environment outer :=
      { agenda := expanded.tasks, answers := expanded.answers,
        unresolved := expanded.unresolved, work := 0 }
    ∃ fuel, (run environment outer fuel started).agenda = [] := by
  let forest := continueRootAnswers_forest environment outer depth bound type source index rule spec
    declared specified admitted sorted tail continued [] .nil answers
  exact ⟨forest.cost, Scheduler.finiteWork_drains (expand environment outer)
    forest.cost _ forest (Nat.le_refl _)⟩

/-- Once the actual frontier execution drains, every result it denotes has
been published, with its assignment, target and full premise history. -/
theorem continueRootAnswers_drained_contains
    (answers : List {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩})
    (fuel : Nat) (wanted : Result environment outer)
    (accepts : ExpansionAccepts (continueRootAnswers environment outer depth bound type source index
      rule spec declared specified admitted sorted answers tail []) wanted) :
    let expanded := continueRootAnswers environment outer depth bound type source index rule spec
      declared specified admitted sorted answers tail []
    let started : State environment outer :=
      { agenda := expanded.tasks, answers := expanded.answers,
        unresolved := expanded.unresolved, work := 0 }
    (run environment outer fuel started).agenda = [] →
      wanted ∈ (run environment outer fuel started).answers := by
  dsimp only
  intro drained
  let expanded := continueRootAnswers environment outer depth bound type source index rule spec
    declared specified admitted sorted answers tail []
  let started : State environment outer :=
    { agenda := expanded.tasks, answers := expanded.answers,
      unresolved := expanded.unresolved, work := 0 }
  have initial : StateAccepts started wanted := accepts
  have retained := run_covers fuel initial
  rcases retained with published | ⟨task, present, _⟩
  · exact published
  · rw [drained] at present
    exact False.elim (List.not_mem_nil present)

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
