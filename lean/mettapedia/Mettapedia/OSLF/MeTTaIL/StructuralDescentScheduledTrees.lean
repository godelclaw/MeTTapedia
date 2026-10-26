import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseMachineDebt
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFiniteWork

/-!
# Finite trees for actual premise continuations

The constructed trees cover the children of the actual small-step transition.
Matcher and query cursors use earned structural debt; a completed answer
passes into its retained continuation before the next alternative resumes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {matcher : MatchingExecution}

abbrev Tree (environment : Environment) (outer : Goal)
    (task : Interpreted.Task matcher environment outer) :=
  Scheduler.TaskTree (expand environment outer) task

abbrev Continued (environment : Environment) (outer goal : Goal)
    (tail : Interpreted.Continuation matcher environment goal outer) :=
  ∀ result : Interpreted.Result matcher environment goal, Tree environment outer (.deliver result tail)

def doneTrees (environment : Environment) (goal : Goal) :
    Continued (matcher := matcher) environment goal goal (.done goal) :=
  fun _ => .branch .nil

def targetRequest {matcher : MatchingExecution} {environment : Environment} {outer : Goal}
    (frame : TargetMatchFrame environment outer matcher) : GeneralScopedMatchMachine.Request :=
  ⟨frame.call.context.rule, frame.call.context.spec, frame.call.context.bound.length,
    frame.call.context.site 1, [], frame.call.binders.length, frame.call.initial,
    frame.call.targetSchema, frame.target⟩

def rootRequest {matcher : MatchingExecution} {environment : Environment} {outer : Goal}
    (frame : RootMatchFrame environment outer matcher) : GeneralScopedMatchMachine.Request :=
  ⟨frame.rule, frame.spec, frame.bound.length, .left, [], 0, [], frame.rule.left, frame.source⟩

def treeTarget (cost : matcher.CursorCost) (environment : Environment) (outer : Goal)
    (frame : TargetMatchFrame environment outer matcher)
    (continued : Continued environment outer
      (.premise frame.depth frame.call.context frame.call.premise frame.call.initial) frame.tail) :
    Tree environment outer (.targetMatch frame) := by
  apply Scheduler.TaskTree.branch
  simp only [expand, expandTargetMatch]
  split
  · rename_i answer found
    have decrease := cost.consume frame.reachable found
    split
    · exact .cons (continued _)
        (.cons (treeTarget cost environment outer {frame with cursor := frame.cursor + 1} continued) .nil)
    · exact .cons
        (treeTarget cost environment outer {frame with cursor := frame.cursor + 1} continued) .nil
  · rename_i found
    split
    · exact .nil
    · rename_i pending
      have decrease := cost.tick frame.reachable found
        (Bool.eq_false_iff.mpr pending)
      exact .cons (treeTarget cost environment outer {frame with
        state := matcher.tick (targetRequest frame) frame.state
        reachable := matcher.tick_reachable frame.reachable} continued) .nil
termination_by cost.debt (targetRequest frame) frame.state frame.cursor
decreasing_by
  all_goals assumption

def treeQuery (cost : matcher.CursorCost) (environment : Environment) (outer : Goal) (depth : Nat) (request : Query.Request)
    (state : Query.State environment request matcher) (cursor : Nat)
    (tail : Interpreted.Continuation matcher environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (continued : Continued environment outer _ tail) :
    Tree environment outer (.query depth request state cursor tail) := by
  apply Scheduler.TaskTree.branch
  simp only [expand, expandQuery]
  split
  · rename_i answer found
    have decrease := queryDebt_cursor cost environment request state cursor answer found
    exact .cons (continued _)
      (.cons (treeQuery cost environment outer depth request state (cursor + 1) tail continued) .nil)
  · rename_i found
    split
    · exact .nil
    · rename_i pending
      have unfinished : state.agenda ≠ [] := by intro same; simp [same] at pending
      have decrease := queryDebt_tick cost environment request state cursor found unfinished
      exact .cons
        (treeQuery cost environment outer depth request (Query.tick environment request state) cursor tail continued) .nil
termination_by queryDebt cost environment request state cursor
decreasing_by
  all_goals assumption
abbrev RootBodies (environment : Environment) (outer : Goal)
    (frame : RootMatchFrame environment outer matcher) :=
  ∀ (answer : matcher.Answer)
    (valid : matcher.meaning.Matches (rootRequest frame) (matcher.trace answer) (matcher.assignment answer))
    (typed : TypedAssignment environment
      ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩ (matcher.assignment answer)),
    Tree environment outer (.evaluate
      (.premises frame.depth ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩
        frame.rule.premises (matcher.assignment answer))
      (.rootBody frame.depth frame.bound frame.type frame.source frame.index frame.rule frame.spec
        frame.declared frame.specified frame.admitted frame.sorted (matcher.trace answer)
        (matcher.assignment answer) valid typed frame.tail))

def treeRootMatch (cost : matcher.CursorCost) (environment : Environment) (outer : Goal)
    (frame : RootMatchFrame environment outer matcher) (bodies : RootBodies environment outer frame) :
    Tree environment outer (.rootMatch frame) := by
  apply Scheduler.TaskTree.branch
  simp only [expand, expandRootMatch, continueRootAnswer]
  split
  · rename_i answer found
    have decrease := cost.consume frame.reachable found
    split
    · rename_i checked
      exact .cons (bodies answer
          (matcher.answers_sound frame.reachable (List.mem_of_getElem? found))
          (checkTypedAssignment_sound checked))
        (.cons (treeRootMatch cost environment outer {frame with cursor := frame.cursor + 1} bodies) .nil)
    · exact .cons
        (treeRootMatch cost environment outer {frame with cursor := frame.cursor + 1} bodies) .nil
  · rename_i found
    split
    · exact .nil
    · rename_i pending
      have decrease := cost.tick frame.reachable found
        (Bool.eq_false_iff.mpr pending)
      exact .cons (treeRootMatch cost environment outer {frame with
        state := matcher.tick (rootRequest frame) frame.state
        reachable := matcher.tick_reachable frame.reachable} bodies) .nil
termination_by cost.debt (rootRequest frame) frame.state frame.cursor
decreasing_by
  all_goals assumption
#print axioms Tree
#print axioms Continued
#print axioms doneTrees
#print axioms treeTarget
#print axioms treeQuery
#print axioms RootBodies
#print axioms treeRootMatch

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
