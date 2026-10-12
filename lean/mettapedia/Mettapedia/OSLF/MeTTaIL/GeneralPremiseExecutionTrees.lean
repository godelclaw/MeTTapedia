import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseMachineDebt
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFiniteWork

/-!
# Finite trees for actual premise continuations

The constructed trees cover the children of the actual small-step transition.
Matcher and query cursors use earned structural debt; a completed answer
passes into its retained continuation before the next alternative resumes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

abbrev Tree (environment : Environment) (outer : Goal) (task : Task environment outer) :=
  Scheduler.TaskTree (expand environment outer) task

abbrev Continued (environment : Environment) (outer goal : Goal)
    (tail : Continuation environment goal outer) :=
  ∀ result : Result environment goal, Tree environment outer (.deliver result tail)

def doneTrees (environment : Environment) (goal : Goal) :
    Continued environment goal goal (.done goal) :=
  fun _ => .branch .nil

def targetRequest {environment : Environment} {outer : Goal}
    (frame : TargetMatchFrame environment outer) : GeneralScopedMatchMachine.Request :=
  ⟨frame.call.context.rule, frame.call.context.spec, frame.call.context.bound.length,
    frame.call.context.site 1, [], frame.call.binders.length, frame.call.initial,
    frame.call.targetSchema, frame.target⟩

def rootRequest {environment : Environment} {outer : Goal}
    (frame : RootMatchFrame environment outer) : GeneralScopedMatchMachine.Request :=
  ⟨frame.rule, frame.spec, frame.bound.length, .left, [], 0, [], frame.rule.left, frame.source⟩

def treeTarget (environment : Environment) (outer : Goal)
    (frame : TargetMatchFrame environment outer)
    (continued : Continued environment outer
      (.premise frame.call.context frame.call.premise frame.call.initial) frame.tail) :
    Tree environment outer (.targetMatch frame) := by
  apply Scheduler.TaskTree.branch
  simp only [expand, expandTargetMatch]
  split
  · rename_i answer found
    have decrease := matcherDebt_cursor (targetRequest frame) frame.state frame.cursor answer found
    split
    · exact .cons (continued _)
        (.cons (treeTarget environment outer {frame with cursor := frame.cursor + 1} continued) .nil)
    · exact .cons
        (treeTarget environment outer {frame with cursor := frame.cursor + 1} continued) .nil
  · rename_i found
    split
    · exact .nil
    · rename_i pending
      have decrease := matcherDebt_tick (targetRequest frame) frame.state frame.cursor found
        (Bool.eq_false_iff.mpr pending)
      exact .cons (treeTarget environment outer {frame with
        state := GeneralScopedMatchMachine.tick (targetRequest frame) frame.state
        reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable} continued) .nil
termination_by matcherDebt (targetRequest frame) frame.state frame.cursor
decreasing_by
  all_goals assumption

def treeQuery (environment : Environment) (outer : Goal) (request : Query.Request)
    (state : Query.State environment request) (cursor : Nat)
    (tail : Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (continued : Continued environment outer _ tail) :
    Tree environment outer (.query request state cursor tail) := by
  apply Scheduler.TaskTree.branch
  simp only [expand, expandQuery]
  split
  · rename_i answer found
    have decrease := queryDebt_cursor environment request state cursor answer found
    exact .cons (continued _)
      (.cons (treeQuery environment outer request state (cursor + 1) tail continued) .nil)
  · rename_i found
    split
    · exact .nil
    · rename_i pending
      have unfinished : state.agenda ≠ [] := by intro same; simp [same] at pending
      have decrease := queryDebt_tick environment request state cursor found unfinished
      exact .cons
        (treeQuery environment outer request (Query.tick environment request state) cursor tail continued) .nil
termination_by queryDebt environment request state cursor
decreasing_by
  all_goals assumption

abbrev RootBodies (environment : Environment) (outer : Goal)
    (frame : RootMatchFrame environment outer) :=
  ∀ (answer : GeneralScopedMatchMachine.Answer)
    (valid : GeneralScopedMatchMachine.Answer.Valid (rootRequest frame) answer)
    (typed : TypedAssignment environment
      ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩ answer.assignment),
    Tree environment outer (.evaluate
      (.premises ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩
        frame.rule.premises answer.assignment)
      (.rootBody frame.bound frame.type frame.source frame.index frame.rule frame.spec
        frame.declared frame.specified frame.admitted frame.sorted answer.trace answer.assignment
        valid typed frame.tail))

def treeRootMatch (environment : Environment) (outer : Goal)
    (frame : RootMatchFrame environment outer) (bodies : RootBodies environment outer frame) :
    Tree environment outer (.rootMatch frame) := by
  apply Scheduler.TaskTree.branch
  simp only [expand, expandRootMatch]
  split
  · rename_i answer found
    have decrease := matcherDebt_cursor (rootRequest frame) frame.state frame.cursor answer found
    split
    · exact .cons (bodies _ _ _)
        (.cons (treeRootMatch environment outer {frame with cursor := frame.cursor + 1} bodies) .nil)
    · exact .cons
        (treeRootMatch environment outer {frame with cursor := frame.cursor + 1} bodies) .nil
  · rename_i found
    split
    · exact .nil
    · rename_i pending
      have decrease := matcherDebt_tick (rootRequest frame) frame.state frame.cursor found
        (Bool.eq_false_iff.mpr pending)
      exact .cons (treeRootMatch environment outer {frame with
        state := GeneralScopedMatchMachine.tick (rootRequest frame) frame.state
        reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable} bodies) .nil
termination_by matcherDebt (rootRequest frame) frame.state frame.cursor
decreasing_by
  all_goals assumption

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution
