import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryTotality
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFinishReadout
import Mettapedia.OSLF.Framework.GeneralFiniteWorkUniqueness

/-!
# Actual continuation trees with resolved primitive work

Resolved trees contain every child produced by the executable transition.
Their cleanliness is proved from admitted projections and retained query
invariants. Uniqueness of actual expansion trees connects these proofs to
the ordinary terminating executor, without replacing its work or answers.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

structure ResolvedTree (environment : Environment) (outer : Goal)
    (task : Task environment outer) where
  tree : Tree environment outer task
  resolved : tree.obligations = []

structure ResolvedForest (environment : Environment) (outer : Goal)
    (tasks : List (Task environment outer)) where
  forest : Scheduler.TaskForest (expand environment outer) tasks
  resolved : forest.obligations = []

def ResolvedForest.nil (environment : Environment) (outer : Goal) :
    ResolvedForest environment outer [] := ⟨.nil, rfl⟩

def ResolvedForest.cons {environment : Environment} {outer : Goal}
    {task : Task environment outer} {tasks : List (Task environment outer)}
    (head : ResolvedTree environment outer task) (tail : ResolvedForest environment outer tasks) :
    ResolvedForest environment outer (task :: tasks) :=
  ⟨.cons head.tree tail.forest,
    by simp only [Scheduler.TaskForest.obligations, head.resolved, tail.resolved, List.nil_append]⟩

def ResolvedTree.branch {environment : Environment} {outer : Goal} {task : Task environment outer}
    (clear : (expand environment outer task).unresolved = [])
    (children : ResolvedForest environment outer (expand environment outer task).tasks) :
    ResolvedTree environment outer task :=
  ⟨.branch children.forest,
    by simp only [Scheduler.TaskTree.obligations, clear, children.resolved, List.nil_append]⟩

abbrev ResolvedContinued (environment : Environment) (outer goal : Goal)
    (tail : Continuation environment goal outer) :=
  ∀ result : Result environment goal, ResolvedTree environment outer (.deliver result tail)

def resolvedDone (environment : Environment) (goal : Goal) :
    ResolvedContinued environment goal goal (.done goal) :=
  fun _ => .branch rfl (.nil _ _)

theorem finish_resolved_of_tree (environment : Environment) (goal : Goal)
    (resolved : ResolvedTree environment goal (.evaluate goal (.done goal))) :
    (finish environment goal).unresolved = [] := by
  rw [finish_obligations, (treeStart environment goal).unique resolved.tree]
  exact resolved.resolved

def resolvedTarget (environment : Environment) (outer : Goal)
    (frame : TargetMatchFrame environment outer)
    (continued : ResolvedContinued environment outer
      (.premise frame.call.context frame.call.premise frame.call.initial) frame.tail) :
    ResolvedTree environment outer (.targetMatch frame) := by
  apply ResolvedTree.branch
  · simp only [expand, expandTargetMatch]
    split
    · split <;> rfl
    · split <;> rfl
  · simp only [expand, expandTargetMatch]
    split
    · rename_i answer found
      have decrease := matcherDebt_cursor (targetRequest frame) frame.state frame.cursor answer found
      split
      · exact .cons (continued _)
          (.cons (resolvedTarget environment outer {frame with cursor := frame.cursor + 1} continued) (.nil _ _))
      · exact .cons
          (resolvedTarget environment outer {frame with cursor := frame.cursor + 1} continued) (.nil _ _)
    · rename_i found
      split
      · exact .nil _ _
      · rename_i pending
        have decrease := matcherDebt_tick (targetRequest frame) frame.state frame.cursor found
          (Bool.eq_false_iff.mpr pending)
        exact .cons (resolvedTarget environment outer {frame with
          state := GeneralScopedMatchMachine.tick (targetRequest frame) frame.state
          reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable} continued) (.nil _ _)
termination_by matcherDebt (targetRequest frame) frame.state frame.cursor
decreasing_by all_goals assumption

def resolvedQuery (environment : Environment) (outer : Goal) (request : Query.Request)
    (admission : Query.InputAdmission environment request)
    (state : Query.State environment request) (ready : Query.StateReady admission state) (cursor : Nat)
    (tail : Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (continued : ResolvedContinued environment outer _ tail) :
    ResolvedTree environment outer (.query request state cursor tail) := by
  apply ResolvedTree.branch
  · simp only [expand, expandQuery]
    split
    · rfl
    · split
      · simp only [ready.1, List.map_nil]
      · rfl
  · simp only [expand, expandQuery]
    split
    · rename_i answer found
      have decrease := queryDebt_cursor
        _root_.Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.ordinaryCursorCost
        environment request state cursor answer found
      exact .cons (continued _)
        (.cons (resolvedQuery environment outer request admission state ready (cursor + 1)
          tail continued) (.nil _ _))
    · rename_i found
      split
      · exact .nil _ _
      · rename_i pending
        have unfinished : state.agenda ≠ [] := by intro same; simp [same] at pending
        have decrease := queryDebt_tick
          _root_.Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.ordinaryCursorCost
          environment request state cursor found unfinished
        exact .cons (resolvedQuery environment outer request admission
          (Query.tick environment request state) (Query.tick_ready admission ready) cursor tail continued) (.nil _ _)
termination_by queryDebt
  _root_.Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.ordinaryCursorCost environment request state cursor
decreasing_by all_goals assumption

abbrev ResolvedRootBodies (environment : Environment) (outer : Goal)
    (frame : RootMatchFrame environment outer) :=
  ∀ (answer : GeneralScopedMatchMachine.Answer)
    (valid : GeneralScopedMatchMachine.Answer.Valid (rootRequest frame) answer)
    (typed : TypedAssignment environment
      ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩ answer.assignment),
    ResolvedTree environment outer (.evaluate
      (.premises ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩
        frame.rule.premises answer.assignment)
      (.rootBody frame.bound frame.type frame.source frame.index frame.rule frame.spec
        frame.declared frame.specified frame.admitted frame.sorted answer.trace answer.assignment
        valid typed frame.tail))

def resolvedRootMatch (environment : Environment) (outer : Goal)
    (frame : RootMatchFrame environment outer) (bodies : ResolvedRootBodies environment outer frame) :
    ResolvedTree environment outer (.rootMatch frame) := by
  apply ResolvedTree.branch
  · simp only [expand, expandRootMatch]
    split
    · split <;> rfl
    · split <;> rfl
  · simp only [expand, expandRootMatch]
    split
    · rename_i answer found
      have decrease := matcherDebt_cursor (rootRequest frame) frame.state frame.cursor answer found
      split
      · exact .cons (bodies _ _ _)
          (.cons (resolvedRootMatch environment outer {frame with cursor := frame.cursor + 1} bodies) (.nil _ _))
      · exact .cons
          (resolvedRootMatch environment outer {frame with cursor := frame.cursor + 1} bodies) (.nil _ _)
    · rename_i found
      split
      · exact .nil _ _
      · rename_i pending
        have decrease := matcherDebt_tick (rootRequest frame) frame.state frame.cursor found
          (Bool.eq_false_iff.mpr pending)
        exact .cons (resolvedRootMatch environment outer {frame with
          state := GeneralScopedMatchMachine.tick (rootRequest frame) frame.state
          reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable} bodies) (.nil _ _)
termination_by matcherDebt (rootRequest frame) frame.state frame.cursor
decreasing_by all_goals assumption

def resolvedScan (environment : Environment) (outer : Goal) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (limit cursor : Nat)
    (tail : Continuation environment (.steps bound type source limit) outer)
    (continued : ResolvedContinued environment outer _ tail)
    (roots : ∀ index, index < limit →
      ∀ childTail : Continuation environment (.root bound type source index) outer,
        ResolvedContinued environment outer _ childTail →
        ResolvedTree environment outer (.evaluate (.root bound type source index) childTail)) :
    ResolvedTree environment outer (.scanChildren bound type source limit cursor tail) := by
  apply ResolvedTree.branch
  · simp only [expand]
    split <;> rfl
  · simp only [expand]
    split
    · rename_i earlier
      have decrease : limit - (cursor + 1) < limit - cursor := by omega
      refine .cons (roots cursor earlier _ ?_)
        (.cons (resolvedScan environment outer bound type source limit (cursor + 1) tail continued roots) (.nil _ _))
      intro result
      cases result with
      | root trace captured completed history target valid =>
        exact .branch rfl (.cons (continued _) (.nil _ _))
    · exact .nil _ _
termination_by limit - cursor
decreasing_by assumption

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution
