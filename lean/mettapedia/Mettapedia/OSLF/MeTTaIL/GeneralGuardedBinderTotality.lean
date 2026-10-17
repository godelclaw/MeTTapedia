import Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderQueryTotality
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseResolvedTrees
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobResolution
import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobResolution

/-!
# Total primitive work in the original guarded binder language

The actual guard-query machine is retained inside the continuation tree.
Its provider cursors either accept or reject each input comparison. The
process dependency is projected through its complete Name spine; neither
orientation nor the two declared consume rules uses a zero-dependency
approximation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderExecution

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open EquationFrontierBinderProfile GeneralPremise GeneralPremise.Execution
open Mettapedia.GSLT.LanguageDef.WellSorted

def resolved_guard_query {allowed : List Token} {choice : Choice} {bound : List TypeExpr}
    {initial : Assignment}
    (typed : TypedAssignment (environment allowed) (choice.context bound) initial)
    (names : BoundNames initial ["P", "Q"])
    (outer : Goal) (state : Query.State (environment allowed) (query choice bound initial))
    (safe : QuerySafe allowed choice bound initial state) (cursor : Nat)
    (tail : Continuation (environment allowed)
      (.premise (choice.context bound) (.relationQuery "allow" [.fvar "Q"]) initial) outer)
    (continued : ResolvedContinued (environment allowed) outer _ tail) :
    ResolvedTree (environment allowed) outer (.query (query choice bound initial) state cursor tail) := by
  apply ResolvedTree.branch
  · simp only [expand, expandQuery]
    split
    · rfl
    · split
      · simp only [safe.1, List.map_nil]
      · rfl
  · simp only [expand, expandQuery]
    split
    · rename_i answer found
      have decrease := queryDebt_cursor (environment allowed) (query choice bound initial)
        state cursor answer found
      exact .cons (continued _)
        (.cons (resolved_guard_query typed names outer state safe (cursor + 1) tail continued) (.nil _ _))
    · rename_i found
      split
      · exact .nil _ _
      · rename_i pending
        have unfinished : state.agenda ≠ [] := by intro same; simp [same] at pending
        have decrease := queryDebt_tick (environment allowed) (query choice bound initial)
          state cursor found unfinished
        exact .cons (resolved_guard_query typed names outer
          (Query.tick (environment allowed) (query choice bound initial) state)
          (query_tick_safe typed names state safe) cursor tail continued) (.nil _ _)
termination_by queryDebt (environment allowed) (query choice bound initial) state cursor
decreasing_by all_goals assumption

theorem query_assignment_unchanged {allowed : List Token} {choice : Choice} {bound : List TypeExpr}
    {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (valid : TracedQuery (environment allowed) (choice.context bound) "allow" [.fvar "Q"]
      initial rowIndex final origins) : final = initial := by
  cases valid with
  | @row rowIndex row signature final origins selected declared rowTyped arguments finalTyped =>
      have same : signature = allowSignature :=
        Option.some.inj (declared.symm.trans (query_signature allowed choice bound initial))
      subst signature
      obtain ⟨token, values⟩ := provider_row_values selected
      rw [values] at arguments
      cases arguments with
      | input interpreted remaining =>
          cases remaining
          rfl
  | dynamicRow registered _ _ _ _ _ _ _ =>
      exact False.elim (query_unregistered allowed choice bound initial registered)

theorem guard_premise_assignment_unchanged {allowed : List Token} {choice : Choice} {bound : List TypeExpr}
    {initial final : Assignment} {event : Event}
    (valid : PremiseHolds (environment allowed) (choice.context bound)
      (.relationQuery "allow" [.fvar "Q"]) initial final event) : final = initial := by
  cases valid with
  | query held => exact query_assignment_unchanged held

theorem guard_premises_assignment_unchanged {allowed : List Token} {choice : Choice} {bound : List TypeExpr}
    {initial final : Assignment} {events : List Event}
    (valid : PremisesHold (environment allowed) (choice.context bound)
      [.relationQuery "allow" [.fvar "Q"]] initial final events) : final = initial := by
  cases valid with
  | cons first remaining =>
      cases remaining
      exact guard_premise_assignment_unchanged first

def resolved_guard_premises {allowed : List Token} {choice : Choice} {bound : List TypeExpr}
    {initial : Assignment}
    (typed : TypedAssignment (environment allowed) (choice.context bound) initial)
    (names : BoundNames initial ["P", "Q"])
    (outer : Goal)
    (tail : Continuation (environment allowed)
      (.premises (choice.context bound) [.relationQuery "allow" [.fvar "Q"]] initial) outer)
    (continued : ResolvedContinued (environment allowed) outer _ tail) :
    ResolvedTree (environment allowed) outer
      (.evaluate (.premises (choice.context bound) [.relationQuery "allow" [.fvar "Q"]] initial) tail) := by
  refine .branch rfl (.cons ?_ (.nil _ _))
  refine .branch rfl (.cons ?_ (.nil _ _))
  apply resolved_guard_query typed names outer _ (query_start_safe _ _ _ _) 0 _
  intro result
  cases result with
  | premise assignment event valid =>
      refine .branch rfl (.cons ?_ (.nil _ _))
      refine .branch rfl (.cons ?_ (.nil _ _))
      exact .branch rfl (.cons (continued (.premises assignment [event] (.cons valid .nil))) (.nil _ _))

def resolved_authored_premises {allowed : List Token} {choice : Choice} {bound : List TypeExpr}
    {initial : Assignment}
    (typed : TypedAssignment (environment allowed) (choice.context bound) initial)
    (names : BoundNames initial ["P", "Q"])
    (outer : Goal)
    (tail : Continuation (environment allowed)
      (.premises (choice.context bound) choice.rule.premises initial) outer)
    (continued : ResolvedContinued (environment allowed) outer _ tail) :
    ResolvedTree (environment allowed) outer
      (.evaluate (.premises (choice.context bound) choice.rule.premises initial) tail) := by
  cases choice <;> exact resolved_guard_premises typed names outer tail continued

theorem authored_premises_resolved {allowed : List Token} {choice : Choice} {bound : List TypeExpr}
    {initial : Assignment}
    (typed : TypedAssignment (environment allowed) (choice.context bound) initial)
    (names : BoundNames initial ["P", "Q"]) :
    (Execution.finish (environment allowed)
      (.premises (choice.context bound) choice.rule.premises initial)).unresolved = [] :=
  finish_resolved_of_tree _ _ (resolved_authored_premises typed names _ _ (resolvedDone _ _))

def resolved_guard_root_body {allowed : List Token} {choice : Choice} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured : Assignment}
    (declared : (environment allowed).language.rewrites[(choice.context bound).ruleIndex]? = some choice.rule)
    (specified : specification? (environment allowed) (choice.context bound).ruleIndex = some choice.spec)
    (admitted : admittedFor choice.rule choice.spec = true)
    (sorted : OpenPatternWellSorted (environment allowed).language (environment allowed).free bound type source)
    (matching : GeneralScopedMatchMachine.TracedMatches choice.rule choice.spec bound.length .left [] 0 []
      choice.rule.left source trace captured)
    (typed : TypedAssignment (environment allowed) (choice.context bound) captured)
    (outer : Goal)
    (tail : Continuation (environment allowed)
      (.root bound type source (choice.context bound).ruleIndex) outer)
    (continued : ResolvedContinued (environment allowed) outer _ tail) :
    ResolvedTree (environment allowed) outer
      (.evaluate (.premises (choice.context bound) choice.rule.premises captured)
        (.rootBody bound type source (choice.context bound).ruleIndex choice.rule choice.spec
          declared specified admitted sorted trace captured matching typed tail)) := by
  have names := matching_names matching.matching
  apply resolved_authored_premises typed names outer _
  intro result
  cases result with
  | premises completed events valid =>
      have same : completed = captured := guard_premises_assignment_unchanged
        (by simpa only [choice.premises] using valid)
      subst completed
      have projected : (reductWith?
          (ScopedReflectiveExecution.binderOperation (environment allowed).reflection choice.rule)
          choice.rule choice.spec bound.length captured).isSome = true :=
        Option.isSome_iff_exists.mpr (reduct_total typed names _)
      apply ResolvedTree.branch
      · dsimp only [Choice.context]
        simp only [expand, delivered]
        split
        rename_i actual current history held same
        cases same
        split
        · rename_i absent
          rw [absent] at projected
          cases projected
        · split <;> rfl
      · dsimp only [Choice.context]
        simp only [expand, delivered]
        split
        rename_i actual current history held same
        cases same
        split
        · rename_i absent
          rw [absent] at projected
          cases projected
        · split
          · exact .cons (continued _) (.nil _ _)
          · exact .nil _ _

#print axioms authored_premises_resolved

end Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderExecution
