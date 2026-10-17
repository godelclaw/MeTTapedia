import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics

/-!
# Typing survives premise execution and lexical restoration

Successful premises keep contextual captures correctly sorted in the caller's
complete bound context. A finite quantifier checks each local element binding,
runs its body, and restores only the parameter from the original assignment.
The other typed outputs remain available to later premises.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem mem_removeParameter {parameter : String} {assignment : Assignment}
    {entry : String × ContextualValue}
    (member : entry ∈ removeParameter parameter assignment) : entry ∈ assignment := by
  induction assignment with
  | nil => simp [removeParameter] at member
  | cons head tail inductionHypothesis =>
      rcases head with ⟨name, value⟩
      by_cases same : name = parameter
      · simp only [removeParameter, same, beq_self_eq_true, ite_true] at member
        exact List.mem_cons_of_mem _ (inductionHypothesis member)
      · simp only [removeParameter, show (name == parameter) = false by simp [same],
          Bool.false_eq_true, if_false, List.mem_cons] at member
        rcases member with equal | member
        · exact List.mem_cons.mpr (Or.inl equal)
        · exact List.mem_cons_of_mem _ (inductionHypothesis member)

theorem TypedAssignment.removeParameter {environment : Environment} {context : Context}
    {assignment : Assignment} (typed : TypedAssignment environment context assignment)
    (parameter : String) :
    TypedAssignment environment context (removeParameter parameter assignment) := by
  constructor
  · intro name value member
    exact typed.1 name value (mem_removeParameter member)
  · intro name value member
    exact typed.2 name value (mem_removeParameter member)

theorem TypedAssignment.restoreParameter {environment : Environment} {context : Context}
    {initial final : Assignment} (initialTyped : TypedAssignment environment context initial)
    (finalTyped : TypedAssignment environment context final) (parameter : String) :
    TypedAssignment environment context (restoreParameter parameter initial final) := by
  cases found : lookup initial parameter with
  | none =>
      simpa only [Mettapedia.OSLF.MeTTaIL.GeneralPremise.restoreParameter, found]
        using finalTyped.removeParameter parameter
  | some saved =>
      have member := ConditionalEquationExecution.lookup_assignment_member
        initial parameter saved found
      have remaining := finalTyped.removeParameter parameter
      simp only [Mettapedia.OSLF.MeTTaIL.GeneralPremise.restoreParameter, found]
      constructor
      · intro name value contains
        rcases List.mem_cons.mp contains with equal | contains
        · cases equal
          exact initialTyped.1 parameter saved member
        · exact remaining.1 name value contains
      · intro name value contains
        rcases List.mem_cons.mp contains with equal | contains
        · cases equal
          exact initialTyped.2 parameter saved member
        · exact remaining.2 name value contains

theorem TracedQuery.final_typed {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment}
    {rowIndex : Nat} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedQuery environment context relation arguments initial rowIndex final origins) :
    TypedAssignment environment context final := by
  cases held with
  | row _ _ _ _ typed => exact typed
  | dynamicRow _ _ _ _ _ _ _ typed => exact typed

mutual
 theorem PremiseHolds.typed {environment : Environment} {context : Context}
    {premise : Premise} {initial final : Assignment} {event : Event}
    (held : PremiseHolds environment context premise initial final event)
    (initialTyped : TypedAssignment environment context initial) :
    TypedAssignment environment context final :=
  match held with
  | .query query => query.final_typed
  | .freshness _ _ => initialTyped
  | .step _ _ _ _ typed => typed
  | .scopedStep _ _ _ typed => typed
  | .quantified _ elements => elements.typed initialTyped

 theorem PremisesHold.typed {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {events : List Event}
    (held : PremisesHold environment context premises initial final events)
    (initialTyped : TypedAssignment environment context initial) :
    TypedAssignment environment context final :=
  match held with
  | .nil => initialTyped
  | .cons head tail => tail.typed (head.typed initialTyped)

 theorem QuantifiedElements.typed {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List Event)}
    (held : QuantifiedElements environment context parameter body index elements initial final events)
    (initialTyped : TypedAssignment environment context initial) :
    TypedAssignment environment context final :=
  match held with
  | .nil => initialTyped
  | .cons localTyped head tail =>
      tail.typed (initialTyped.restoreParameter (head.typed localTyped) _)
end

theorem RootFiring.completed_typed {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (firing : RootFiring environment bound type source index trace captured completed history target) :
    ∃ rule spec, environment.language.rewrites[index]? = some rule ∧
      specification? environment index = some spec ∧
      TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ completed := by
  cases firing with
  | fire declared specified _ _ _ capturedTyped premises _ _ =>
      exact ⟨_, _, declared, specified, premises.typed capturedTyped⟩

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
