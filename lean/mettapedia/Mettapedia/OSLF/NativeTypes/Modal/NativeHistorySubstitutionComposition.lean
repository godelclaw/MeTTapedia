import Mettapedia.OSLF.NativeTypes.Modal.NativeHistorySubstitutionIdentity

/-!
# Composition of contextual actions on complete operational histories

The laws retain every nested receipt rather than compare only endpoint
sets. Original child context evidence determines the local binder prefix;
the original directed firing justifies each recursive history comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeHistorySubstitutionComposition

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching

mutual
theorem premise_composes {environment : Environment} {context : Context} {premise : Premise}
    {initial final : ScopedRuleMatching.Assignment} {history : Event}
    (held : PremiseHolds environment context premise initial final history)
    (middle target : List TypeExpr) (first second : ContextSubstitution.Assignment) :
    NativeEventSubstitution.event middle target second
      (NativeEventSubstitution.event context.bound middle first history) =
      NativeEventSubstitution.event context.bound target
        (fun index => ContextSubstitution.substitute second (first index)) history :=
  match held with
  | .query _ => by simp only [NativeEventSubstitution.event]
  | .freshness _ _ => by simp only [NativeEventSubstitution.event, ContextSubstitution.substitute_comp]
  | .step _ _ firing _ _ => by
      simp only [NativeEventSubstitution.child_unscoped, ContextSubstitution.substitute_comp,
        NativeContextualSubstitution.assignment_composition, firing_composes firing middle target first second]
  | .scopedStep (step := step) _ firing _ _ => by
      have histories := firing_composes firing (step.binders ++ middle) (step.binders ++ target)
        (ContextSubstitution.lift step.binders.length first) (ContextSubstitution.lift step.binders.length second)
      simp only [ContextSubstitution.lift_comp] at histories
      simp only [NativeEventSubstitution.child_scoped, ContextSubstitution.substitute_comp,
        NativeContextualSubstitution.assignment_composition, ContextSubstitution.lift_comp, histories]
  | .quantified _ elements => by
      simp only [NativeEventSubstitution.event, quantified_composes elements middle target first second]
termination_by structural held

theorem premises_compose {environment : Environment} {context : Context} {premises : List Premise}
    {initial final : ScopedRuleMatching.Assignment} {history : List Event}
    (held : PremisesHold environment context premises initial final history)
    (middle target : List TypeExpr) (first second : ContextSubstitution.Assignment) :
    NativeEventSubstitution.events middle target second
      (NativeEventSubstitution.events context.bound middle first history) =
      NativeEventSubstitution.events context.bound target
        (fun index => ContextSubstitution.substitute second (first index)) history :=
  match held with
  | .nil => by simp only [NativeEventSubstitution.events]
  | .cons head tail => by
      have headSquare := premise_composes head middle target first second
      have tailSquare := premises_compose tail middle target first second
      simp only [Context.next] at tailSquare
      simp only [NativeEventSubstitution.events, headSquare, tailSquare]
termination_by structural held

theorem quantified_composes {environment : Environment} {context : Context} {parameter : String}
    {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : ScopedRuleMatching.Assignment} {history : List (Nat × Pattern × List Event)}
    (held : QuantifiedElements environment context parameter body index elements initial final history)
    (middle target : List TypeExpr) (first second : ContextSubstitution.Assignment) :
    NativeEventSubstitution.quantified middle target second
      (NativeEventSubstitution.quantified context.bound middle first history) =
      NativeEventSubstitution.quantified context.bound target
        (fun index => ContextSubstitution.substitute second (first index)) history :=
  match held with
  | .nil => by simp only [NativeEventSubstitution.quantified]
  | .cons _ head tail => by
      have headSquare := premise_composes head middle target first second
      simp only [Context.quantified] at headSquare
      simp only [NativeEventSubstitution.quantified, NativeEventSubstitution.events,
        ContextSubstitution.substitute_comp, headSquare, quantified_composes tail middle target first second]
termination_by structural held

theorem firing_composes {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source result : Pattern} {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List Event}
    (firing : RootFiring environment bound type source index trace captured completed history result)
    (middle target : List TypeExpr) (first second : ContextSubstitution.Assignment) :
    NativeEventSubstitution.events middle target second
      (NativeEventSubstitution.events bound middle first history) =
      NativeEventSubstitution.events bound target
        (fun index => ContextSubstitution.substitute second (first index)) history :=
  match firing with
  | .fire _ _ _ _ _ _ premises _ _ => premises_compose premises middle target first second
termination_by structural firing
end

end Mettapedia.OSLF.NativeTypes.Modal.NativeHistorySubstitutionComposition
