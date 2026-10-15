import Mettapedia.OSLF.NativeTypes.Modal.NativeFiringSubstitution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseTyping

/-!
# Identity reindexing of complete valid histories

Ambient metadata is obtained from actual independent assignment typing.
Nested child and quantified receipts retain their original ordered data.
The law applies to valid histories without assuming a contextual admission
profile merely to justify an identity operation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeHistorySubstitutionIdentity

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching

 theorem typed_assignment_identity {environment : Environment} {context : Context}
    {original : ScopedRuleMatching.Assignment}
    (typed : TypedAssignment environment context original) :
    NativeContextualSubstitution.assignment context.bound.length Pattern.bvar original = original := by
  apply NativeContextualSubstitution.assignment_identity
  intro name value member
  obtain ⟨_, _, _, _, _, ambient, _⟩ := typed.1 name value member
  exact ambient

theorem firing_assignment_identity {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List Event}
    (firing : RootFiring environment bound type source index trace captured completed history target) :
    NativeContextualSubstitution.assignment bound.length Pattern.bvar captured = captured ∧
      NativeContextualSubstitution.assignment bound.length Pattern.bvar completed = completed := by
  cases firing with
  | fire _ _ _ _ _ capturedTyped premises _ _ =>
      exact ⟨typed_assignment_identity capturedTyped, typed_assignment_identity (premises.typed capturedTyped)⟩

mutual
theorem premise_identity {environment : Environment} {context : Context} {premise : Premise}
    {initial final : ScopedRuleMatching.Assignment} {history : Event}
    (held : PremiseHolds environment context premise initial final history) :
    NativeEventSubstitution.event context.bound context.bound Pattern.bvar history = history :=
  match held with
  | .query _ => by simp only [NativeEventSubstitution.event]
  | .freshness _ _ => by simp only [NativeEventSubstitution.event, ContextSubstitution.substitute_id]
  | .step _ _ firing _ _ => by
      obtain ⟨capturedSame, completedSame⟩ := firing_assignment_identity firing
      simp only [NativeEventSubstitution.child_unscoped, ContextSubstitution.substitute_id,
        capturedSame, completedSame, firing_identity firing]
  | .scopedStep _ firing _ _ => by
      obtain ⟨capturedSame, completedSame⟩ := firing_assignment_identity firing
      simp only [NativeEventSubstitution.child_scoped, ContextSubstitution.lift_identity,
        ContextSubstitution.substitute_id, capturedSame, completedSame, firing_identity firing]
  | .quantified _ elements => by
      simp only [NativeEventSubstitution.event, quantified_identity elements]
termination_by structural held

theorem premises_identity {environment : Environment} {context : Context} {premises : List Premise}
    {initial final : ScopedRuleMatching.Assignment} {history : List Event}
    (held : PremisesHold environment context premises initial final history) :
    NativeEventSubstitution.events context.bound context.bound Pattern.bvar history = history :=
  match held with
  | .nil => by simp only [NativeEventSubstitution.events]
  | .cons head tail => by
      have headSame := premise_identity head
      have tailSame := premises_identity tail
      simp only [Context.next] at tailSame
      simp only [NativeEventSubstitution.events, headSame, tailSame]
termination_by structural held

theorem quantified_identity {environment : Environment} {context : Context} {parameter : String}
    {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : ScopedRuleMatching.Assignment} {history : List (Nat × Pattern × List Event)}
    (held : QuantifiedElements environment context parameter body index elements initial final history) :
    NativeEventSubstitution.quantified context.bound context.bound Pattern.bvar history = history :=
  match held with
  | .nil => by simp only [NativeEventSubstitution.quantified]
  | .cons _ head tail => by
      have headSame := premise_identity head
      simp only [Context.quantified] at headSame
      simp only [NativeEventSubstitution.quantified, NativeEventSubstitution.events,
        ContextSubstitution.substitute_id, headSame, quantified_identity tail]
termination_by structural held

theorem firing_identity {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List Event}
    (firing : RootFiring environment bound type source index trace captured completed history target) :
    NativeEventSubstitution.events bound bound Pattern.bvar history = history :=
  match firing with
  | .fire _ _ _ _ _ _ premises _ _ => premises_identity premises
termination_by structural firing
end

end Mettapedia.OSLF.NativeTypes.Modal.NativeHistorySubstitutionIdentity
