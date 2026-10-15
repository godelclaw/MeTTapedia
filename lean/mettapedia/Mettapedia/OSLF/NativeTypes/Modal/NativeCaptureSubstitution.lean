import Mettapedia.OSLF.NativeTypes.Modal.NativeRecoverySubstitution

/-!
# Forward transport of actual scoped capture computations

The original repeated-variable comparison is retained. Ambient substitution
can identify previously distinct values, so the theorem is forward
preservation, not reflection. Capture and residual collection capture use
their actual authored dependency and occurrence-spine decoders.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeCaptureSubstitution

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching

theorem assign_substitutes {initial final : Assignment} {name : String} {original : ContextualValue}
    (accepted : assign initial name original = some final)
    (target : Nat) (substitution : ContextSubstitution.Assignment) :
    assign (NativeContextualSubstitution.assignment target substitution initial) name
      (NativeContextualSubstitution.value target substitution original) =
      some (NativeContextualSubstitution.assignment target substitution final) := by
  cases stored : lookup initial name with
  | none =>
      have finalSame : final = (name, original) :: initial := by
        simp only [assign, stored] at accepted
        exact (Option.some.inj accepted).symm
      rw [finalSame]
      simp only [assign, NativeContextualSubstitution.lookup_assignment, stored, Option.map_none]
      rfl
  | some prior =>
      have priorSame : prior = original := by
        by_contra different
        simp [assign, stored, different] at accepted
      subst prior
      have finalSame : final = initial := by
        simp only [assign, stored, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at accepted
        exact accepted.symm
      subst final
      simp only [assign, NativeContextualSubstitution.lookup_assignment, stored, Option.map_some,
        beq_self_eq_true, ↓reduceIte]

theorem capture_substitutes {rule : RewriteRule} {spec : RuleBindingSpec}
    {source target depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {name : String} {actual : Pattern}
    (accepted : capture? rule spec source depth site path initial name actual = some final)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    capture? rule spec target depth site path
      (NativeContextualSubstitution.assignment target substitution initial) name
      (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution) actual) =
      some (NativeContextualSubstitution.assignment target substitution final) := by
  unfold capture? at accepted
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨dependencies, declared, arguments, located, original, recovered, assigned⟩ := accepted
  have newRecovery := NativeRecoverySubstitution.recovery_substitutes recovered substitution boundScoped
  have newAssignment := assign_substitutes assigned target substitution
  simp only [capture?, Option.bind_eq_bind, declared, located, newRecovery, newAssignment, Option.bind_some]

theorem captureRest_substitutes {rule : RewriteRule} {spec : RuleBindingSpec}
    {source target depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {name : String} {kind : CollType} {elements : List Pattern}
    (accepted : captureRest? rule spec source depth site path initial name kind elements = some final)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    captureRest? rule spec target depth site path
      (NativeContextualSubstitution.assignment target substitution initial) name kind
      (elements.map (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution))) =
      some (NativeContextualSubstitution.assignment target substitution final) := by
  simpa only [captureRest?, ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map] using
    capture_substitutes accepted substitution boundScoped

end Mettapedia.OSLF.NativeTypes.Modal.NativeCaptureSubstitution
