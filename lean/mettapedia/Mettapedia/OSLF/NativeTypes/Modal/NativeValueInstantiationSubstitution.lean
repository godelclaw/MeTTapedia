import Mettapedia.OSLF.NativeTypes.Modal.NativeOccurrenceSubstitution

/-!
# Ambient transport of the actual checked occurrence interpreter

The interpreter's scope checks are discharged after substitution from the
independent well-scoped assignment law. This is a theorem about successful
`instantiateValue?` computations, including their retained contextual value,
rather than an equality asserted between unrelated schema interpreters.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeValueInstantiationSubstitution

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

theorem instantiated_readout {original : ContextualValue} {ambient depth : Nat}
    {arguments : List Pattern} {actual : Pattern}
    (accepted : instantiateValue? original ambient depth arguments = some actual) :
    original.ambient = ambient ∧ arguments.length = original.dependencies.length ∧
      original.body.isWellScopedAt (original.dependencies.length + ambient) = true ∧
      actual = ContextSubstitution.substitute
        (occurrenceAssignment original.dependencies.length depth arguments) original.body := by
  unfold instantiateValue? at accepted
  split at accepted <;> try contradiction
  rename_i correctAmbient
  split at accepted <;> try contradiction
  rename_i correctArity
  split at accepted <;> try contradiction
  rename_i bodyScoped
  split at accepted <;> try contradiction
  dsimp only at accepted
  split at accepted <;> try contradiction
  have ambientSame : original.ambient = ambient := by
    by_contra unequal
    exact correctAmbient (bne_iff_ne.mpr unequal)
  have aritySame : arguments.length = original.dependencies.length := by
    by_contra unequal
    exact correctArity (bne_iff_ne.mpr unequal)
  have scope : original.body.isWellScopedAt (original.dependencies.length + ambient) = true := by
    cases actualScope : original.body.isWellScopedAt (original.dependencies.length + ambient) <;>
      simp_all
  exact ⟨ambientSame, aritySame, scope, (Option.some.inj accepted).symm⟩

theorem instantiated_from_checks {original : ContextualValue} {ambient depth : Nat}
    {arguments : List Pattern}
    (ambientSame : original.ambient = ambient)
    (aritySame : arguments.length = original.dependencies.length)
    (bodyScoped : original.body.isWellScopedAt (original.dependencies.length + ambient) = true)
    (argumentsScoped : arguments.all (fun argument => argument.isWellScopedAt (depth + ambient)) = true)
    (resultScoped :
      (ContextSubstitution.substitute (occurrenceAssignment original.dependencies.length depth arguments)
        original.body).isWellScopedAt (depth + ambient) = true) :
    instantiateValue? original ambient depth arguments =
      some (ContextSubstitution.substitute
        (occurrenceAssignment original.dependencies.length depth arguments) original.body) := by
  simp [instantiateValue?, ambientSame, aritySame, bodyScoped, argumentsScoped, resultScoped]

theorem successful_instantiation_substitutes {original : ContextualValue} {source target depth : Nat}
    {arguments : List Pattern} {actual : Pattern}
    (accepted : instantiateValue? original source depth arguments = some actual)
    (localScopes : ∀ argument ∈ arguments, argument.isWellScopedAt depth = true)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    instantiateValue? (NativeContextualSubstitution.value target substitution original) target depth arguments =
      some (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution) actual) := by
  obtain ⟨_, arity, bodyScope, actualValue⟩ := instantiated_readout accepted
  have square := NativeOccurrenceSubstitution.interpreted_body_square arity localScopes substitution original.body
  have resultScope :
      (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution) actual).isWellScopedAt
        (depth + target) = true := by
    exact ContextSubstitution.substitute_wellScoped
      (by simpa only [Nat.add_comm] using boundScoped.lift depth) (instantiateValue?_scoped _ _ _ _ _ accepted)
  have newBodyScope :
      (NativeContextualSubstitution.value target substitution original).body.isWellScopedAt
        (original.dependencies.length + target) = true := by
    exact ContextSubstitution.substitute_wellScoped
      (by simpa only [Nat.add_comm] using boundScoped.lift original.dependencies.length) bodyScope
  have argumentScopes : arguments.all (fun argument => argument.isWellScopedAt (depth + target)) = true := by
    apply List.all_eq_true.mpr
    intro argument member
    exact ScopedPattern.isWellScopedAt_mono (localScopes argument member) (Nat.le_add_right _ _)
  have readout := instantiated_from_checks
    (original := NativeContextualSubstitution.value target substitution original)
    (ambient := target) (depth := depth) rfl arity newBodyScope argumentScopes
    (by
      change (ContextSubstitution.substitute (occurrenceAssignment original.dependencies.length depth arguments)
        (ContextSubstitution.substitute (ContextSubstitution.lift original.dependencies.length substitution)
          original.body)).isWellScopedAt (depth + target) = true
      rw [← square, ← actualValue]
      exact resultScope)
  change _ = some (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution) actual)
  rw [readout]
  apply congrArg some
  change ContextSubstitution.substitute (occurrenceAssignment original.dependencies.length depth arguments)
    (ContextSubstitution.substitute (ContextSubstitution.lift original.dependencies.length substitution)
      original.body) = _
  rw [← square, ← actualValue]

end Mettapedia.OSLF.NativeTypes.Modal.NativeValueInstantiationSubstitution
