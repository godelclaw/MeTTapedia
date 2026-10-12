import Mettapedia.OSLF.NativeTypes.Modal.NativeValueInstantiationSubstitution

/-!
# Exact inverse recovery of scoped authored captures

The inverse occurrence substitution is justified from the actual parsed
injective local-variable spine. Its composition with the forward occurrence
assignment is the identity on complete bodies, including nested binders.
This gives capture recovery after an ambient substitution without allowing
new dependence on an unselected local binder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeRecoverySubstitution

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

def localIndex? (depth : Nat) : Pattern → Option Nat
  | .bvar index => if index < depth then some index else none
  | _ => none

private theorem index_readout {depth index : Nat} {pattern : Pattern}
    (selected : localIndex? depth pattern = some index) : pattern = .bvar index ∧ index < depth := by
  cases pattern <;> simp only [localIndex?] at selected <;> try contradiction
  split at selected <;> try contradiction
  cases Option.some.inj selected
  exact ⟨rfl, by assumption⟩

private theorem indices_readout {depth : Nat} {arguments : List Pattern} {indices : List Nat}
    (selected : arguments.mapM (localIndex? depth) = some indices) :
    arguments = indices.map Pattern.bvar ∧ ∀ index ∈ indices, index < depth := by
  induction arguments generalizing indices with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at selected
      subst indices
      exact ⟨rfl, by simp⟩
  | cons first rest ih =>
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def] at selected
      obtain ⟨index, parsed, suffix, parsedRest, same⟩ := selected
      cases Option.some.inj same
      obtain ⟨firstSame, within⟩ := index_readout parsed
      obtain ⟨restSame, suffixWithin⟩ := ih parsedRest
      refine ⟨by simp only [List.map_cons, firstSame, restSame], ?_⟩
      intro item member
      rcases List.mem_cons.mp member with same | member
      · subst item; exact within
      · exact suffixWithin item member

theorem variableSpine_readout {depth : Nat} {arguments : List Pattern} {indices : List Nat}
    (selected : variableSpine? depth arguments = some indices) :
    arguments = indices.map Pattern.bvar ∧ indices.Nodup ∧ ∀ index ∈ indices, index < depth := by
  change (do
    let actual ← arguments.mapM (localIndex? depth)
    if actual.Nodup then some actual else none) = some indices at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  obtain ⟨actual, parsed, chosen⟩ := selected
  split at chosen <;> try contradiction
  rename_i unique
  cases Option.some.inj chosen
  obtain ⟨same, within⟩ := indices_readout parsed
  exact ⟨same, unique, within⟩

theorem spine_local_scopes {depth : Nat} {arguments : List Pattern} {indices : List Nat}
    (selected : variableSpine? depth arguments = some indices) :
    ∀ argument ∈ arguments, argument.isWellScopedAt depth = true := by
  obtain ⟨same, _, within⟩ := variableSpine_readout selected
  rw [same]
  intro argument member
  obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
  exact decide_eq_true (within index present)

theorem inverse_occurrence_assignment {dependencies depth ambient : Nat}
    {arguments : List Pattern} {indices : List Nat}
    (selected : variableSpine? depth arguments = some indices)
    (arity : indices.length = dependencies) :
    (fun index => ContextSubstitution.substitute (recoveryAssignment depth dependencies ambient indices)
      (occurrenceAssignment dependencies depth arguments index)) = Pattern.bvar := by
  obtain ⟨same, unique, within⟩ := variableSpine_readout selected
  subst arguments
  funext index
  by_cases dependency : index < dependencies
  · have inIndices : index < indices.length := by omega
    have inArguments : index < (indices.map Pattern.bvar).length := by simpa using inIndices
    have present := List.getElem_mem inIndices
    simp only [occurrenceAssignment, dependency, ite_true,
      List.getD_eq_getElem _ _ inArguments, List.getElem_map, ContextSubstitution.substitute,
      recoveryAssignment, within _ present, List.getElem_mem inIndices, ite_true,
      unique.idxOf_getElem index inIndices]
  · have outside : ¬ depth + (index - dependencies) < depth := by omega
    simp only [occurrenceAssignment, dependency, ite_false, ContextSubstitution.substitute,
      recoveryAssignment, outside]
    congr 1
    omega

theorem recover_interpreted_body {dependencies depth ambient : Nat}
    {arguments : List Pattern} {indices : List Nat}
    (selected : variableSpine? depth arguments = some indices)
    (arity : indices.length = dependencies) (body : Pattern) :
    ContextSubstitution.substitute (recoveryAssignment depth dependencies ambient indices)
      (ContextSubstitution.substitute (occurrenceAssignment dependencies depth arguments) body) = body := by
  rw [ContextSubstitution.substitute_comp, inverse_occurrence_assignment selected arity,
    ContextSubstitution.substitute_id]

theorem recovery_from_instantiation {original : ContextualValue} {ambient depth : Nat}
    {arguments : List Pattern} {actual : Pattern} {indices : List Nat}
    (selected : variableSpine? depth arguments = some indices)
    (accepted : instantiateValue? original ambient depth arguments = some actual) :
    recoverValue? original.dependencies ambient depth arguments actual = some original := by
  obtain ⟨ambientSame, argumentArity, bodyScope, actualValue⟩ :=
    NativeValueInstantiationSubstitution.instantiated_readout accepted
  have indexArity : indices.length = original.dependencies.length := by
    obtain ⟨same, _, _⟩ := variableSpine_readout selected
    rw [same, List.length_map] at argumentArity
    exact argumentArity
  have originalBody := recover_interpreted_body (ambient := ambient) selected indexArity original.body
  have actualScope := instantiateValue?_scoped _ _ _ _ _ accepted
  have restored :
      ({dependencies := original.dependencies, ambient := ambient,
        body := ContextSubstitution.substitute
          (recoveryAssignment depth original.dependencies.length ambient indices) actual} : ContextualValue) =
      original := by
    rw [actualValue, originalBody, ← ambientSame]
  simp [recoverValue?, actualScope, selected, indexArity, restored, accepted]

theorem recovery_substitutes {dependencies : List TypeExpr} {source target depth : Nat}
    {arguments : List Pattern} {actual : Pattern} {original : ContextualValue}
    (recovered : recoverValue? dependencies source depth arguments actual = some original)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    recoverValue? dependencies target depth arguments
      (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution) actual) =
      some (NativeContextualSubstitution.value target substitution original) := by
  have instantiated := recoverValue?_forward _ _ _ _ _ _ recovered
  obtain ⟨dependencySame, ambientSame⟩ := recoverValue?_context _ _ _ _ _ _ recovered
  have parsed : ∃ indices, variableSpine? depth arguments = some indices := by
    unfold recoverValue? at recovered
    split at recovered <;> try contradiction
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered
    obtain ⟨indices, selected, _⟩ := recovered
    exact ⟨indices, selected⟩
  obtain ⟨indices, selected⟩ := parsed
  have next := NativeValueInstantiationSubstitution.successful_instantiation_substitutes instantiated
    (spine_local_scopes selected) substitution boundScoped
  have backwards := recovery_from_instantiation selected next
  simpa only [NativeContextualSubstitution.value_dependencies, dependencySame] using backwards

end Mettapedia.OSLF.NativeTypes.Modal.NativeRecoverySubstitution
