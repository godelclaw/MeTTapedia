import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderMatch

/-!
# First-order scoped firings have ordinary rule readouts

The scoped matcher retains contextual metadata. On dependency-free first-order
schemas the metadata reads back to an ordinary substitution. The result below
compares the independent matching and instantiation judgments, rather than
comparing a definition to its own executable spelling.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch Match MatchSpec

 theorem inferred_success_arguments_empty {rule : RewriteRule} {name : String}
    {site : RulePatternSite} {path : List Nat} {arguments : List Pattern}
    (read : arguments? rule (GeneralRuleBindingInference.inferredSpec rule) name site path = some arguments) :
    arguments = [] := by
  have original := read
  unfold arguments? at read
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at read
  obtain ⟨dependencies, declared, _⟩ := read
  have empty := GeneralRuleBindingInference.inferred_dependencies_empty declared
  exact GeneralRuleBindingInference.inferred_arguments_empty (empty ▸ declared) original

 theorem matching_ordinary_defined {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : ScopedRuleMatching.Assignment} {schema target : Pattern}
    (matched : Matches rule spec ambient site path depth initial schema target final) :
    Defined (ordinary final) schema.freeFvarNames := by
  intro name member
  obtain ⟨value, found⟩ := GeneralPremise.matching_bound_names matched name member
  exact ⟨value.body, by rw [ordinary_lookup, found]; rfl⟩

mutual
 theorem instantiation_readout {rule : RewriteRule} {operation : Pattern → Pattern → Pattern}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {assignment : ScopedRuleMatching.Assignment} {schema target : Pattern}
    (shape : FirstOrder schema) (roots : GeneralPremise.RootValues ambient assignment)
    (read : instantiateWith? operation rule (GeneralRuleBindingInference.inferredSpec rule)
      ambient site path 0 assignment schema = some target) :
    applyBindings (ordinary assignment) schema = target := by
  cases shape with
  | metavariable name =>
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨value, found, arguments, occurrence, read⟩ := read
    have empty := inferred_success_arguments_empty occurrence
    subst arguments
    have same := Option.some.inj ((root_value_readout (roots name value found)).symm.trans read)
    exact (ordinary_variable found).trans same
  | constructor label arguments shapes =>
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨results, read, same⟩ := read
    cases Option.some.inj same
    have children := instantiation_arguments_readout shapes roots read
    simpa only [applyBindings] using congrArg (Pattern.apply label) children
 termination_by sizeOf schema

 theorem instantiation_arguments_readout {rule : RewriteRule} {operation : Pattern → Pattern → Pattern}
    {ambient index : Nat} {site : RulePatternSite} {path : List Nat}
    {assignment : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
    (shapes : ∀ schema ∈ schemas, FirstOrder schema) (roots : GeneralPremise.RootValues ambient assignment)
    (read : instantiateArgsWith? operation rule (GeneralRuleBindingInference.inferredSpec rule)
      ambient site path 0 assignment index schemas = some targets) :
    schemas.map (applyBindings (ordinary assignment)) = targets := by
  cases schemas with
  | nil =>
    simp only [instantiateArgsWith?, Option.some.injEq] at read
    simpa only [List.map_nil] using read
  | cons schema schemas =>
    simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨target, first, targets, rest, same⟩ := read
    cases Option.some.inj same
    have head := instantiation_readout (shapes schema (by simp)) roots first
    have tail := instantiation_arguments_readout
      (fun child member => shapes child (List.mem_cons_of_mem _ member)) roots rest
    simp only [List.map_cons, head, tail]
 termination_by sizeOf schemas
end

 theorem rule_readout {rule : RewriteRule} {ambient : Nat} {source target : Pattern}
    {captured : ScopedRuleMatching.Assignment}
    {operation : Pattern → Pattern → Pattern}
    (left : FirstOrder rule.left) (right : FirstOrder rule.right)
    (matching : Matches rule (GeneralRuleBindingInference.inferredSpec rule) ambient .left [] 0
      [] rule.left source captured)
    (roots : GeneralPremise.RootValues ambient captured)
    (reduct : reductWith? operation rule (GeneralRuleBindingInference.inferredSpec rule) ambient
      captured = some target)
    (right_bound : ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames) :
    ∃ bindings, MatchRel rule.left source bindings ∧ applyBindings bindings rule.right = target := by
  have reconstructed := matching_reconstructs left matching (.refl _) roots
  obtain ⟨bindings, matched, compatible, _, names⟩ :=
    match_instance (ordinary captured) left (matching_ordinary_defined matching)
  rw [reconstructed] at matched
  have rhs := instantiation_readout right roots reduct
  refine ⟨bindings, matched, ?_⟩
  exact (compatible_readout right compatible (fun name member =>
    (names name).mpr (right_bound name member))).trans rhs

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
