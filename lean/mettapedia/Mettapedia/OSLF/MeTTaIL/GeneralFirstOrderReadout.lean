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

@[simp] theorem ordinary_names (assignment : ScopedRuleMatching.Assignment) :
    (ordinary assignment).map Prod.fst = assignment.map Prod.fst := by
  simp only [ordinary, List.map_map, Function.comp_def]

theorem scoped_lookup_none_iff_not_mem_names (assignment : ScopedRuleMatching.Assignment) (name : String) :
    lookup assignment name = none ↔ name ∉ assignment.map Prod.fst := by
  have ordinaryAbsent := lookup_none_iff_not_mem_names (ordinary assignment) name
  rw [ordinary_lookup, ordinary_names] at ordinaryAbsent
  simpa only [Option.map_eq_none_iff] using ordinaryAbsent

/-- A logical agreement retains unique raw stores, their exact bound domain,
and all lookups. Raw list equality is neither required nor manufactured. -/
structure BindingAgreement (names : List String) (assignment : ScopedRuleMatching.Assignment)
    (bindings : Bindings) : Prop where
  scopedUnique : (assignment.map Prod.fst).Nodup
  ordinaryUnique : (bindings.map Prod.fst).Nodup
  scopedNames : ∀ name, name ∈ assignment.map Prod.fst ↔ name ∈ names
  ordinaryNames : SameNames bindings names
  lookups : ∀ name, (lookup assignment name).map ContextualValue.body = bindings.lookup name

theorem BindingAgreement.readout {names : List String} {assignment : ScopedRuleMatching.Assignment}
    {bindings : Bindings} (agreement : BindingAgreement names assignment bindings) (order : List String) :
    bindingReadout order (ordinary assignment) = bindingReadout order bindings :=
  bindingReadout_eq_of_lookups order (ordinary assignment) bindings
    (fun name => (ordinary_lookup assignment name).trans (agreement.lookups name))

theorem BindingAgreement.absent {names : List String} {assignment : ScopedRuleMatching.Assignment}
    {bindings : Bindings} (agreement : BindingAgreement names assignment bindings) {name : String}
    (absent : name ∉ names) : lookup assignment name = none ∧ bindings.lookup name = none :=
  ⟨(scoped_lookup_none_iff_not_mem_names assignment name).mpr
      (fun member => absent ((agreement.scopedNames name).mp member)),
   (lookup_none_iff_not_mem_names bindings name).mpr
      (fun member => absent ((agreement.ordinaryNames name).mp member))⟩

/-- A successful capture adds precisely one name or retains the previous
capture. It cannot introduce duplicates into a store whose keys are unique. -/
theorem assign_unique_names {initial final : ScopedRuleMatching.Assignment} {name : String}
    {value : ContextualValue} (assigned : assign initial name value = some final)
    (unique : (initial.map Prod.fst).Nodup) :
    (final.map Prod.fst).Nodup ∧
      ∀ queried, queried ∈ final.map Prod.fst ↔ queried = name ∨ queried ∈ initial.map Prod.fst := by
  unfold assign at assigned
  cases prior : lookup initial name with
  | none =>
    cases Option.some.inj (by simpa only [prior] using assigned)
    refine ⟨List.nodup_cons.mpr ⟨(scoped_lookup_none_iff_not_mem_names initial name).mp prior, unique⟩, ?_⟩
    intro queried
    simp only [List.map_cons, List.mem_cons]
  | some stored =>
    simp only [prior] at assigned
    split at assigned
    · cases Option.some.inj assigned
      have present : name ∈ initial.map Prod.fst := by
        by_contra absent
        have empty := (scoped_lookup_none_iff_not_mem_names initial name).mpr absent
        rw [prior] at empty
        cases empty
      refine ⟨unique, ?_⟩
      intro queried
      constructor
      · exact Or.inr
      · rintro (rfl | member)
        · exact present
        · exact member
    · cases assigned

theorem capture_unique_names {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    {name : String} {target : Pattern}
    (captured : capture? rule spec ambient depth site path initial name target = some final)
    (unique : (initial.map Prod.fst).Nodup) :
    (final.map Prod.fst).Nodup ∧
      ∀ queried, queried ∈ final.map Prod.fst ↔ queried = name ∨ queried ∈ initial.map Prod.fst := by
  simp only [capture?, Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  obtain ⟨_, _, _, _, _, _, assigned⟩ := captured
  exact assign_unique_names assigned unique

mutual
  theorem matching_unique_names {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : ScopedRuleMatching.Assignment} {schema target : Pattern}
      (shape : FirstOrder schema)
      (matched : Matches rule spec ambient site path depth initial schema target final)
      (unique : (initial.map Prod.fst).Nodup) :
      (final.map Prod.fst).Nodup ∧ ∀ name,
        name ∈ final.map Prod.fst ↔ name ∈ initial.map Prod.fst ∨ name ∈ schema.freeFvarNames := by
    cases shape with
    | metavariable name =>
      cases matched with
      | capture captured =>
        obtain ⟨finalUnique, names⟩ := capture_unique_names captured unique
        refine ⟨finalUnique, ?_⟩
        intro queried
        simpa only [Pattern.freeFvarNames, List.mem_singleton, or_comm] using names queried
    | constructor label arguments shapes =>
      cases matched with
      | constructor children =>
        simpa only [Pattern.freeFvarNames] using arguments_unique_names shapes children unique
  termination_by sizeOf schema

  theorem arguments_unique_names {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
      (shapes : ∀ schema ∈ schemas, FirstOrder schema)
      (matched : Arguments rule spec ambient site path depth initial index schemas targets final)
      (unique : (initial.map Prod.fst).Nodup) :
      (final.map Prod.fst).Nodup ∧ ∀ name,
        name ∈ final.map Prod.fst ↔ name ∈ initial.map Prod.fst ∨ name ∈ schemas.flatMap Pattern.freeFvarNames := by
    cases schemas with
    | nil => cases matched; exact ⟨unique, by simp⟩
    | cons schema schemas =>
      cases matched with
      | cons first rest =>
        obtain ⟨middleUnique, firstNames⟩ := matching_unique_names (shapes schema (by simp)) first unique
        obtain ⟨finalUnique, restNames⟩ := arguments_unique_names
          (fun child member => shapes child (List.mem_cons_of_mem _ member)) rest middleUnique
        refine ⟨finalUnique, ?_⟩
        intro name
        rw [restNames, firstNames]
        simp only [List.flatMap_cons, List.mem_append, or_assoc]
  termination_by sizeOf schemas
end

theorem query_arguments_unique {context : GeneralPremise.Context} {index : Nat}
    {initial final : ScopedRuleMatching.Assignment} {schemas values : List Pattern}
    {modes : List RelationArgMode}
    (shapes : ∀ schema ∈ schemas, FirstOrder schema)
    (held : GeneralPremise.ArgumentsHold context index initial schemas values modes final)
    (unique : (initial.map Prod.fst).Nodup) : (final.map Prod.fst).Nodup := by
  induction held with
  | nil => exact unique
  | cons head tail ih =>
    have tailShapes := fun child member => shapes child (List.mem_cons_of_mem _ member)
    cases head with
    | input _ => exact ih tailShapes unique
    | output matching =>
      exact ih tailShapes (matching_unique_names (shapes _ (by simp)) matching unique).1

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
