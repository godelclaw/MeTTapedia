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


 theorem matching_ordinary_defined {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : ScopedRuleMatching.Assignment} {schema target : Pattern}
    (matched : Matches rule spec ambient site path depth initial schema target final) :
    Defined (ordinary final) schema.freeFvarNames := by
  intro name member
  obtain ⟨value, found⟩ := GeneralPremise.matching_bound_names matched name member
  exact ⟨value.body, by rw [ordinary_lookup, found]; rfl⟩

 theorem instantiation_readout {rule : RewriteRule} {operation : Pattern → Pattern → Pattern}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {assignment : ScopedRuleMatching.Assignment} {schema target : Pattern}
    (shape : FirstOrder schema) (roots : GeneralPremise.RootValues ambient assignment)
    (read : instantiateWith? operation rule (GeneralRuleBindingInference.inferredSpec rule)
      ambient site path 0 assignment schema = some target) :
    applyBindings (ordinary assignment) schema = target := binderFree_instantiation_readout shape.binderFree roots read

 theorem instantiation_arguments_readout {rule : RewriteRule} {operation : Pattern → Pattern → Pattern}
    {ambient index : Nat} {site : RulePatternSite} {path : List Nat}
    {assignment : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
    (shapes : ∀ schema ∈ schemas, FirstOrder schema) (roots : GeneralPremise.RootValues ambient assignment)
    (read : instantiateArgsWith? operation rule (GeneralRuleBindingInference.inferredSpec rule)
      ambient site path 0 assignment index schemas = some targets) :
    schemas.map (applyBindings (ordinary assignment)) = targets := binderFree_instantiation_arguments_readout (firstOrder_arguments_binderFree shapes) roots read


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


/-! ## Recursive matching retains its complete binding domain -/

mutual
/-- Uniqueness and the exact added-name domain depend on the scoped capture
operation, not on a constructor-only approximation to the schema. -/
theorem matching_unique_names_recursive {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {schema target : Pattern}
    (matched : Matches rule spec ambient site path depth initial schema target final)
    (unique : (initial.map Prod.fst).Nodup) :
    (final.map Prod.fst).Nodup ∧ ∀ name,
      name ∈ final.map Prod.fst ↔ name ∈ initial.map Prod.fst ∨ name ∈ schema.freeFvarNames := by
  cases matched with
  | capture captured =>
    obtain ⟨result,names⟩ := capture_unique_names captured unique
    exact ⟨result,by simpa only [Pattern.freeFvarNames,List.mem_singleton,or_comm] using names⟩
  | bound => exact ⟨unique,by simp [Pattern.freeFvarNames]⟩
  | constructor children =>
    simpa only [Pattern.freeFvarNames] using arguments_unique_names_recursive children unique
  | binder body => simpa only [Pattern.freeFvarNames] using matching_unique_names_recursive body unique
  | binders body => simpa only [Pattern.freeFvarNames] using matching_unique_names_recursive body unique
  | substitution body replacement =>
    obtain ⟨middleUnique,bodyNames⟩ := matching_unique_names_recursive body unique
    obtain ⟨finalUnique,replacementNames⟩ := matching_unique_names_recursive replacement middleUnique
    refine ⟨finalUnique,?_⟩
    intro name
    rw [replacementNames,bodyNames]
    simp only [Pattern.freeFvarNames,List.mem_append,or_assoc]
  | bag _ children =>
    simpa only [Pattern.freeFvarNames] using bag_unique_names_recursive children unique
  | vector children =>
    simpa only [Pattern.freeFvarNames,Option.toList_none,List.append_nil] using
      arguments_unique_names_recursive children unique
  | vectorRest children captured =>
    obtain ⟨middleUnique,childNames⟩ := arguments_unique_names_recursive children unique
    obtain ⟨finalUnique,restNames⟩ := capture_unique_names captured middleUnique
    refine ⟨finalUnique,?_⟩
    intro name
    rw [restNames,childNames]
    simp only [Pattern.freeFvarNames,Option.toList_some,List.mem_append,List.mem_singleton]
    tauto
termination_by sizeOf schema

theorem arguments_unique_names_recursive {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {schemas targets : List Pattern}
    (matched : Arguments rule spec ambient site path depth initial index schemas targets final)
    (unique : (initial.map Prod.fst).Nodup) :
    (final.map Prod.fst).Nodup ∧ ∀ name,
      name ∈ final.map Prod.fst ↔ name ∈ initial.map Prod.fst ∨ name ∈ schemas.flatMap Pattern.freeFvarNames := by
  cases matched with
  | nil => exact ⟨unique,by simp⟩
  | cons head tail =>
    obtain ⟨middleUnique,headNames⟩ := matching_unique_names_recursive head unique
    obtain ⟨finalUnique,tailNames⟩ := arguments_unique_names_recursive tail middleUnique
    refine ⟨finalUnique,?_⟩
    intro name
    rw [tailNames,headNames]
    simp only [List.flatMap_cons,List.mem_append,or_assoc]
termination_by sizeOf schemas

theorem bag_unique_names_recursive {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {schemas targets : List Pattern} {rest : Option String} {kind : CollType}
    (matched : Bag rule spec ambient site path depth initial index schemas rest kind targets final)
    (unique : (initial.map Prod.fst).Nodup) :
    (final.map Prod.fst).Nodup ∧ ∀ name,
      name ∈ final.map Prod.fst ↔ name ∈ initial.map Prod.fst ∨
        name ∈ schemas.flatMap Pattern.freeFvarNames ++ rest.toList := by
  cases matched with
  | nil => exact ⟨unique,by simp⟩
  | rest captured =>
    obtain ⟨finalUnique,names⟩ := capture_unique_names captured unique
    exact ⟨finalUnique,by simpa only [List.flatMap_nil,List.nil_append,Option.toList_some,
      List.mem_singleton,or_comm] using names⟩
  | cons _ _ head tail =>
    obtain ⟨middleUnique,headNames⟩ := matching_unique_names_recursive head unique
    obtain ⟨finalUnique,tailNames⟩ := bag_unique_names_recursive tail middleUnique
    refine ⟨finalUnique,?_⟩
    intro name
    rw [tailNames,headNames]
    simp only [List.flatMap_cons,List.mem_append,or_assoc]
termination_by sizeOf schemas
end

/-- A dependency-free root capture reads as the actual occurrence target.
The retained later assignment is read directly; no pattern reconstruction is
assumed, and its raw list order is irrelevant. -/
theorem capture_ordinary_compatible {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final chosen : Assignment}
    {name : String} {target : Pattern}
    (captured : capture? rule spec ambient 0 site path
      initial name target = some final)
    (later : Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    Compatible (ordinary chosen) [(name,target)] := by
  obtain ⟨_,arguments,value,_,_,_,found,projected,_⟩ := GeneralScopedMatch.capture_interpretation captured
  have retained := later _ _ found
  have empty := root_value_arguments_empty (roots name value retained) projected
  subst arguments
  have valueEq : value.body = target :=
    Option.some.inj ((root_value_readout (roots name value retained)).symm.trans projected)
  intro entry member
  cases List.mem_singleton.mp member
  rw [ordinary_lookup,retained,Option.map_some,valueEq]

mutual
/-- Recursive binder-free scoped matching maps to the ordinary relational
matcher with the same selected bag indices and exact residuals. Unlike a
substitution reconstruction lemma, this includes unordered collections. -/
theorem binderFree_matching_readback {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final chosen : Assignment}
    {schema target : Pattern} (shape : binderFree schema = true)
    (matched : Matches rule spec
      ambient site path 0 initial schema target final)
    (later : Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ bindings, MatchRel schema target bindings ∧ Compatible (ordinary chosen) bindings ∧
      (bindings.map Prod.fst).Nodup ∧ SameNames bindings schema.freeFvarNames := by
  cases schema with
  | fvar name =>
    cases matched with
    | capture captured =>
      exact ⟨[(name,target)],.fvar,capture_ordinary_compatible captured later roots,
        by simp,by simp [SameNames,Pattern.freeFvarNames]⟩
  | bvar index =>
    cases matched
    exact ⟨[],.bvar,by simp [Compatible],by simp,by simp [SameNames,Pattern.freeFvarNames]⟩
  | apply label schemas =>
    cases matched with
    | constructor children =>
      obtain ⟨bindings,raw,compatible,unique,names⟩ :=
        binderFree_arguments_readback shape children later roots
      exact ⟨bindings,.apply raw raw.length_eq,compatible,unique,by
        simpa only [Pattern.freeFvarNames] using names⟩
  | lambda | multiLambda | subst => simp only [binderFree,Bool.false_eq_true] at shape
  | collection kind schemas rest =>
    cases matched with
    | bag nonvector children =>
      obtain ⟨bindings,raw,compatible,unique,names⟩ :=
        binderFree_bag_readback shape children later roots
      exact ⟨bindings,.collection nonvector raw,compatible,unique,by
        simpa only [Pattern.freeFvarNames] using names⟩
    | vector children =>
      obtain ⟨bindings,raw,compatible,unique,names⟩ :=
        binderFree_arguments_readback shape children later roots
      exact ⟨bindings,.vector raw,compatible,unique,by
        simpa only [Pattern.freeFvarNames,Option.toList_none,List.append_nil] using names⟩
    | @vectorRest _ _ _ _ name targets middle _ children captured =>
      obtain ⟨frontBindings,raw,frontCompatible,frontUnique,frontNames⟩ :=
        binderFree_arguments_readback shape children (Extends.trans (capture_extends captured) later) roots
      have restCompatible := capture_ordinary_compatible captured later roots
      obtain ⟨bindings,merged,compatible,unique,names⟩ :=
        merge_compatible (ordinary chosen) frontBindings [(name,.collection .vec (targets.drop schemas.length) none)]
          frontCompatible restCompatible frontUnique
      refine ⟨bindings,.vectorRest raw merged,compatible,unique,?_⟩
      intro queried
      rw [names,frontNames queried]
      simp only [Pattern.freeFvarNames,Option.toList_some,List.mem_append,List.map_cons,List.map_nil,
        List.mem_singleton]
termination_by sizeOf schema

theorem binderFree_arguments_readback {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final chosen : Assignment}
    {schemas targets : List Pattern} (shapes : binderFreeList schemas = true)
    (matched : Arguments rule spec
      ambient site path 0 initial index schemas targets final)
    (later : Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ bindings, MatchArgsRel schemas targets bindings ∧ Compatible (ordinary chosen) bindings ∧
      (bindings.map Prod.fst).Nodup ∧ SameNames bindings (schemas.flatMap Pattern.freeFvarNames) := by
  cases matched with
  | nil => exact ⟨[],.nil,by simp [Compatible],by simp,by simp [SameNames]⟩
  | cons head tail =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    obtain ⟨headBindings,headRaw,headCompatible,headUnique,headNames⟩ :=
      binderFree_matching_readback headShape head (tail.extends.trans later) roots
    obtain ⟨tailBindings,tailRaw,tailCompatible,_,tailNames⟩ :=
      binderFree_arguments_readback tailShapes tail later roots
    obtain ⟨bindings,merged,compatible,unique,names⟩ :=
      merge_compatible (ordinary chosen) headBindings tailBindings headCompatible tailCompatible headUnique
    refine ⟨bindings,.cons headRaw tailRaw merged,compatible,unique,?_⟩
    intro name
    rw [names,headNames name,tailNames name]
    simp only [List.flatMap_cons,List.mem_append]
termination_by sizeOf schemas

theorem binderFree_bag_readback {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final chosen : Assignment}
    {schemas targets : List Pattern} {rest : Option String} {kind : CollType}
    (shapes : binderFreeList schemas = true)
    (matched : Bag rule spec
      ambient site path 0 initial index schemas rest kind targets final)
    (later : Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ bindings, MatchBagRel schemas rest kind targets bindings ∧ Compatible (ordinary chosen) bindings ∧
      (bindings.map Prod.fst).Nodup ∧
      SameNames bindings (schemas.flatMap Pattern.freeFvarNames ++ rest.toList) := by
  cases matched with
  | nil => exact ⟨[],.nilNoRest,by simp [Compatible],by simp,by simp [SameNames]⟩
  | rest captured =>
    refine ⟨_,.nilRest,capture_ordinary_compatible captured later roots,by simp,?_⟩
    simp [SameNames]
  | cons selected within head tail =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    obtain ⟨headBindings,headRaw,headCompatible,headUnique,headNames⟩ :=
      binderFree_matching_readback headShape head (tail.extends.trans later) roots
    obtain ⟨tailBindings,tailRaw,tailCompatible,_,tailNames⟩ :=
      binderFree_bag_readback tailShapes tail later roots
    obtain ⟨bindings,merged,compatible,unique,names⟩ :=
      merge_compatible (ordinary chosen) headBindings tailBindings headCompatible tailCompatible headUnique
    refine ⟨bindings,.cons selected within headRaw tailRaw merged,compatible,unique,?_⟩
    intro name
    rw [names,headNames name,tailNames name]
    simp only [List.flatMap_cons,List.mem_append,or_assoc]
termination_by sizeOf schemas
end

/-- At an empty initial store the relational mapping gives complete exact
binding readback, including missing names and without asserting raw list
identity. -/
theorem binderFree_matching_bindingAgreement {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {schema target : Pattern} {captured : Assignment}
    (shape : binderFree schema = true)
    (matched : Matches rule spec
      ambient site path 0 [] schema target captured)
    (roots : GeneralPremise.RootValues ambient captured) :
    ∃ bindings,bindings ∈ matchPattern schema target ∧ BindingAgreement schema.freeFvarNames captured bindings := by
  obtain ⟨bindings,raw,compatible,rawUnique,rawNames⟩ :=
    binderFree_matching_readback shape matched (.refl _) roots
  obtain ⟨scopedUnique,scopedNames⟩ := matching_unique_names_recursive matched (by simp)
  have rawDomain : SameNames bindings ((ordinary captured).map Prod.fst) := by
    intro name
    rw [ordinary_names,rawNames name,scopedNames name]
    simp
  have readback := compatible_lookup_all compatible rawDomain
  exact ⟨bindings,matchRel_complete raw,
    ⟨scopedUnique,rawUnique,by simpa using scopedNames,rawNames,
      fun name => (ordinary_lookup captured name).symm.trans (readback name).symm⟩⟩


mutual
/-- A successful binder-free instantiation has a literal relational match.
Collection residuals are taken from that actual successful read, so a rest
with the wrong kind or an open tail is not silently accepted. -/
theorem binderFree_instantiation_matching {rule : RewriteRule} {spec : RuleBindingSpec}
    {operation : Pattern → Pattern → Pattern} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {assignment chosen : Assignment}
    {schema target : Pattern} (shape : binderFree schema = true)
    (later : Extends assignment chosen) (roots : GeneralPremise.RootValues ambient chosen)
    (read : instantiateWith? operation rule spec
      ambient site path 0 assignment schema = some target) :
    ∃ bindings,MatchRel schema target bindings ∧ Compatible (ordinary chosen) bindings ∧
      (bindings.map Prod.fst).Nodup ∧ SameNames bindings schema.freeFvarNames := by
  cases schema with
  | fvar name =>
    simp only [instantiateWith?,Option.bind_eq_bind,Option.bind_eq_some_iff] at read
    obtain ⟨value,found,arguments,occurrence,projected⟩ := read
    have retained := later name value found
    have empty := root_value_arguments_empty (roots name value retained) projected
    subst arguments
    have same : value.body = target :=
      Option.some.inj ((root_value_readout (roots name value retained)).symm.trans projected)
    refine ⟨[(name,target)],.fvar,?_,by simp,by simp [SameNames,Pattern.freeFvarNames]⟩
    intro entry member
    cases List.mem_singleton.mp member
    rw [ordinary_lookup,retained,Option.map_some,same]
  | bvar index =>
    simp only [instantiateWith?, Option.some.injEq] at read
    cases read
    exact ⟨[],.bvar,by simp [Compatible],by simp,by simp [SameNames,Pattern.freeFvarNames]⟩
  | apply label schemas =>
    simp only [instantiateWith?,Option.bind_eq_bind,Option.bind_eq_some_iff] at read
    obtain ⟨targets,read,same⟩ := read
    cases Option.some.inj same
    obtain ⟨bindings,raw,compatible,unique,names⟩ :=
      binderFree_instantiation_arguments_matching shape later roots read
    exact ⟨bindings,.apply raw raw.length_eq,compatible,unique,by
      simpa only [Pattern.freeFvarNames] using names⟩
  | lambda | multiLambda | subst => simp only [binderFree,Bool.false_eq_true] at shape
  | collection kind schemas rest =>
    simp only [instantiateWith?,Option.bind_eq_bind,Option.bind_eq_some_iff] at read
    obtain ⟨explicit,explicitRead,read⟩ := read
    cases rest with
    | none =>
      cases Option.some.inj read
      by_cases vector : kind = .vec
      · subst kind
        obtain ⟨bindings,raw,compatible,unique,names⟩ :=
          binderFree_instantiation_arguments_matching shape later roots explicitRead
        exact ⟨bindings,.vector raw,compatible,unique,by
          simpa only [Pattern.freeFvarNames,Option.toList_none,List.append_nil] using names⟩
      · obtain ⟨bindings,raw,compatible,unique,names⟩ :=
          binderFree_instantiation_bag_matching (residual := []) (restBindings := []) shape later roots
            explicitRead .nilNoRest (by simp [Compatible]) (by simp) (by simp [SameNames])
        exact ⟨bindings,.collection vector (by simpa only [List.append_nil] using raw),
          compatible,unique,by simpa only [Pattern.freeFvarNames] using names⟩
    | some name =>
      simp only [Option.bind_eq_some_iff] at read
      obtain ⟨value,found,arguments,occurrence,actual,projected,read⟩ := read
      have retained := later name value found
      have empty := root_value_arguments_empty (roots name value retained) projected
      subst arguments
      have body : actual = value.body :=
        Option.some.inj (projected.symm.trans (root_value_readout (roots name value retained)))
      subst actual
      cases stored : value.body with
      | collection actualKind residual tail =>
        cases tail with
        | some _ => simp only [stored] at read; cases read
        | none =>
          simp only [stored] at read
          split at read
          · rename_i sameKind
            have sameKind : actualKind = kind := beq_iff_eq.mp sameKind
            subst actualKind
            cases Option.some.inj read
            have residualCompatible : Compatible (ordinary chosen) [(name,.collection kind residual none)] := by
              intro entry member
              cases List.mem_singleton.mp member
              rw [ordinary_lookup,retained,Option.map_some,stored]
            by_cases vector : kind = .vec
            · subst kind
              obtain ⟨front,raw,compatible,unique,names⟩ :=
                binderFree_instantiation_arguments_matching shape later roots explicitRead
              obtain ⟨bindings,merged,combined,combinedUnique,combinedNames⟩ :=
                merge_compatible (ordinary chosen) front [(name,.collection .vec residual none)]
                  compatible residualCompatible unique
              have length := raw.length_eq
              have prefixReadback : (explicit ++ residual).take schemas.length = explicit := by
                rw [length]
                exact List.take_left
              have suffix : (explicit ++ residual).drop schemas.length = residual := by
                rw [length]
                exact List.drop_left
              refine ⟨bindings,.vectorRest (prefixReadback.symm ▸ raw) ?_,combined,combinedUnique,?_⟩
              · simpa only [suffix] using merged
              · intro key
                rw [combinedNames key,names key]
                simp only [Pattern.freeFvarNames,Option.toList_some,List.mem_append,
                  List.map_cons,List.map_nil,List.mem_singleton]
            · obtain ⟨bindings,raw,compatible,unique,names⟩ :=
                binderFree_instantiation_bag_matching shape later roots explicitRead
                  (.nilRest : MatchBagRel [] (some name) kind residual [(name,.collection kind residual none)])
                  residualCompatible (by simp) (by simp [SameNames])
              exact ⟨bindings,.collection vector raw,compatible,unique,by
                simpa only [Pattern.freeFvarNames] using names⟩
          · cases read
      | _ => simp only [stored] at read; cases read
termination_by sizeOf schema

/-- Ordered instantiation retains the original element order and all names. -/
theorem binderFree_instantiation_arguments_matching {rule : RewriteRule} {spec : RuleBindingSpec}
    {operation : Pattern → Pattern → Pattern} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {assignment chosen : Assignment}
    {schemas targets : List Pattern} (shapes : binderFreeList schemas = true)
    (later : Extends assignment chosen) (roots : GeneralPremise.RootValues ambient chosen)
    (read : instantiateArgsWith? operation rule spec
      ambient site path 0 assignment index schemas = some targets) :
    ∃ bindings,MatchArgsRel schemas targets bindings ∧ Compatible (ordinary chosen) bindings ∧
      (bindings.map Prod.fst).Nodup ∧ SameNames bindings (schemas.flatMap Pattern.freeFvarNames) := by
  cases schemas with
  | nil =>
    simp only [instantiateArgsWith?, Option.some.injEq] at read
    cases read
    exact ⟨[],.nil,by simp [Compatible],by simp,by simp [SameNames]⟩
  | cons schema schemas =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    simp only [instantiateArgsWith?,Option.bind_eq_bind,Option.bind_eq_some_iff] at read
    obtain ⟨target,first,targets,rest,same⟩ := read
    cases Option.some.inj same
    obtain ⟨head,headRaw,headCompatible,headUnique,headNames⟩ :=
      binderFree_instantiation_matching headShape later roots first
    obtain ⟨tail,tailRaw,tailCompatible,_,tailNames⟩ :=
      binderFree_instantiation_arguments_matching tailShapes later roots rest
    obtain ⟨bindings,merged,compatible,unique,names⟩ :=
      merge_compatible (ordinary chosen) head tail headCompatible tailCompatible headUnique
    refine ⟨bindings,.cons headRaw tailRaw merged,compatible,unique,?_⟩
    intro key
    rw [names,headNames key,tailNames key]
    simp only [List.flatMap_cons,List.mem_append]
termination_by sizeOf schemas

/-- A positional instantiation also gives a bag match by selecting the first
remaining explicit element each time. The end witness retains the actual rest. -/
theorem binderFree_instantiation_bag_matching {rule : RewriteRule} {spec : RuleBindingSpec}
    {operation : Pattern → Pattern → Pattern} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {assignment chosen : Assignment}
    {schemas explicit residual : List Pattern} {rest : Option String} {kind : CollType}
    {restBindings : Bindings} (shapes : binderFreeList schemas = true)
    (later : Extends assignment chosen) (roots : GeneralPremise.RootValues ambient chosen)
    (read : instantiateArgsWith? operation rule spec
      ambient site path 0 assignment index schemas = some explicit)
    (endMatch : MatchBagRel [] rest kind residual restBindings)
    (endCompatible : Compatible (ordinary chosen) restBindings)
    (endUnique : (restBindings.map Prod.fst).Nodup) (endNames : SameNames restBindings rest.toList) :
    ∃ bindings,MatchBagRel schemas rest kind (explicit ++ residual) bindings ∧
      Compatible (ordinary chosen) bindings ∧ (bindings.map Prod.fst).Nodup ∧
      SameNames bindings (schemas.flatMap Pattern.freeFvarNames ++ rest.toList) := by
  cases schemas with
  | nil =>
    simp only [instantiateArgsWith?, Option.some.injEq] at read
    cases read
    exact ⟨restBindings,endMatch,endCompatible,endUnique,by simpa using endNames⟩
  | cons schema schemas =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    simp only [instantiateArgsWith?,Option.bind_eq_bind,Option.bind_eq_some_iff] at read
    obtain ⟨target,first,targets,read,same⟩ := read
    cases Option.some.inj same
    obtain ⟨head,headRaw,headCompatible,headUnique,headNames⟩ :=
      binderFree_instantiation_matching headShape later roots first
    obtain ⟨tail,tailRaw,tailCompatible,_,tailNames⟩ :=
      binderFree_instantiation_bag_matching tailShapes later roots read endMatch endCompatible endUnique endNames
    obtain ⟨bindings,merged,compatible,unique,names⟩ :=
      merge_compatible (ordinary chosen) head tail headCompatible tailCompatible headUnique
    refine ⟨bindings,?_,compatible,unique,?_⟩
    · simpa only [List.cons_append,List.getElem_cons_zero,List.eraseIdx_cons_zero] using
        (MatchBagRel.cons 0 (by simp) headRaw tailRaw merged)
    · intro key
      rw [names,headNames key,tailNames key]
      simp only [List.flatMap_cons,List.mem_append,or_assoc]
termination_by sizeOf schemas
end

#print axioms binderFree_instantiation_matching
#print axioms binderFree_instantiation_arguments_matching
#print axioms binderFree_instantiation_bag_matching

#print axioms matching_unique_names_recursive
#print axioms arguments_unique_names_recursive
#print axioms bag_unique_names_recursive
#print axioms capture_ordinary_compatible
#print axioms binderFree_matching_readback
#print axioms binderFree_arguments_readback
#print axioms binderFree_bag_readback
#print axioms binderFree_matching_bindingAgreement

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
