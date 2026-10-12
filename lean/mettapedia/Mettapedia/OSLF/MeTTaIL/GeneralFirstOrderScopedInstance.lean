import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderReadout
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderTyping
import Mettapedia.OSLF.MeTTaIL.MatchBindingExtension

/-!
# Scoped witnesses for ordinary first-order rule instances

Occurrence addresses are read from the authored rule. Dependency-free captures
store the caller context and retain their exact bodies. Consistent repeated
variables reuse the first capture; constructor traversal preserves all readouts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch Match MatchSpec
open Mettapedia.GSLT.LanguageDef.WellSorted

 def NameCoherent (rule : RewriteRule) (site : RulePatternSite) (path : List Nat) (schema : Pattern) : Prop :=
    ∀ suffix, (sitePattern? rule site).bind (occurrenceAt? · (path ++ suffix)) = occurrenceAt? schema suffix

 theorem NameCoherent.left (rule : RewriteRule) : NameCoherent rule .left [] rule.left := by
  intro suffix
  rfl

 theorem NameCoherent.right (rule : RewriteRule) : NameCoherent rule .right [] rule.right := by
  intro suffix
  rfl

 theorem NameCoherent.fvar {rule : RewriteRule} {site : RulePatternSite} {path : List Nat} {name : String}
    (coherent : NameCoherent rule site path (.fvar name)) :
    occurrenceDeclared rule {name, site, path, arguments := []} = true := by
  unfold occurrenceDeclared
  rw [← List.append_nil path]
  rw [coherent []]
  simp [occurrenceAt?]

 def ArgumentsNameCoherent (rule : RewriteRule) (site : RulePatternSite) (path : List Nat)
    (index : Nat) (schemas : List Pattern) : Prop :=
    ∀ offset schema, schemas[offset]? = some schema → NameCoherent rule site (path ++ [index + offset]) schema

 theorem NameCoherent.arguments {rule : RewriteRule} {site : RulePatternSite} {path : List Nat}
    {label : String} {schemas : List Pattern} (coherent : NameCoherent rule site path (.apply label schemas)) :
    ArgumentsNameCoherent rule site path 0 schemas := by
  intro offset schema selected suffix
  have read := coherent (offset :: suffix)
  simpa only [Nat.zero_add, List.append_assoc, List.singleton_append, occurrenceAt?, selected,
    Option.bind_some] using read

 theorem ArgumentsNameCoherent.head {rule : RewriteRule} {site : RulePatternSite} {path : List Nat}
    {index : Nat} {schema : Pattern} {schemas : List Pattern}
    (coherent : ArgumentsNameCoherent rule site path index (schema :: schemas)) :
    NameCoherent rule site (path ++ [index]) schema := by
  simpa only [Nat.add_zero] using coherent 0 schema rfl

 theorem ArgumentsNameCoherent.tail {rule : RewriteRule} {site : RulePatternSite} {path : List Nat}
    {index : Nat} {schema : Pattern} {schemas : List Pattern}
    (coherent : ArgumentsNameCoherent rule site path index (schema :: schemas)) :
    ArgumentsNameCoherent rule site path (index + 1) schemas := by
  intro offset child selected
  have read := coherent (offset + 1) child (by simpa using selected)
  simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using read

 theorem context_filter_of_lookup (context : List (String × TypeExpr)) {name : String} {type : TypeExpr}
    (unique : (context.map Prod.fst).Nodup) (found : context.lookup name = some type) :
    context.filter (fun entry => entry.1 == name) = [(name, type)] := by
    induction context with
    | nil => simp at found
    | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      simp only [List.lookup] at found
      have keys := List.nodup_cons.mp (by simpa only [List.map_cons] using unique)
      by_cases same : key = name
      · subst key
        have equal := Option.some.inj (by simpa using found)
        subst value
        have noRest : rest.filter (fun entry => entry.1 == name) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro entry member accepted
          have keySame : entry.1 = name := beq_iff_eq.mp accepted
          exact keys.1 (keySame ▸ List.mem_map_of_mem member)
        simp [noRest]
      · have absent : (key == name) = false := by simp [same]
        have reversed : (name == key) = false := by simp [Ne.symm same]
        have restFound : rest.lookup name = some type := by simpa only [reversed] using found
        have remaining := ih keys.2 restFound
        simp only [List.filter_cons, absent, Bool.false_eq_true, if_false, remaining]

 theorem inferred_dependencies_of_lookup (rule : RewriteRule) {name : String} {type : TypeExpr}
    (unique : (rule.typeContext.map Prod.fst).Nodup) (found : rule.typeContext.lookup name = some type) :
    dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some [] := by
  have filtered := context_filter_of_lookup rule.typeContext unique found
  simp only [dependencies?, GeneralRuleBindingInference.inferredSpec, List.filter_map]
  change (match (rule.typeContext.filter (fun entry => entry.1 == name)).map
      (fun entry => (entry.1, ([] : List TypeExpr))) with
    | [(_, dependencies)] => some dependencies
    | _ => none) = some []
  rw [filtered]
  rfl

 theorem raw_lookup_member {bindings : Bindings} {name : String} {target : Pattern}
    (found : bindings.lookup name = some target) : (name, target) ∈ bindings := by
  unfold Bindings.lookup at found
  obtain ⟨entry, selected, equal⟩ := Option.map_eq_some_iff.mp found
  have key : entry.1 = name := beq_iff_eq.mp
    (List.find?_some (p := fun entry : String × Pattern => entry.1 == name) selected)
  rcases entry with ⟨keyName, value⟩
  dsimp only at key equal
  subst keyName
  subst value
  exact List.mem_of_find?_eq_some selected

 def rootValue (ambient : Nat) (body : Pattern) : ContextualValue := ⟨[], ambient, body⟩

 theorem recover_root {ambient : Nat} {body : Pattern} (scopeProof : body.isWellScopedAt ambient = true) :
    recoverValue? [] ambient 0 [] body = some (rootValue ambient body) := by
  have recovery : recoveryAssignment 0 0 ambient [] = Pattern.bvar := by
    funext index
    simp [recoveryAssignment]
  have occurrence : occurrenceAssignment 0 0 [] = Pattern.bvar := by
    funext index
    simp [occurrenceAssignment]
  simp [recoverValue?, scopeProof, variableSpine?, recovery, ContextSubstitution.substitute_id,
    rootValue, instantiateValue?, occurrence]

 def ScopedCompatible (ambient : Nat) (environment : Bindings) (assignment : ScopedRuleMatching.Assignment) : Prop :=
    ∀ entry ∈ assignment, entry.2.dependencies = [] ∧ entry.2.ambient = ambient ∧
      environment.lookup entry.1 = some entry.2.body

 theorem capture_instance {rule : RewriteRule} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {environment : Bindings} {initial : ScopedRuleMatching.Assignment} {name : String} {target : Pattern}
    (before : ScopedCompatible ambient environment initial)
    (valueRead : environment.lookup name = some target)
    (dependency : dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some [])
    (coherent : NameCoherent rule site path (.fvar name)) (scopeProof : target.isWellScopedAt ambient = true) :
    ∃ final, capture? rule (GeneralRuleBindingInference.inferredSpec rule) ambient 0 site path initial name target = some final ∧
      ScopedCompatible ambient environment final := by
  have arguments : arguments? rule (GeneralRuleBindingInference.inferredSpec rule) name site path = some [] :=
    arguments?_empty_of_declared rule _ name site path dependency coherent.fvar rfl
  have reduced := recover_root scopeProof
  cases prior : lookup initial name with
  | none =>
    refine ⟨(name, rootValue ambient target) :: initial, ?_, ?_⟩
    · simp only [capture?, dependency, arguments, reduced, Option.bind_eq_bind, Option.bind_some, assign, prior]
    · intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨rfl, rfl, valueRead⟩
      · exact before entry member
  | some value =>
    obtain ⟨empty, caller, found⟩ := before (name, value)
      (ConditionalEquationExecution.lookup_assignment_member initial name value prior)
    have body := Option.some.inj (found.symm.trans valueRead)
    have same : value = rootValue ambient target := by
      cases value
      simp_all [rootValue]
    refine ⟨initial, ?_, before⟩
    simp only [capture?, dependency, arguments, reduced, Option.bind_eq_bind, Option.bind_some, assign, prior, same,
      beq_self_eq_true, if_true]

mutual
 theorem raw_matching_defined {schema target : Pattern} {bindings : Bindings}
    (shape : FirstOrder schema) (matched : MatchRel schema target bindings) :
    Defined bindings schema.freeFvarNames := by
  cases shape with
  | metavariable name =>
    cases matched
    intro queried member
    have same : queried = name := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using member
    subst queried
    exact ⟨target, by simp [Bindings.lookup]⟩
  | constructor label arguments shapes =>
    cases matched with
    | apply argumentsMatched _ =>
      simpa only [Pattern.freeFvarNames] using raw_matching_arguments_defined shapes argumentsMatched
 termination_by sizeOf schema

 theorem raw_matching_arguments_defined {schemas targets : List Pattern} {bindings : Bindings}
    (shapes : ∀ schema ∈ schemas, FirstOrder schema) (matched : MatchArgsRel schemas targets bindings) :
    Defined bindings (schemas.flatMap Pattern.freeFvarNames) := by
  cases schemas with
  | nil => intro _ member; cases member
  | cons schema schemas =>
    cases matched with
    | cons first rest merged =>
      have firstDefined := raw_matching_defined (shapes schema (by simp)) first
      have restDefined := raw_matching_arguments_defined
        (fun child member => shapes child (List.mem_cons_of_mem _ member)) rest
      intro name member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with earlier | later
      · obtain ⟨value, read⟩ := firstDefined name earlier
        exact ⟨value, MatchBindingExtension.lookup_preserved
          (fun _ _ selected => mergeBindings_subsumed_left merged selected) read⟩
      · obtain ⟨value, read⟩ := restDefined name later
        exact ⟨value, MatchBindingExtension.lookup_preserved
          (fun _ _ selected => mergeBindings_subsumed_right merged selected) read⟩
 termination_by sizeOf schemas
end

mutual
 theorem scoped_instance {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : RewriteRule} {site : RulePatternSite} {path : List Nat} {schema : Pattern}
    {environment : Bindings} {initial : ScopedRuleMatching.Assignment}
    (shape : FirstOrder schema) (coherent : NameCoherent rule site path schema)
    (defined : Defined environment schema.freeFvarNames)
    (typed : CapturesTyped language free bound rule.typeContext environment)
    (unique : (rule.typeContext.map Prod.fst).Nodup)
    (before : ScopedCompatible bound.length environment initial) :
    ∃ final, Matches rule (GeneralRuleBindingInference.inferredSpec rule) bound.length site path 0
      initial schema (applyBindings environment schema) final ∧
      ScopedCompatible bound.length environment final := by
  cases shape with
  | metavariable name =>
    obtain ⟨body, read⟩ := defined name (by simp [Pattern.freeFvarNames])
    obtain ⟨expected, declared, sorted⟩ := typed (name, body) (raw_lookup_member read)
    obtain ⟨final, captured, compatible⟩ := capture_instance before read
      (inferred_dependencies_of_lookup rule unique declared) coherent sorted.1.isWellScopedAt
    refine ⟨final, ?_, compatible⟩
    simpa only [apply_variable, read, Option.getD_some] using Matches.capture captured
  | constructor label arguments shapes =>
    obtain ⟨final, matched, compatible⟩ := scoped_arguments_instance shapes coherent.arguments
      (by simpa only [Pattern.freeFvarNames] using defined) typed unique before
    refine ⟨final, ?_, compatible⟩
    simpa only [applyBindings] using (Matches.constructor matched :
      Matches rule (GeneralRuleBindingInference.inferredSpec rule) bound.length site path 0 initial
        (.apply label arguments) (.apply label (arguments.map (applyBindings environment))) final)
 termination_by sizeOf schema

 theorem scoped_arguments_instance {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : RewriteRule} {site : RulePatternSite} {path : List Nat} {index : Nat} {schemas : List Pattern}
    {environment : Bindings} {initial : ScopedRuleMatching.Assignment}
    (shapes : ∀ schema ∈ schemas, FirstOrder schema)
    (coherent : ArgumentsNameCoherent rule site path index schemas)
    (defined : Defined environment (schemas.flatMap Pattern.freeFvarNames))
    (typed : CapturesTyped language free bound rule.typeContext environment)
    (unique : (rule.typeContext.map Prod.fst).Nodup)
    (before : ScopedCompatible bound.length environment initial) :
    ∃ final, Arguments rule (GeneralRuleBindingInference.inferredSpec rule) bound.length site path 0
      initial index schemas (schemas.map (applyBindings environment)) final ∧
      ScopedCompatible bound.length environment final := by
  cases schemas with
  | nil => exact ⟨initial, .nil, before⟩
  | cons schema schemas =>
    obtain ⟨middle, first, firstCompatible⟩ := scoped_instance (shapes schema (by simp)) coherent.head
      (fun name member => defined name (by simp [member])) typed unique before
    obtain ⟨final, rest, compatible⟩ := scoped_arguments_instance
      (fun child member => shapes child (List.mem_cons_of_mem _ member)) coherent.tail
      (fun name member => defined name (by simp [member])) typed unique firstCompatible
    exact ⟨final, .cons first rest, compatible⟩
 termination_by sizeOf schemas
end

 theorem ScopedCompatible.typed {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : RewriteRule} {environment : Bindings} {assignment : ScopedRuleMatching.Assignment}
    (compatible : ScopedCompatible bound.length environment assignment)
    (typed : CapturesTyped language free bound rule.typeContext environment)
    (unique : (rule.typeContext.map Prod.fst).Nodup) :
    ConditionalEquationExecution.AssignmentTyped language free bound rule
      (GeneralRuleBindingInference.inferredSpec rule) assignment ∧
    ConditionalEquationExecution.AssignmentObjects assignment := by
  constructor
  · intro name value member
    obtain ⟨empty, caller, read⟩ := compatible (name, value) member
    obtain ⟨expected, declared, bodyTyped⟩ := typed (name, value.body) (raw_lookup_member read)
    exact ⟨[], expected, inferred_dependencies_of_lookup rule unique declared, declared,
      empty, caller, bodyTyped.1⟩
  · intro name value member
    obtain ⟨_, _, read⟩ := compatible (name, value) member
    exact (typed (name, value.body) (raw_lookup_member read)).choose_spec.2.2.2.1

 theorem ScopedCompatible.rootValues {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : RewriteRule} {environment : Bindings} {assignment : ScopedRuleMatching.Assignment}
    (compatible : ScopedCompatible bound.length environment assignment)
    (typed : CapturesTyped language free bound rule.typeContext environment) :
    GeneralPremise.RootValues bound.length assignment := by
  intro name value selected
  obtain ⟨empty, caller, read⟩ := compatible (name, value)
    (ConditionalEquationExecution.lookup_assignment_member _ _ _ selected)
  exact ⟨empty, caller, (typed (name, value.body) (raw_lookup_member read)).choose_spec.2.1.isWellScopedAt⟩

 theorem ScopedCompatible.lookup {ambient : Nat} {environment : Bindings}
    {assignment : ScopedRuleMatching.Assignment} (compatible : ScopedCompatible ambient environment assignment)
    {name : String} {value : ContextualValue} (found : lookup assignment name = some value) :
    environment.lookup name = some value.body :=
    (compatible (name, value) (ConditionalEquationExecution.lookup_assignment_member _ _ _ found)).2.2

 theorem ScopedCompatible.readout {ambient : Nat} {environment : Bindings}
    {assignment : ScopedRuleMatching.Assignment} {schema : Pattern}
    (compatible : ScopedCompatible ambient environment assignment) (shape : FirstOrder schema)
    (defined : GeneralPremise.BoundNames assignment schema.freeFvarNames) :
    applyBindings (ordinary assignment) schema = applyBindings environment schema := by
  apply apply_eq_of_same_lookups shape
  intro name member
  obtain ⟨value, found⟩ := defined name member
  rw [ordinary_lookup, found, Option.map_some, compatible.lookup found]

mutual
 theorem instantiation_total {rule : RewriteRule} {operation : Pattern → Pattern → Pattern}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {assignment : ScopedRuleMatching.Assignment}
    {schema : Pattern} (shape : FirstOrder schema) (coherent : NameCoherent rule site path schema)
    (defined : GeneralPremise.BoundNames assignment schema.freeFvarNames)
    (roots : GeneralPremise.RootValues ambient assignment)
    (declared : ∀ name ∈ schema.freeFvarNames,
      dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some []) :
    ∃ target, instantiateWith? operation rule (GeneralRuleBindingInference.inferredSpec rule)
      ambient site path 0 assignment schema = some target := by
  cases shape with
  | metavariable name =>
    obtain ⟨value, found⟩ := defined name (by simp [Pattern.freeFvarNames])
    have arguments : arguments? rule (GeneralRuleBindingInference.inferredSpec rule) name site path = some [] :=
      arguments?_empty_of_declared rule _ name site path
        (declared name (by simp [Pattern.freeFvarNames])) coherent.fvar rfl
    exact ⟨value.body, by simp only [instantiateWith?, found, arguments, Option.bind_eq_bind,
      Option.bind_some, root_value_readout (roots name value found)]⟩
  | constructor label arguments shapes =>
    obtain ⟨targets, read⟩ := instantiation_arguments_total (operation := operation) shapes coherent.arguments
      (by simpa only [Pattern.freeFvarNames] using defined) roots
      (by simpa only [Pattern.freeFvarNames] using declared)
    exact ⟨.apply label targets, by simp only [instantiateWith?, read, Option.bind_eq_bind, Option.bind_some]⟩
 termination_by sizeOf schema

 theorem instantiation_arguments_total {rule : RewriteRule} {operation : Pattern → Pattern → Pattern}
    {ambient index : Nat} {site : RulePatternSite} {path : List Nat} {assignment : ScopedRuleMatching.Assignment}
    {schemas : List Pattern} (shapes : ∀ schema ∈ schemas, FirstOrder schema)
    (coherent : ArgumentsNameCoherent rule site path index schemas)
    (defined : GeneralPremise.BoundNames assignment (schemas.flatMap Pattern.freeFvarNames))
    (roots : GeneralPremise.RootValues ambient assignment)
    (declared : ∀ name ∈ schemas.flatMap Pattern.freeFvarNames,
      dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some []) :
    ∃ targets, instantiateArgsWith? operation rule (GeneralRuleBindingInference.inferredSpec rule)
      ambient site path 0 assignment index schemas = some targets := by
  cases schemas with
  | nil => exact ⟨[], by simp only [instantiateArgsWith?]⟩
  | cons schema schemas =>
    obtain ⟨first, head⟩ := instantiation_total (operation := operation) (shapes schema (by simp)) coherent.head
      (fun name member => defined name (by simp [member])) roots
      (fun name member => declared name (by simp [member]))
    obtain ⟨rest, tail⟩ := instantiation_arguments_total (operation := operation)
      (fun child member => shapes child (List.mem_cons_of_mem _ member)) coherent.tail
      (fun name member => defined name (by simp [member])) roots
      (fun name member => declared name (by simp [member]))
    exact ⟨first :: rest, by simp only [instantiateArgsWith?, head, tail,
      Option.bind_eq_bind, Option.bind_some]⟩
 termination_by sizeOf schemas
end

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
