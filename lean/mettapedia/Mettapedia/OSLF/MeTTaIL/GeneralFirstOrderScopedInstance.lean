import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderReadout
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderTyping
import Mettapedia.OSLF.MeTTaIL.MatchBindingExtension
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCaptureRepresentations
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCanonicalProjection

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

 theorem context_filter_of_lookup {α : Type} (context : List (String × α)) {name : String} {type : α}
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

private theorem context_lookup_of_member {α : Type} {context : List (String × α)}
    {name : String} {type : α} (unique : (context.map Prod.fst).Nodup)
    (member : (name,type) ∈ context) : context.lookup name = some type := by
  induction context with
  | nil => cases member
  | cons entry rest ih =>
    rcases entry with ⟨key,value⟩
    have distinct := List.nodup_cons.mp (by simpa only [List.map_cons] using unique)
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact List.lookup_cons_self
    · have different : name ≠ key := by
        intro same
        exact distinct.1 (same ▸ List.mem_map_of_mem later)
      simpa only [List.lookup,show (name == key) = false from by simp [different]] using ih distinct.2 later

/-- Source admission covers the real authored type context exactly. Together
with its zero-dependency check it yields the actual dependency lookup, without
replacing an explicit specification by the inferred one. -/
theorem dependencies_empty_of_admitted {rule : RewriteRule} {spec : RuleBindingSpec}
    {name : String} {type : TypeExpr} (admitted : admittedFor rule spec = true)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    (declared : rule.typeContext.lookup name = some type) : dependencies? spec name = some [] := by
  have checks := admitted
  simp only [admittedFor,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨before,after,contextEq,_⟩ := List.lookup_eq_some_iff.mp declared
  have member : (name,type) ∈ rule.typeContext := by rw [contextEq]; simp
  obtain ⟨entry,entryMember,sameName⟩ := List.any_eq_true.mp (List.all_eq_true.mp checks.1.2 _ member)
  rcases entry with ⟨key,dependencies⟩
  have equal : key = name := by simpa only [beq_iff_eq] using sameName
  subst key
  have lookup := context_lookup_of_member checks.1.1.1.1.2 entryMember
  have filtered := context_filter_of_lookup spec.dependencies checks.1.1.1.1.2 lookup
  have found : dependencies? spec name = some dependencies := by
    simp only [dependencies?,filtered]
  have empty := GeneralPremise.checkZeroDependencies_sound spec zero name dependencies found
  simpa only [empty] using found

#print axioms dependencies_empty_of_admitted

/-- An admitted dependency-free authored occurrence reads the empty spine
whether it is implicit or explicitly retained in the source table. -/
theorem arguments_empty_of_admitted {rule : RewriteRule} {spec : RuleBindingSpec}
    {name : String} {site : RulePatternSite} {path : List Nat}
    (admitted : admittedFor rule spec = true)
    (dependency : dependencies? spec name = some [])
    (actual : occurrenceDeclared rule {name,site,path,arguments := []} = true) :
    arguments? rule spec name site path = some [] := by
  have checks := admitted
  simp only [admittedFor,Bool.and_eq_true,decide_eq_true_eq] at checks
  have unique : (spec.occurrences.map fun row => (row.name,row.site,row.path)).Nodup :=
    checks.1.1.1.2
  let selected := spec.occurrences.filter
    (fun row => row.name == name && row.site == site && row.path == path)
  have rowKey : ∀ row ∈ selected,(row.name,row.site,row.path) = (name,site,path) := by
    intro row member
    have conditions := (List.mem_filter.mp member).2
    simp only [Bool.and_eq_true,beq_iff_eq] at conditions
    rcases conditions with ⟨⟨a,b⟩,c⟩
    exact Prod.ext a (Prod.ext b c)
  have selectedUnique : (selected.map fun row => (row.name,row.site,row.path)).Nodup :=
    unique.sublist ((List.filter_sublist ..).map _)
  cases found : selected with
  | nil =>
    exact arguments?_empty_of_declared rule spec name site path dependency actual found
  | cons row tail =>
    have firstKey := rowKey row (by simp [found])
    have tailEmpty : tail = [] := by
      cases tail with
      | nil => rfl
      | cons other rest =>
        have otherKey := rowKey other (by simp [found])
        have notMember := (List.nodup_cons.mp (by
          simpa only [found,List.map_cons] using selectedUnique)).1
        exact False.elim (notMember (by simp [firstKey,otherKey]))
    have rowMember : row ∈ spec.occurrences :=
      List.mem_of_mem_filter (show row ∈ selected by simp [found])
    have rowChecked := List.all_eq_true.mp checks.2 row rowMember
    have rowName : row.name = name := congrArg Prod.fst firstKey
    rw [rowName,dependency] at rowChecked
    cases depth : occurrenceDepthAtSite? rule row.site row.path with
    | none => simp [depth] at rowChecked
    | some value =>
      simp only [depth,Bool.and_eq_true,beq_iff_eq,List.length_nil] at rowChecked
      have empty : row.arguments = [] := List.eq_nil_of_length_eq_zero rowChecked.2.1
      have matching : spec.occurrences.filter
          (fun row => row.name == name && row.site == site && row.path == path) = [row] := by
        simpa only [tailEmpty] using found
      rw [arguments?_explicit_contract rule spec name site path row [] dependency
        (by simp only [empty,List.length_nil]) matching rowChecked.1,empty]

#print axioms arguments_empty_of_admitted

 theorem capture_instance_with_arguments {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {environment : Bindings} {initial : ScopedRuleMatching.Assignment} {name : String} {target : Pattern}
    (before : ScopedCompatible ambient environment initial)
    (valueRead : environment.lookup name = some target)
    (dependency : dependencies? spec name = some [])
    (arguments : arguments? rule spec name site path = some [])
    (scopeProof : target.isWellScopedAt ambient = true) :
    ∃ final, capture? rule spec ambient 0 site path initial name target = some final ∧
      ScopedCompatible ambient environment final := by
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

 theorem capture_instance {rule : RewriteRule} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {environment : Bindings} {initial : ScopedRuleMatching.Assignment} {name : String} {target : Pattern}
    (before : ScopedCompatible ambient environment initial)
    (valueRead : environment.lookup name = some target)
    (dependency : dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some [])
    (coherent : NameCoherent rule site path (.fvar name)) (scopeProof : target.isWellScopedAt ambient = true) :
    ∃ final, capture? rule (GeneralRuleBindingInference.inferredSpec rule) ambient 0 site path initial name target = some final ∧
      ScopedCompatible ambient environment final := by
  exact capture_instance_with_arguments before valueRead dependency
    (arguments?_empty_of_declared rule _ name site path dependency coherent.fvar rfl) scopeProof

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

 theorem ScopedCompatible.typed_with_dependencies {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {environment : Bindings} {assignment : ScopedRuleMatching.Assignment}
    (compatible : ScopedCompatible bound.length environment assignment)
    (typed : CapturesTyped language free bound rule.typeContext environment)
    (dependencies : ∀ name type,rule.typeContext.lookup name = some type → dependencies? spec name = some []) :
    ConditionalEquationExecution.AssignmentTyped language free bound rule
      spec assignment ∧
    ConditionalEquationExecution.AssignmentObjects assignment := by
  constructor
  · intro name value member
    obtain ⟨empty, caller, read⟩ := compatible (name, value) member
    obtain ⟨expected, declared, bodyTyped⟩ := typed (name, value.body) (raw_lookup_member read)
    exact ⟨[], expected, dependencies name expected declared, declared,
      empty, caller, bodyTyped.1⟩
  · intro name value member
    obtain ⟨_, _, read⟩ := compatible (name, value) member
    exact (typed (name, value.body) (raw_lookup_member read)).choose_spec.2.2.2.1

 theorem ScopedCompatible.typed {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : RewriteRule} {environment : Bindings} {assignment : ScopedRuleMatching.Assignment}
    (compatible : ScopedCompatible bound.length environment assignment)
    (typed : CapturesTyped language free bound rule.typeContext environment)
    (unique : (rule.typeContext.map Prod.fst).Nodup) :
    ConditionalEquationExecution.AssignmentTyped language free bound rule
      (GeneralRuleBindingInference.inferredSpec rule) assignment ∧
    ConditionalEquationExecution.AssignmentObjects assignment := by
  exact compatible.typed_with_dependencies typed
    (fun _ _ declared => inferred_dependencies_of_lookup rule unique declared)

/-- Read the actual admitted specification while retaining every typed body
and object condition of the ordinary capture store. -/
theorem ScopedCompatible.typed_admitted {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec}
    {environment : Bindings} {assignment : ScopedRuleMatching.Assignment}
    (compatible : ScopedCompatible bound.length environment assignment)
    (typed : CapturesTyped language free bound rule.typeContext environment)
    (admitted : admittedFor rule spec = true) (zero : GeneralPremise.checkZeroDependencies spec = true) :
    ConditionalEquationExecution.AssignmentTyped language free bound rule spec assignment ∧
      ConditionalEquationExecution.AssignmentObjects assignment := by
  exact compatible.typed_with_dependencies typed
    (fun _ _ declared => dependencies_empty_of_admitted admitted zero declared)

#print axioms ScopedCompatible.typed_with_dependencies
#print axioms ScopedCompatible.typed_admitted

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


/-! ## Ordinary witnesses map through recursive collection schemas -/

/-- Collection elements use the same authored child addresses as constructor
arguments. The rest occupies the following address and is handled separately. -/
theorem NameCoherent.collection_arguments {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {kind : CollType} {schemas : List Pattern} {rest : Option String}
    (coherent : NameCoherent rule site path (.collection kind schemas rest)) :
    ArgumentsNameCoherent rule site path 0 schemas := by
  intro offset schema selected suffix
  have within : offset < schemas.length := (List.getElem?_eq_some_iff.mp selected).1
  have read := coherent (offset :: suffix)
  simpa only [Nat.zero_add,List.append_assoc,List.singleton_append,occurrenceAt?,
    if_pos within,selected,Option.bind_some] using read

/-- A rest capture is the real final occurrence in the authored collection
schema, independent of the number of target elements remaining at that point. -/
theorem NameCoherent.collection_rest {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {kind : CollType} {schemas : List Pattern} {name : String}
    (coherent : NameCoherent rule site path (.collection kind schemas (some name))) :
    NameCoherent rule site (path ++ [schemas.length]) (.fvar name) := by
  intro suffix
  have read := coherent (schemas.length :: suffix)
  cases suffix <;> simpa only [List.append_assoc,List.singleton_append,occurrenceAt?,
    Nat.lt_irrefl,if_false,beq_self_eq_true,List.isEmpty_nil,List.isEmpty_cons,
    Bool.and_self,Bool.true_and,Bool.false_eq_true,↓reduceIte] using read

/-- Every actual pair on either side of a successful merge is retained.
This concerns pair membership, including repeated names in the supplied row. -/
theorem mergeBindings_right_subset {first second combined : Bindings}
    (merged : mergeBindings first second = some combined) : second ⊆ combined := by
  induction second generalizing first with
  | nil => simp
  | cons entry rest ih =>
    rcases entry with ⟨name,value⟩
    simp only [mergeBindings,List.foldlM_cons] at merged
    cases found : first.find? (fun entry => entry.1 == name) with
    | none =>
      simp only [found] at merged
      have prefixKept := LinearMatch.mergeBindings_subset ((name,value) :: first) rest merged
      have restKept := ih merged
      intro entry member
      rcases List.mem_cons.mp member with rfl | later
      · exact prefixKept (List.mem_cons_self ..)
      · exact restKept later
    | some previous =>
      simp only [found] at merged
      split at merged
      next equal =>
        have sameValue : previous.2 = value := beq_iff_eq.mp equal
        have sameName : previous.1 = name := beq_iff_eq.mp (List.find?_some (p := fun entry : String × Pattern => entry.1 == name) found)
        have entryMember : (name,value) ∈ first := by
          have original := List.mem_of_find?_eq_some found
          simpa only [← sameName,← sameValue,Prod.mk.eta] using original
        have prefixKept := LinearMatch.mergeBindings_subset first rest merged
        have restKept := ih merged
        intro entry member
        rcases List.mem_cons.mp member with rfl | later
        · exact prefixKept entryMember
        · exact restKept later
      next => cases merged

theorem compatible_merge_components {environment first second combined : Bindings}
    (merged : mergeBindings first second = some combined)
    (compatible : Compatible environment combined) :
    Compatible environment first ∧ Compatible environment second :=
  ⟨fun entry member => compatible entry (LinearMatch.mergeBindings_subset first second merged member),
   fun entry member => compatible entry (mergeBindings_right_subset merged member)⟩

private theorem wellScopedList_of_members {ambient : Nat} {targets : List Pattern}
    (scopes : ∀ target ∈ targets,target.isWellScopedAt ambient = true) :
    Pattern.isWellScopedListAt ambient targets = true := by
  induction targets with
  | nil => rfl
  | cons head tail ih =>
    simp only [Pattern.isWellScopedListAt,Bool.and_eq_true]
    exact ⟨scopes head (by simp),ih (fun target member => scopes target (List.mem_cons_of_mem _ member))⟩

private theorem wellScopedList_members {ambient : Nat} {targets : List Pattern}
    (scopes : Pattern.isWellScopedListAt ambient targets = true) :
    ∀ target ∈ targets,target.isWellScopedAt ambient = true := by
  induction targets with
  | nil => intro _ member; cases member
  | cons head tail ih =>
    simp only [Pattern.isWellScopedListAt,Bool.and_eq_true] at scopes
    intro target member
    rcases List.mem_cons.mp member with rfl | later
    · exact scopes.1
    · exact ih scopes.2 target later

private theorem objectList_members {targets : List Pattern}
    (objects : isObjectPatternList targets = true) : ∀ target ∈ targets,isObjectPattern target = true := by
  induction targets with
  | nil => intro _ member; cases member
  | cons head tail ih =>
    simp only [isObjectPatternList,Bool.and_eq_true] at objects
    intro target member
    rcases List.mem_cons.mp member with rfl | later
    · exact objects.1
    · exact ih objects.2 target later

mutual
/-- An actual ordinary match has the scoped match with the same target and
collection choices when its real occurrences are dependency-free and the
subject is an object scopeMatch in the caller context. These are primitive source
eligibility checks, not an assumed agreement of the two match judgments. -/
theorem binderFree_scoped_of_matchRel_with_arguments {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {schema target : Pattern}
    {environment bindings : Bindings} {initial : Assignment}
    (occurrencesReady : ∀ name site path,dependencies? spec name = some [] →
      occurrenceDeclared rule {name,site,path,arguments := []} = true →
      arguments? rule spec name site path = some [])
    (shape : binderFree schema = true) (coherent : NameCoherent rule site path schema)
    (declared : ∀ name ∈ schema.freeFvarNames,
      dependencies? spec name = some [])
    (matched : MatchRel schema target bindings) (compatible : Compatible environment bindings)
    (scope : target.isWellScopedAt ambient = true) (object : isObjectPattern target = true)
    (before : ScopedCompatible ambient environment initial) :
    ∃ final,Matches rule spec
        ambient site path 0 initial schema target final ∧ ScopedCompatible ambient environment final := by
  cases schema with
  | fvar name =>
    cases matched
    have valueRead := compatible (name,target) (List.mem_singleton_self _)
    obtain ⟨final,captured,after⟩ := capture_instance_with_arguments before valueRead
      (declared name (by simp [Pattern.freeFvarNames]))
      (occurrencesReady name site path (declared name (by simp [Pattern.freeFvarNames])) coherent.fvar) scope
    exact ⟨final,.capture captured,after⟩
  | bvar index => cases matched; exact ⟨initial,.bound,before⟩
  | apply label schemas =>
    cases matched with
    | apply children _ =>
      obtain ⟨final,scopeMatch,after⟩ := binderFree_scoped_of_matchArgsRel_with_arguments occurrencesReady shape coherent.arguments
        (by simpa only [Pattern.freeFvarNames] using declared) children compatible
        (wellScopedList_members scope) (objectList_members object) before
      exact ⟨final,.constructor scopeMatch,after⟩
  | lambda | multiLambda | subst => simp only [binderFree,Bool.false_eq_true] at shape
  | collection kind schemas rest =>
    have noRest : ∀ {actualKind targets actualRest},target = .collection actualKind targets actualRest →
        actualRest = none := by
      intro actualKind targets actualRest same
      rw [same] at object
      exact Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp object).1
    cases matched with
    | @collection _ _ _ targets _ actualRest nonvector children =>
      have restEq : actualRest = none := noRest rfl
      subst actualRest
      obtain ⟨final,scopeMatch,after⟩ := binderFree_scoped_of_matchBagRel_with_arguments occurrencesReady shape coherent.collection_arguments
        (fun name same => by subst rest; simpa only [Nat.zero_add] using coherent.collection_rest)
        (by simpa only [Pattern.freeFvarNames] using declared) children compatible
        (wellScopedList_members scope) (objectList_members (Bool.and_eq_true_iff.mp object).2) before
      exact ⟨final,.bag nonvector scopeMatch,after⟩
    | @vector _ targets _ actualRest children =>
      have restEq : actualRest = none := noRest rfl
      subst actualRest
      obtain ⟨final,scopeMatch,after⟩ := binderFree_scoped_of_matchArgsRel_with_arguments occurrencesReady shape coherent.collection_arguments
        (by simpa only [Pattern.freeFvarNames,Option.toList_none,List.append_nil] using declared)
        children compatible (wellScopedList_members scope)
        (objectList_members (Bool.and_eq_true_iff.mp object).2) before
      exact ⟨final,.vector scopeMatch,after⟩
    | @vectorRest _ prefixBindings name _ targets actualRest children merged =>
      have restEq : actualRest = none := noRest rfl
      subst actualRest
      obtain ⟨prefixCompatible,restCompatible⟩ := compatible_merge_components merged compatible
      obtain ⟨middle,scopeMatch,middleCompatible⟩ := binderFree_scoped_of_matchArgsRel_with_arguments occurrencesReady shape
        coherent.collection_arguments
        (fun queried member => declared queried (by simp [Pattern.freeFvarNames,member]))
        children prefixCompatible
        (fun child member => wellScopedList_members scope child (List.mem_of_mem_take member))
        (fun child member => objectList_members (Bool.and_eq_true_iff.mp object).2 child
          (List.mem_of_mem_take member)) before
      have restScope : (.collection .vec (targets.drop schemas.length) none : Pattern).isWellScopedAt ambient = true :=
        wellScopedList_of_members (fun child member =>
          wellScopedList_members scope child (List.mem_of_mem_drop member))
      obtain ⟨final,captured,after⟩ := capture_instance_with_arguments middleCompatible
        (restCompatible _ (List.mem_singleton_self _))
        (declared name (by simp [Pattern.freeFvarNames]))
        (occurrencesReady name site (path ++ [schemas.length])
          (declared name (by simp [Pattern.freeFvarNames])) coherent.collection_rest.fvar) restScope
      exact ⟨final,.vectorRest scopeMatch captured,after⟩
termination_by sizeOf schema

theorem binderFree_scoped_of_matchArgsRel_with_arguments {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {schemas targets : List Pattern}
    {environment bindings : Bindings} {initial : Assignment}
    (occurrencesReady : ∀ name site path,dependencies? spec name = some [] →
      occurrenceDeclared rule {name,site,path,arguments := []} = true →
      arguments? rule spec name site path = some [])
    (shapes : binderFreeList schemas = true)
    (coherent : ArgumentsNameCoherent rule site path index schemas)
    (declared : ∀ name ∈ schemas.flatMap Pattern.freeFvarNames,
      dependencies? spec name = some [])
    (matched : MatchArgsRel schemas targets bindings) (compatible : Compatible environment bindings)
    (scopes : ∀ target ∈ targets,target.isWellScopedAt ambient = true)
    (objects : ∀ target ∈ targets,isObjectPattern target = true)
    (before : ScopedCompatible ambient environment initial) :
    ∃ final,Arguments rule spec
        ambient site path 0 initial index schemas targets final ∧ ScopedCompatible ambient environment final := by
  cases matched with
  | nil => exact ⟨initial,.nil,before⟩
  | cons head tail merged =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    obtain ⟨headCompatible,tailCompatible⟩ := compatible_merge_components merged compatible
    obtain ⟨middle,headScoped,middleCompatible⟩ := binderFree_scoped_of_matchRel_with_arguments occurrencesReady headShape coherent.head
      (fun name member => declared name (by simp [member]))
      head headCompatible (scopes _ (List.mem_cons_self ..)) (objects _ (List.mem_cons_self ..)) before
    obtain ⟨final,tailScoped,after⟩ := binderFree_scoped_of_matchArgsRel_with_arguments occurrencesReady tailShapes coherent.tail
      (fun name member => declared name (List.mem_append_right _ member)) tail tailCompatible
      (fun target member => scopes target (List.mem_cons_of_mem _ member))
      (fun target member => objects target (List.mem_cons_of_mem _ member)) middleCompatible
    exact ⟨final,.cons headScoped tailScoped,after⟩
termination_by sizeOf schemas

theorem binderFree_scoped_of_matchBagRel_with_arguments {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {schemas targets : List Pattern}
    {kind : CollType} {rest : Option String} {environment bindings : Bindings} {initial : Assignment}
    (occurrencesReady : ∀ name site path,dependencies? spec name = some [] →
      occurrenceDeclared rule {name,site,path,arguments := []} = true →
      arguments? rule spec name site path = some [])
    (shapes : binderFreeList schemas = true)
    (coherent : ArgumentsNameCoherent rule site path index schemas)
    (restCoherent : ∀ name,rest = some name →
      NameCoherent rule site (path ++ [index + schemas.length]) (.fvar name))
    (declared : ∀ name ∈ schemas.flatMap Pattern.freeFvarNames ++ rest.toList,
      dependencies? spec name = some [])
    (matched : MatchBagRel schemas rest kind targets bindings) (compatible : Compatible environment bindings)
    (scopes : ∀ target ∈ targets,target.isWellScopedAt ambient = true)
    (objects : ∀ target ∈ targets,isObjectPattern target = true)
    (before : ScopedCompatible ambient environment initial) :
    ∃ final,Bag rule spec
        ambient site path 0 initial index schemas rest kind targets final ∧ ScopedCompatible ambient environment final := by
  cases matched with
  | nilNoRest => exact ⟨initial,.nil,before⟩
  | @nilRest name _ _ =>
    have restScope : (.collection kind targets none : Pattern).isWellScopedAt ambient = true :=
      wellScopedList_of_members scopes
    obtain ⟨final,captured,after⟩ := capture_instance_with_arguments before (compatible _ (List.mem_singleton_self _))
      (declared name (by simp))
      (occurrencesReady name site (path ++ [index + [].length]) (declared name (by simp))
        (restCoherent name rfl).fvar) restScope
    exact ⟨final,.rest captured,after⟩
  | cons selected within head tail merged =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    obtain ⟨headCompatible,tailCompatible⟩ := compatible_merge_components merged compatible
    obtain ⟨middle,headScoped,middleCompatible⟩ := binderFree_scoped_of_matchRel_with_arguments occurrencesReady headShape coherent.head
      (fun name member => declared name (by simp only [List.flatMap_cons,List.mem_append]; exact Or.inl (Or.inl member)))
      head headCompatible (scopes _ (List.getElem_mem within)) (objects _ (List.getElem_mem within)) before
    obtain ⟨final,tailScoped,after⟩ := binderFree_scoped_of_matchBagRel_with_arguments occurrencesReady tailShapes coherent.tail
      (fun name same => by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using restCoherent name same)
      (fun name member => declared name (by
        simpa only [List.flatMap_cons,List.mem_append,or_assoc] using Or.inr member))
      tail tailCompatible
      (fun target member => scopes target (List.mem_of_mem_eraseIdx member))
      (fun target member => objects target (List.mem_of_mem_eraseIdx member)) middleCompatible
    exact ⟨final,.cons selected within headScoped tailScoped,after⟩
termination_by sizeOf schemas
end

theorem binderFree_scoped_of_matchRel {rule : RewriteRule} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {schema target : Pattern}
    {environment bindings : Bindings} {initial : Assignment}
    (shape : binderFree schema = true) (coherent : NameCoherent rule site path schema)
    (declared : ∀ name ∈ schema.freeFvarNames,
      dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some [])
    (matched : MatchRel schema target bindings) (compatible : Compatible environment bindings)
    (scope : target.isWellScopedAt ambient = true) (object : isObjectPattern target = true)
    (before : ScopedCompatible ambient environment initial) :
    ∃ final,Matches rule (GeneralRuleBindingInference.inferredSpec rule)
        ambient site path 0 initial schema target final ∧ ScopedCompatible ambient environment final := by
  exact binderFree_scoped_of_matchRel_with_arguments
    (fun name site path dependency actual =>
      arguments?_empty_of_declared rule _ name site path dependency actual rfl)
    shape coherent declared matched compatible scope object before

theorem binderFree_scoped_of_matchArgsRel {rule : RewriteRule} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {schemas targets : List Pattern}
    {environment bindings : Bindings} {initial : Assignment}
    (shapes : binderFreeList schemas = true)
    (coherent : ArgumentsNameCoherent rule site path index schemas)
    (declared : ∀ name ∈ schemas.flatMap Pattern.freeFvarNames,
      dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some [])
    (matched : MatchArgsRel schemas targets bindings) (compatible : Compatible environment bindings)
    (scopes : ∀ target ∈ targets,target.isWellScopedAt ambient = true)
    (objects : ∀ target ∈ targets,isObjectPattern target = true)
    (before : ScopedCompatible ambient environment initial) :
    ∃ final,Arguments rule (GeneralRuleBindingInference.inferredSpec rule)
        ambient site path 0 initial index schemas targets final ∧ ScopedCompatible ambient environment final := by
  exact binderFree_scoped_of_matchArgsRel_with_arguments
    (fun name site path dependency actual =>
      arguments?_empty_of_declared rule _ name site path dependency actual rfl)
    shapes coherent declared matched compatible scopes objects before

theorem binderFree_scoped_of_matchBagRel {rule : RewriteRule} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {schemas targets : List Pattern}
    {kind : CollType} {rest : Option String} {environment bindings : Bindings} {initial : Assignment}
    (shapes : binderFreeList schemas = true)
    (coherent : ArgumentsNameCoherent rule site path index schemas)
    (restCoherent : ∀ name,rest = some name →
      NameCoherent rule site (path ++ [index + schemas.length]) (.fvar name))
    (declared : ∀ name ∈ schemas.flatMap Pattern.freeFvarNames ++ rest.toList,
      dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some [])
    (matched : MatchBagRel schemas rest kind targets bindings) (compatible : Compatible environment bindings)
    (scopes : ∀ target ∈ targets,target.isWellScopedAt ambient = true)
    (objects : ∀ target ∈ targets,isObjectPattern target = true)
    (before : ScopedCompatible ambient environment initial) :
    ∃ final,Bag rule (GeneralRuleBindingInference.inferredSpec rule)
        ambient site path 0 initial index schemas rest kind targets final ∧ ScopedCompatible ambient environment final := by
  exact binderFree_scoped_of_matchBagRel_with_arguments
    (fun name site path dependency actual =>
      arguments?_empty_of_declared rule _ name site path dependency actual rfl)
    shapes coherent restCoherent declared matched compatible scopes objects before

theorem binderFree_scoped_of_matchRel_admitted {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {schema target : Pattern}
    {environment bindings : Bindings} {initial : Assignment}
    (admitted : admittedFor rule spec = true)
    (shape : binderFree schema = true) (coherent : NameCoherent rule site path schema)
    (declared : ∀ name ∈ schema.freeFvarNames,
      dependencies? spec name = some [])
    (matched : MatchRel schema target bindings) (compatible : Compatible environment bindings)
    (scope : target.isWellScopedAt ambient = true) (object : isObjectPattern target = true)
    (before : ScopedCompatible ambient environment initial) :
    ∃ final,Matches rule spec
        ambient site path 0 initial schema target final ∧ ScopedCompatible ambient environment final := by
  exact binderFree_scoped_of_matchRel_with_arguments
    (fun _ _ _ dependency actual => arguments_empty_of_admitted admitted dependency actual)
    shape coherent declared matched compatible scope object before


#print axioms NameCoherent.collection_arguments
#print axioms NameCoherent.collection_rest
#print axioms mergeBindings_right_subset
#print axioms compatible_merge_components
#print axioms capture_instance_with_arguments
#print axioms binderFree_scoped_of_matchRel_with_arguments
#print axioms binderFree_scoped_of_matchArgsRel_with_arguments
#print axioms binderFree_scoped_of_matchBagRel_with_arguments
#print axioms binderFree_scoped_of_matchRel_admitted
#print axioms binderFree_scoped_of_matchRel
#print axioms binderFree_scoped_of_matchArgsRel
#print axioms binderFree_scoped_of_matchBagRel


/-- Successful literal merge retains precisely the union of binding names.
The statement identifies no allocation or derivation occurrences. -/
theorem mergeBindings_name_union {first second combined : Bindings}
    (merged : mergeBindings first second = some combined) (name : String) :
    name ∈ combined.map Prod.fst ↔ name ∈ first.map Prod.fst ∨ name ∈ second.map Prod.fst := by
  constructor
  · intro member
    obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp (merge_members merged present) with earlier | later
    · exact Or.inl (List.mem_map_of_mem earlier)
    · exact Or.inr (List.mem_map_of_mem later)
  · rintro (member | member)
    · obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
      exact List.mem_map_of_mem (LinearMatch.mergeBindings_subset first second merged present)
    · obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
      exact List.mem_map_of_mem (mergeBindings_right_subset merged present)

mutual
/-- Every actual raw matching witness binds exactly the schema's free names,
including collection rests. This is independent of presentation order. -/
theorem raw_matching_names_recursive {schema target : Pattern} {bindings : Bindings}
    (matched : MatchRel schema target bindings) : SameNames bindings schema.freeFvarNames :=
  match matched with
  | .fvar => by simp [SameNames,Pattern.freeFvarNames]
  | .bvar => by simp [SameNames,Pattern.freeFvarNames]
  | .apply children _ => by simpa only [Pattern.freeFvarNames] using raw_matching_arguments_names_recursive children
  | .lambda body => by simpa only [Pattern.freeFvarNames] using raw_matching_names_recursive body
  | .multiLambda body => by simpa only [Pattern.freeFvarNames] using raw_matching_names_recursive body
  | .collection _ children => by simpa only [Pattern.freeFvarNames] using raw_matching_bag_names_recursive children
  | .vector children => by
    simpa only [Pattern.freeFvarNames,Option.toList_none,List.append_nil] using raw_matching_arguments_names_recursive children
  | .vectorRest children merged => by
    intro name
    rw [mergeBindings_name_union merged,raw_matching_arguments_names_recursive children name]
    simp only [Pattern.freeFvarNames,Option.toList_some,List.map_cons,List.map_nil,List.mem_cons,
      List.not_mem_nil,or_false,List.mem_append]
  | .subst body replacement merged => by
    intro name
    rw [mergeBindings_name_union merged,raw_matching_names_recursive body name,
      raw_matching_names_recursive replacement name]
    simp only [Pattern.freeFvarNames,List.mem_append]

theorem raw_matching_arguments_names_recursive {schemas targets : List Pattern} {bindings : Bindings}
    (matched : MatchArgsRel schemas targets bindings) : SameNames bindings (schemas.flatMap Pattern.freeFvarNames) :=
  match matched with
  | .nil => by simp [SameNames]
  | .cons head tail merged => by
    intro name
    rw [mergeBindings_name_union merged,raw_matching_names_recursive head name,
      raw_matching_arguments_names_recursive tail name]
    simp only [List.flatMap_cons,List.mem_append]

theorem raw_matching_bag_names_recursive {schemas targets : List Pattern}
    {kind : CollType} {rest : Option String} {bindings : Bindings}
    (matched : MatchBagRel schemas rest kind targets bindings) :
    SameNames bindings (schemas.flatMap Pattern.freeFvarNames ++ rest.toList) :=
  match matched with
  | .nilNoRest => by simp [SameNames]
  | .nilRest => by simp [SameNames]
  | .cons _ _ head tail merged => by
    intro name
    rw [mergeBindings_name_union merged,raw_matching_names_recursive head name,
      raw_matching_bag_names_recursive tail name]
    simp only [List.flatMap_cons,List.mem_append,or_assoc]
end

/-- Each schema name has an actual lookup after a successful raw match. -/
theorem raw_matching_defined_recursive {schema target : Pattern} {bindings : Bindings}
    (matched : MatchRel schema target bindings) : Defined bindings schema.freeFvarNames := by
  intro name member
  exact (lookup_some_iff_mem_names bindings name).mpr ((raw_matching_names_recursive matched name).mpr member)

#print axioms mergeBindings_name_union
#print axioms raw_matching_names_recursive
#print axioms raw_matching_arguments_names_recursive
#print axioms raw_matching_bag_names_recursive
#print axioms raw_matching_defined_recursive


/-! ## Typed total instantiation from retained concrete rests -/

/-- The actual typed capture and zero-dependency certificate give an open
object in the original caller fibre, with its retained canonical metadata. -/
theorem assigned_root_open {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {assignment : Assignment} {name : String} {value : ContextualValue} {expected : TypeExpr}
    (typed : GeneralPremise.TypedAssignment environment context assignment)
    (canonical : GeneralPremise.CanonicalValues assignment)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (found : lookup assignment name = some value)
    (declared : context.rule.typeContext.lookup name = some expected) :
    OpenPatternWellSorted environment.language environment.free context.bound expected value.body := by
  have member := ConditionalEquationExecution.lookup_assignment_member assignment name value found
  obtain ⟨dependencies,type,specified,sortFound,_,_,bodyTyped⟩ := typed.1 name value member
  have empty := GeneralPremise.checkZeroDependencies_sound context.spec zero name dependencies specified
  have same := Option.some.inj (sortFound.symm.trans declared)
  subst type
  rw [empty,List.nil_append] at bodyTyped
  exact ⟨bodyTyped,canonical name value found,typed.2 name value member,bodyTyped.isWellScopedAt⟩

/-- A concrete stored collection has the kind and element type of its actual
rest declaration. Neither shape nor same-kind evidence is inferred merely
from the value's root metadata. -/
theorem assigned_rest_elements {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {assignment : Assignment} {name : String} {value : ContextualValue}
    {kind actualKind : CollType} {elementType : TypeExpr} {elements : List Pattern}
    (typed : GeneralPremise.TypedAssignment environment context assignment)
    (canonical : GeneralPremise.CanonicalValues assignment)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (found : lookup assignment name = some value)
    (declared : context.rule.typeContext.lookup name = some (.collection kind elementType))
    (concrete : value.body = .collection actualKind elements none) :
    actualKind = kind ∧ ElementsHaveType environment.language environment.free context.bound elements elementType ∧
      Pattern.hasCanonicalBinderMetadataList elements = true ∧ isObjectPatternList elements = true := by
  have opened := assigned_root_open typed canonical zero found declared
  rw [concrete] at opened
  cases opened.1 with
  | collection elementsTyped =>
    exact ⟨rfl,elementsTyped,opened.2.1,by
      simpa only [isObjectPattern,Option.isNone_none,Bool.true_and] using opened.2.2.1⟩

private theorem binderFree_representation_target {parameter : TermParam} {schema target : Pattern}
    (shape : binderFree schema = true) (represented : MatchesParameterRepresentation parameter schema) :
    MatchesParameterRepresentation parameter target := by
  cases parameter with
  | simple => trivial
  | abstractionNamed => cases schema <;> simp [MatchesParameterRepresentation,binderFree] at represented shape
  | multiAbstractionNamed => cases schema <;> simp [MatchesParameterRepresentation,binderFree] at represented shape

private theorem instantiated_elements_append {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {first second : List Pattern} {type : TypeExpr}
    (front : ElementsHaveType language free bound first type)
    (back : ElementsHaveType language free bound second type) :
    ElementsHaveType language free bound (first ++ second) type := by
  induction first with
  | nil => exact back
  | cons head tail ih =>
    cases front with
    | cons headTyped tailTyped => exact .cons headTyped (ih tailTyped)

private theorem instantiated_canonical_append {first second : List Pattern}
    (front : Pattern.hasCanonicalBinderMetadataList first = true)
    (back : Pattern.hasCanonicalBinderMetadataList second = true) :
    Pattern.hasCanonicalBinderMetadataList (first ++ second) = true := by
  apply (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mpr
  intro target member
  rcases List.mem_append.mp member with earlier | later
  · exact (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp front target earlier
  · exact (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp back target later

private theorem instantiated_objects_append {first second : List Pattern}
    (front : isObjectPatternList first = true) (back : isObjectPatternList second = true) :
    isObjectPatternList (first ++ second) = true := by
  induction first with
  | nil => exact back
  | cons head tail ih =>
    simp only [isObjectPatternList,Bool.and_eq_true] at front
    simp only [List.cons_append,isObjectPatternList,Bool.and_eq_true]
    exact ⟨front.1,ih front.2⟩

#print axioms assigned_root_open
#print axioms assigned_rest_elements

mutual
/-- An admitted recursive binder-free schema instantiates to a typed open
object when every source name is bound and its actual rest captures are
concrete. The result uses the original occurrence addresses and stored bodies. -/
theorem binderFree_instantiation_total_open {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {operation : Pattern → Pattern → Pattern} {site : RulePatternSite} {path : List Nat}
    {assignment : Assignment} {schema : Pattern} {expected : TypeExpr}
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (typed : GeneralPremise.TypedAssignment environment context assignment)
    (canonical : GeneralPremise.CanonicalValues assignment)
    (shape : binderFree schema = true) (coherent : NameCoherent context.rule site path schema)
    (schemaTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType environment.language
      (FreeTypeContext.ofList context.rule.typeContext) [] schema expected)
    (defined : GeneralPremise.BoundNames assignment schema.freeFvarNames)
    (finite : GeneralPremise.FiniteCaptureNames assignment (GeneralPremise.restCaptureNames schema)) :
    ∃ target,instantiateWith? operation context.rule context.spec context.bound.length site path 0 assignment schema = some target ∧
      OpenPatternWellSorted environment.language environment.free context.bound expected target := by
  cases schema with
  | fvar name =>
    cases schemaTyped with
    | fvar nameTyped =>
      have declared : context.rule.typeContext.lookup name = some expected := by
        simpa only [context_ofList_lookup] using nameTyped
      obtain ⟨value,found⟩ := defined name (by simp [Pattern.freeFvarNames])
      have dependencies := dependencies_empty_of_admitted admitted zero declared
      have arguments := arguments_empty_of_admitted admitted dependencies coherent.fvar
      have read := root_value_readout ((typed.rootValues zero) name value found)
      exact ⟨value.body,by
        simp only [instantiateWith?,found,arguments,read,Option.bind_eq_bind,Option.bind_some],
        assigned_root_open typed canonical zero found declared⟩
  | bvar index => cases schemaTyped with | bvar impossible => simp at impossible
  | lambda | multiLambda | subst => simp only [binderFree,Bool.false_eq_true] at shape
  | apply label schemas =>
    cases schemaTyped with
    | constructor declared ordinary schemasTyped =>
      obtain ⟨targets,read,targetsTyped,targetsCanonical,targetsObjects⟩ :=
        binderFree_instantiation_arguments_total_open (operation := operation) admitted zero typed canonical shape coherent.arguments schemasTyped
          (by simpa only [Pattern.freeFvarNames] using defined)
          (by simpa only [GeneralPremise.restCaptureNames] using finite)
      have targetTyped := HasType.constructor declared ordinary targetsTyped
      refine ⟨_,?_,targetTyped,targetsCanonical,targetsObjects,targetTyped.isWellScopedAt⟩
      simp only [instantiateWith?,read,Option.bind_eq_bind,Option.bind_some]
  | collection kind schemas rest =>
    obtain ⟨elementType,schemasTyped,restTyped,build⟩ : ∃ elementType,
        Mettapedia.GSLT.LanguageDef.RestAwareTyping.ElementsHaveType environment.language
          (FreeTypeContext.ofList context.rule.typeContext) [] schemas elementType ∧
        Mettapedia.GSLT.LanguageDef.RestAwareTyping.RestHasType (FreeTypeContext.ofList context.rule.typeContext)
          kind elementType rest ∧
        (∀ outputs,ElementsHaveType environment.language environment.free context.bound outputs elementType →
          HasType environment.language environment.free context.bound (.collection kind outputs none) expected) := by
      cases schemaTyped with
      | collection children restRole => exact ⟨_,children,restRole,fun _ children => .collection children⟩
      | collectionConstructor declared signature children restRole =>
        exact ⟨_,children,restRole,fun _ children => .collectionConstructor declared signature children⟩
    obtain ⟨explicit,read,explicitTyped,explicitCanonical,explicitObjects⟩ :=
      binderFree_instantiation_elements_total_open (operation := operation) admitted zero typed canonical shape coherent.collection_arguments schemasTyped
        (fun name member => defined name (by simp only [Pattern.freeFvarNames]; exact List.mem_append_left _ member))
        (fun name member => finite name (by simp only [GeneralPremise.restCaptureNames]; exact List.mem_append_left _ member))
    cases rest with
    | none =>
      have targetTyped := build explicit explicitTyped
      exact ⟨.collection kind explicit none,by simp only [instantiateWith?,read,Option.bind_eq_bind,Option.bind_some],
        targetTyped,explicitCanonical,by
          simpa only [isObjectPattern,Option.isNone_none,Bool.true_and] using explicitObjects,targetTyped.isWellScopedAt⟩
    | some name =>
      obtain ⟨value,actualKind,residual,found,concrete⟩ := finite name (by simp [GeneralPremise.restCaptureNames])
      have declared : context.rule.typeContext.lookup name = some (.collection kind elementType) := by
        simpa only [Mettapedia.GSLT.LanguageDef.RestAwareTyping.RestHasType,context_ofList_lookup] using restTyped
      obtain ⟨sameKind,residualTyped,residualCanonical,residualObjects⟩ :=
        assigned_rest_elements typed canonical zero found declared concrete
      subst actualKind
      have dependencies := dependencies_empty_of_admitted admitted zero declared
      have arguments := arguments_empty_of_admitted admitted dependencies coherent.collection_rest.fvar
      have valueRead := root_value_readout ((typed.rootValues zero) name value found)
      have targetTyped := build (explicit ++ residual) (instantiated_elements_append explicitTyped residualTyped)
      exact ⟨.collection kind (explicit ++ residual) none,by
        simp only [instantiateWith?,read,found,arguments,valueRead,concrete,Option.bind_eq_bind,
          Option.bind_some,beq_self_eq_true,↓reduceIte],targetTyped,
        instantiated_canonical_append explicitCanonical residualCanonical,by
          simpa only [isObjectPattern,Option.isNone_none,Bool.true_and] using
            instantiated_objects_append explicitObjects residualObjects,targetTyped.isWellScopedAt⟩
termination_by sizeOf schema

theorem binderFree_instantiation_arguments_total_open {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {operation : Pattern → Pattern → Pattern} {site : RulePatternSite} {path : List Nat} {index : Nat}
    {assignment : Assignment} {schemas : List Pattern} {parameters : List TermParam}
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (typed : GeneralPremise.TypedAssignment environment context assignment)
    (canonical : GeneralPremise.CanonicalValues assignment)
    (shapes : binderFreeList schemas = true) (coherent : ArgumentsNameCoherent context.rule site path index schemas)
    (schemasTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.ArgumentsHaveTypes environment.language
      (FreeTypeContext.ofList context.rule.typeContext) [] schemas parameters)
    (defined : GeneralPremise.BoundNames assignment (schemas.flatMap Pattern.freeFvarNames))
    (finite : GeneralPremise.FiniteCaptureNames assignment (schemas.flatMap GeneralPremise.restCaptureNames)) :
    ∃ targets,instantiateArgsWith? operation context.rule context.spec context.bound.length site path 0 assignment index schemas = some targets ∧
      ArgumentsHaveTypes environment.language environment.free context.bound targets parameters ∧
      Pattern.hasCanonicalBinderMetadataList targets = true ∧ isObjectPatternList targets = true := by
  cases schemas with
  | nil => cases schemasTyped; exact ⟨[],by simp only [instantiateArgsWith?],.nil,rfl,rfl⟩
  | cons schema schemas =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    cases schemasTyped with
    | cons represented typeFound headTyped tailTyped =>
      obtain ⟨first,headRead,firstOpen⟩ := binderFree_instantiation_total_open (operation := operation) admitted zero typed canonical
        headShape coherent.head headTyped
        (fun name member => defined name (by simp [member]))
        (fun name member => finite name (by simp [member]))
      obtain ⟨rest,tailRead,restTyped,restCanonical,restObjects⟩ :=
        binderFree_instantiation_arguments_total_open (operation := operation) admitted zero typed canonical tailShapes coherent.tail tailTyped
          (fun name member => defined name (by simp [member]))
          (fun name member => finite name (by simp [member]))
      exact ⟨first::rest,by simp only [instantiateArgsWith?,headRead,tailRead,Option.bind_eq_bind,Option.bind_some],
        .cons (binderFree_representation_target headShape represented) typeFound firstOpen.1 restTyped,
        by simp only [Pattern.hasCanonicalBinderMetadataList,firstOpen.2.1,restCanonical,Bool.true_and],
        by simp only [isObjectPatternList,firstOpen.2.2.1,restObjects,Bool.true_and]⟩
termination_by sizeOf schemas

theorem binderFree_instantiation_elements_total_open {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {operation : Pattern → Pattern → Pattern} {site : RulePatternSite} {path : List Nat} {index : Nat}
    {assignment : Assignment} {schemas : List Pattern} {elementType : TypeExpr}
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (typed : GeneralPremise.TypedAssignment environment context assignment)
    (canonical : GeneralPremise.CanonicalValues assignment)
    (shapes : binderFreeList schemas = true) (coherent : ArgumentsNameCoherent context.rule site path index schemas)
    (schemasTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.ElementsHaveType environment.language
      (FreeTypeContext.ofList context.rule.typeContext) [] schemas elementType)
    (defined : GeneralPremise.BoundNames assignment (schemas.flatMap Pattern.freeFvarNames))
    (finite : GeneralPremise.FiniteCaptureNames assignment (schemas.flatMap GeneralPremise.restCaptureNames)) :
    ∃ targets,instantiateArgsWith? operation context.rule context.spec context.bound.length site path 0 assignment index schemas = some targets ∧
      ElementsHaveType environment.language environment.free context.bound targets elementType ∧
      Pattern.hasCanonicalBinderMetadataList targets = true ∧ isObjectPatternList targets = true := by
  cases schemas with
  | nil => exact ⟨[],by simp only [instantiateArgsWith?],.nil _ _,rfl,rfl⟩
  | cons schema schemas =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    cases schemasTyped with
    | cons headTyped tailTyped =>
      obtain ⟨first,headRead,firstOpen⟩ := binderFree_instantiation_total_open (operation := operation) admitted zero typed canonical
        headShape coherent.head headTyped
        (fun name member => defined name (by simp [member]))
        (fun name member => finite name (by simp [member]))
      obtain ⟨rest,tailRead,restTyped,restCanonical,restObjects⟩ :=
        binderFree_instantiation_elements_total_open (operation := operation) admitted zero typed canonical tailShapes coherent.tail tailTyped
          (fun name member => defined name (by simp [member]))
          (fun name member => finite name (by simp [member]))
      exact ⟨first::rest,by simp only [instantiateArgsWith?,headRead,tailRead,Option.bind_eq_bind,Option.bind_some],
        .cons firstOpen.1 restTyped,
        by simp only [Pattern.hasCanonicalBinderMetadataList,firstOpen.2.1,restCanonical,Bool.true_and],
        by simp only [isObjectPatternList,firstOpen.2.2.1,restObjects,Bool.true_and]⟩
termination_by sizeOf schemas
end

#print axioms binderFree_instantiation_total_open
#print axioms binderFree_instantiation_arguments_total_open
#print axioms binderFree_instantiation_elements_total_open

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
