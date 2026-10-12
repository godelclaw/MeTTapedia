import Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution
import Mettapedia.OSLF.MeTTaIL.FocusedRelationQueryExecution
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Typed conditional equation and rule occurrences

This interpreter fixes the finite relation-provider snapshot and executes
ordered relation queries while retaining contextual captures. Each endpoint
and each stored assignment is checked against the authored sort declarations.
Unsupported premises and unavailable root projections are explicit pending
obligations. They do not certify absence of an equation or reduction instance.

Equation orientation is metadata, separate from directed rule execution.
Both use the same scoped matcher, query interpreter and reduct operation.
The relational query judgment below reads provider rows and ordered matching
choices independently of the whole-rule executor.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution

open Syntax RuleBinding ScopedRuleMatching Engine
open ScopedEquationExecution (Orientation orientedRule)
open ScopedPremiseExecution (PremiseEvent)
open Mettapedia.GSLT.LanguageDef.WellSorted
  (FreeTypeContext HasType checkHasType isObjectPattern checkOpenPatternWellSorted
    OpenPatternWellSorted)
open Match

/-- A retained contextual value has its declared sort in its full dependency
and ambient context. Rule metavariable sorts and object free names are separate. -/
def AssignmentTyped (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec)
    (assignment : Assignment) : Prop :=
  ∀ name value, (name, value) ∈ assignment →
    ∃ dependencies expected,
      dependencies? spec name = some dependencies ∧
      rule.typeContext.lookup name = some expected ∧
      value.dependencies = dependencies ∧ value.ambient = bound.length ∧
      HasType language free (dependencies ++ bound) value.body expected

/-- Executable checking of the exact stored contextual values, including
values unused by the next query. -/
def checkAssignment (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec)
    (assignment : Assignment) : Bool :=
  assignment.all fun (name, value) =>
    match dependencies? spec name, rule.typeContext.lookup name with
    | some dependencies, some expected =>
        value.dependencies == dependencies && value.ambient == bound.length &&
          isObjectPattern value.body &&
          checkHasType language free (dependencies ++ bound) value.body expected
    | _, _ => false

theorem checkAssignment_sound {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec}
    {assignment : Assignment}
    (checked : checkAssignment language free bound rule spec assignment = true) :
    AssignmentTyped language free bound rule spec assignment := by
  intro name value member
  have entry := List.all_eq_true.mp checked (name, value) member
  change (match dependencies? spec name, rule.typeContext.lookup name with
    | some dependencies, some expected =>
        value.dependencies == dependencies && value.ambient == bound.length &&
          isObjectPattern value.body &&
          checkHasType language free (dependencies ++ bound) value.body expected
    | _, _ => false) = true at entry
  cases dependencies : dependencies? spec name with
  | none => simp [dependencies] at entry
  | some deps =>
      cases expected : rule.typeContext.lookup name with
      | none => simp [dependencies, expected] at entry
      | some sort =>
          simp only [dependencies, expected, Bool.and_eq_true, beq_iff_eq] at entry
          exact ⟨deps, sort, rfl, rfl, entry.1.1.1, entry.1.1.2,
            Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType_sound entry.2⟩

/-- Stored captures are object terms rather than schema substitutions or
open collection tails. -/
def AssignmentObjects (assignment : Assignment) : Prop :=
  ∀ name value, (name, value) ∈ assignment → isObjectPattern value.body = true

theorem checkAssignment_objects {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec}
    {assignment : Assignment}
    (checked : checkAssignment language free bound rule spec assignment = true) :
    AssignmentObjects assignment := by
  intro name value member
  have entry := List.all_eq_true.mp checked (name, value) member
  cases dependencies : dependencies? spec name <;>
    cases expected : rule.typeContext.lookup name <;>
    simp [dependencies, expected, Bool.and_eq_true] at entry
  exact entry.1.2

theorem checkAssignment_complete {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec}
    {assignment : Assignment}
    (typed : AssignmentTyped language free bound rule spec assignment)
    (objects : AssignmentObjects assignment) :
    checkAssignment language free bound rule spec assignment = true := by
  apply List.all_eq_true.mpr
  rintro ⟨name, value⟩ member
  obtain ⟨dependencies, expected, declared, sorted, metadata, ambient, bodyTyped⟩ :=
    typed name value member
  have bodyChecked := Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType_complete_of_object
    bodyTyped (objects name value member)
  simp [declared, sorted, metadata, ambient, bodyChecked, objects name value member]

theorem lookup_assignment_member (assignment : Assignment) (name : String)
    (value : ContextualValue) (found : lookup assignment name = some value) :
    (name, value) ∈ assignment := by
  unfold lookup at found
  cases selected : assignment.find? (fun entry => entry.1 == name) with
  | none => simp [selected] at found
  | some pair =>
      have member := List.mem_of_find?_eq_some selected
      have named := List.find?_some selected
      simp only [beq_iff_eq] at named
      simp only [selected, Option.map_some, Option.some.injEq] at found
      cases pair with
      | mk actualName actualValue =>
          dsimp only at named found member
          subst actualName
          subst actualValue
          exact member

/-- A root projection cannot erase a local dependency. Its successful
readout is the exact captured body in the caller's ambient context. -/
theorem instantiate_root_readout (value : ContextualValue) (ambient : Nat)
    (result : Pattern) (projected : instantiateValue? value ambient 0 [] = some result) :
    value.dependencies = [] ∧ result = value.body := by
  have empty : value.dependencies = [] := by
    by_contra nonempty
    have lengthPositive : value.dependencies.length ≠ 0 := by simpa using nonempty
    simp [instantiateValue?] at projected
    exact lengthPositive projected.2.1.symm
  have identity : occurrenceAssignment 0 0 [] = Pattern.bvar := by
    funext index
    simp [occurrenceAssignment]
  simp [instantiateValue?, empty, identity,
    ContextSubstitution.substitute_id] at projected
  exact ⟨empty, projected.2.2.symm⟩

/-- Every actually queried captured input has its authored result sort and
ordinary scope after focused projection, including an ambient binder. -/
theorem projected_input_typed (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec)
    (assignment : Assignment) (name : String) (value : ContextualValue)
    (result : Pattern)
    (typed : AssignmentTyped language free bound rule spec assignment)
    (found : lookup assignment name = some value)
    (projected : instantiateValue? value bound.length 0 [] = some result) :
    ∃ expected, rule.typeContext.lookup name = some expected ∧
      HasType language free bound result expected ∧
      result.isWellScopedAt bound.length = true := by
  obtain ⟨dependencies, expected, _, sorted, metadata, _, bodyTyped⟩ :=
    typed name value (lookup_assignment_member assignment name value found)
  obtain ⟨empty, exactBody⟩ := instantiate_root_readout value bound.length result projected
  have emptyDependencies : dependencies = [] := metadata.symm.trans empty
  subst dependencies
  rw [exactBody]
  have rootTyped : HasType language free bound value.body expected := by simpa [empty] using bodyTyped
  exact ⟨expected, sorted, rootTyped, rootTyped.isWellScopedAt⟩

/-- Focused projection checks only requested input names, but every retained
root binding keeps its declared sort and the caller's complete binder context. -/
theorem projectNames?_typed (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec)
    (assignment : Assignment) (names : List String) (root : Bindings)
    (typed : AssignmentTyped language free bound rule spec assignment)
    (projected : FocusedRelationQueryExecution.projectNames? bound.length assignment names = some root) :
    ∀ name result, (name, result) ∈ root →
      ∃ expected, rule.typeContext.lookup name = some expected ∧
        HasType language free bound result expected ∧
        result.isWellScopedAt bound.length = true := by
  induction names generalizing root with
  | nil =>
      simp only [FocusedRelationQueryExecution.projectNames?, Option.some.injEq] at projected
      subst root
      intro name result member
      cases member
  | cons first names ih =>
      cases found : lookup assignment first with
      | none =>
          simp only [FocusedRelationQueryExecution.projectNames?, found] at projected
          exact ih root projected
      | some value =>
          cases readout : instantiateValue? value bound.length 0 [] with
          | none =>
              simp [FocusedRelationQueryExecution.projectNames?, found, readout] at projected
          | some result =>
              cases remaining : FocusedRelationQueryExecution.projectNames? bound.length assignment names with
              | none =>
                  simp [FocusedRelationQueryExecution.projectNames?, found, readout, remaining] at projected
              | some tail =>
                  simp [FocusedRelationQueryExecution.projectNames?, found, readout, remaining] at projected
                  subst root
                  intro name actual member
                  rcases List.mem_cons.mp member with same | later
                  · cases same
                    exact projected_input_typed language free bound rule spec assignment
                      first value result typed found readout
                  · exact ih tail remaining name actual later

/-- Independent query satisfaction selects an actual row, its matcher
extension, and the retained contextual reconciliation. -/
inductive QuerySatisfied (relEnv : RelationEnv) (language : LanguageDef)
    (spec : RuleBindingSpec) (ambient : Nat) (relation : String)
    (arguments : List Pattern) (initial : Assignment) (final : Assignment) : Prop where
  | row (root : Bindings) (tuple : List Pattern) (extension result : Bindings)
      (projected : FocusedRelationQueryExecution.projectNames? ambient initial
        (arguments.flatMap Pattern.freeFvarNames).eraseDups = some root)
      (provided : tuple ∈ builtinRelationTuples language relation
        (arguments.map (applyBindings root)) ++
          relEnv.tuples relation (arguments.map (applyBindings root)))
      (matched : extension ∈ matchRelationArgs root arguments tuple)
      (merged : mergeBindings root extension = some result)
      (reconciled : extendRoot? spec ambient initial result = some final) :
      QuerySatisfied relEnv language spec ambient relation arguments initial final

theorem relationQueryStep_readout (relEnv : RelationEnv) (language : LanguageDef)
    (root result : Bindings) (relation : String) (arguments : List Pattern)
    (member : result ∈ relationQueryStep relEnv language root relation arguments) :
    ∃ tuple extension,
      tuple ∈ builtinRelationTuples language relation (arguments.map (applyBindings root)) ++
        relEnv.tuples relation (arguments.map (applyBindings root)) ∧
      extension ∈ matchRelationArgs root arguments tuple ∧
      mergeBindings root extension = some result := by
  simp only [relationQueryStep, List.mem_flatMap, List.mem_filterMap] at member
  obtain ⟨tuple, provided, extension, matched, merged⟩ := member
  exact ⟨tuple, extension, provided, matched, merged⟩

theorem queryResults_sound (relEnv : RelationEnv) (language : LanguageDef)
    (spec : RuleBindingSpec) (ambient index : Nat) (relation : String)
    (arguments : List Pattern) (initial final : Assignment)
    (event : PremiseEvent Empty)
    (member : (event, final) ∈ FocusedRelationQueryExecution.queryResults
      relEnv language spec ambient index relation arguments initial) :
    QuerySatisfied relEnv language spec ambient relation arguments initial final := by
  obtain ⟨root, result, resultIndex, projected, selected, reconciled, _⟩ :=
    FocusedRelationQueryExecution.queryResults_readout relEnv language spec
      ambient index relation arguments initial final event member
  obtain ⟨tuple, extension, provided, matched, merged⟩ :=
    relationQueryStep_readout relEnv language root result relation arguments
      (List.fst_mem_of_mem_zipIdx selected)
  exact .row root tuple extension result projected provided matched merged reconciled

/-- Provider and matching occurrences remain distinct even for identical
rows or binding results. -/
structure QueryAlternative where
  providerIndex : Nat
  matcherIndex : Nat
  result : Bindings
deriving Repr, DecidableEq

def rowAlternatives (root : Bindings) (arguments tuple : List Pattern)
    (providerIndex : Nat) : List QueryAlternative :=
  (matchRelationArgs root arguments tuple).zipIdx.filterMap fun (extension, matcherIndex) =>
    (mergeBindings root extension).map fun result =>
      { providerIndex, matcherIndex, result }

def queryAlternatives (relEnv : RelationEnv) (language : LanguageDef)
    (root : Bindings) (relation : String) (arguments : List Pattern) : List QueryAlternative :=
  (builtinRelationTuples language relation (arguments.map (applyBindings root)) ++
    relEnv.tuples relation (arguments.map (applyBindings root))).zipIdx.flatMap fun
      (tuple, providerIndex) => rowAlternatives root arguments tuple providerIndex

theorem rowAlternatives_readout (root : Bindings) (arguments tuple : List Pattern)
    (providerIndex : Nat) :
    (rowAlternatives root arguments tuple providerIndex).map QueryAlternative.result =
      (matchRelationArgs root arguments tuple).filterMap (mergeBindings root) := by
  unfold rowAlternatives
  rw [List.map_filterMap]
  have erased : (fun pair : Bindings × Nat =>
      Option.map QueryAlternative.result ((mergeBindings root pair.1).map fun result =>
        { providerIndex, matcherIndex := pair.2, result } : Option QueryAlternative)) =
      fun pair => mergeBindings root pair.1 := by
    funext pair
    cases mergeBindings root pair.1 <;> rfl
  rw [erased]
  change List.filterMap ((mergeBindings root) ∘ Prod.fst)
    (matchRelationArgs root arguments tuple).zipIdx = _
  rw [← List.filterMap_map]
  rw [List.zipIdx_map_fst]

/-- Forgetting the independently retained provider and matcher positions
recovers the engine's query-result list, including order and duplicates. -/
theorem queryAlternatives_readout (relEnv : RelationEnv) (language : LanguageDef)
    (root : Bindings) (relation : String) (arguments : List Pattern) :
    (queryAlternatives relEnv language root relation arguments).map QueryAlternative.result =
      relationQueryStep relEnv language root relation arguments := by
  unfold queryAlternatives
  rw [List.map_flatMap]
  simp only [rowAlternatives_readout]
  change List.flatMap
    (fun pair : List Pattern × Nat => (matchRelationArgs root arguments pair.1).filterMap
      (mergeBindings root))
    (builtinRelationTuples language relation (arguments.map (applyBindings root)) ++
      relEnv.tuples relation (arguments.map (applyBindings root))).zipIdx = _
  rw [← List.flatMap_map Prod.fst
    (fun tuple => (matchRelationArgs root arguments tuple).filterMap (mergeBindings root))]
  rw [List.zipIdx_map_fst]
  rfl

theorem rowAlternatives_origin (root : Bindings) (arguments tuple : List Pattern)
    (providerIndex : Nat) (alternative : QueryAlternative)
    (member : alternative ∈ rowAlternatives root arguments tuple providerIndex) :
    alternative.providerIndex = providerIndex ∧
      ∃ extension,
        (matchRelationArgs root arguments tuple)[alternative.matcherIndex]? = some extension ∧
        mergeBindings root extension = some alternative.result := by
  simp only [rowAlternatives, List.mem_filterMap] at member
  obtain ⟨⟨extension, matcherIndex⟩, selected, represented⟩ := member
  cases merged : mergeBindings root extension with
  | none => simp [merged] at represented
  | some result =>
      simp only [merged, Option.map_some, Option.some.injEq] at represented
      cases represented
      exact ⟨rfl, extension, List.mem_zipIdx_iff_getElem?.mp selected, merged⟩

/-- Every independent query alternative retains actual provider and matcher
positions, including repeated equal rows. -/
theorem queryAlternatives_origin (relEnv : RelationEnv) (language : LanguageDef)
    (root : Bindings) (relation : String) (arguments : List Pattern)
    (alternative : QueryAlternative)
    (member : alternative ∈ queryAlternatives relEnv language root relation arguments) :
    ∃ tuple extension,
      (builtinRelationTuples language relation (arguments.map (applyBindings root)) ++
        relEnv.tuples relation (arguments.map (applyBindings root)))[alternative.providerIndex]? =
          some tuple ∧
      (matchRelationArgs root arguments tuple)[alternative.matcherIndex]? = some extension ∧
      mergeBindings root extension = some alternative.result := by
  simp only [queryAlternatives, List.mem_flatMap] at member
  obtain ⟨⟨tuple, providerIndex⟩, selected, rowMember⟩ := member
  obtain ⟨origin, extension, matched, merged⟩ :=
    rowAlternatives_origin root arguments tuple providerIndex alternative rowMember
  have provided := List.mem_zipIdx_iff_getElem?.mp selected
  rw [← origin] at provided
  exact ⟨tuple, extension, provided, matched, merged⟩

/-- The root event's ordinal selects a concrete provider/matcher occurrence
from the independent candidate presentation; it is not an arbitrary number. -/
inductive QuerySatisfiedAt (relEnv : RelationEnv) (language : LanguageDef)
    (spec : RuleBindingSpec) (ambient resultIndex : Nat) (relation : String)
    (arguments : List Pattern) (initial final : Assignment) : Prop where
  | selected (root : Bindings) (alternative : QueryAlternative)
      (projected : FocusedRelationQueryExecution.projectNames? ambient initial
        (arguments.flatMap Pattern.freeFvarNames).eraseDups = some root)
      (position : (queryAlternatives relEnv language root relation arguments)[resultIndex]? =
        some alternative)
      (reconciled : extendRoot? spec ambient initial alternative.result = some final) :
      QuerySatisfiedAt relEnv language spec ambient resultIndex relation arguments initial final

theorem QuerySatisfiedAt.forget {relEnv : RelationEnv} {language : LanguageDef}
    {spec : RuleBindingSpec} {ambient resultIndex : Nat} {relation : String}
    {arguments : List Pattern} {initial final : Assignment}
    (query : QuerySatisfiedAt relEnv language spec ambient resultIndex
      relation arguments initial final) :
    QuerySatisfied relEnv language spec ambient relation arguments initial final := by
  cases query with
  | selected root alternative projected position reconciled =>
      have member := List.mem_of_getElem? position
      obtain ⟨tuple, extension, provided, matched, merged⟩ :=
        queryAlternatives_origin relEnv language root relation arguments alternative member
      exact .row root tuple extension alternative.result projected
        (List.mem_of_getElem? provided) (List.mem_of_getElem? matched) merged reconciled

theorem queryResults_indexed_sound (relEnv : RelationEnv) (language : LanguageDef)
    (spec : RuleBindingSpec) (ambient index : Nat) (relation : String)
    (arguments : List Pattern) (initial final : Assignment)
    (event : PremiseEvent Empty)
    (member : (event, final) ∈ FocusedRelationQueryExecution.queryResults
      relEnv language spec ambient index relation arguments initial) :
    ∃ resultIndex, event = .root index resultIndex ∧
      QuerySatisfiedAt relEnv language spec ambient resultIndex relation arguments initial final := by
  obtain ⟨root, result, resultIndex, projected, selected, reconciled, eventEq⟩ :=
    FocusedRelationQueryExecution.queryResults_readout relEnv language spec
      ambient index relation arguments initial final event member
  have atResult := List.mem_zipIdx_iff_getElem?.mp selected
  rw [← queryAlternatives_readout] at atResult
  rw [List.getElem?_map] at atResult
  cases alternativeAt : (queryAlternatives relEnv language root relation arguments)[resultIndex]? with
  | none => simp [alternativeAt] at atResult
  | some alternative =>
      simp only [alternativeAt, Option.map_some, Option.some.injEq] at atResult
      exact ⟨resultIndex, eventEq,
        .selected root alternative projected alternativeAt (atResult ▸ reconciled)⟩

theorem queryResults_indexed_complete (relEnv : RelationEnv) (language : LanguageDef)
    (spec : RuleBindingSpec) (ambient index resultIndex : Nat) (relation : String)
    (arguments : List Pattern) (initial final : Assignment)
    (supported : ScopedPremiseExecution.hasOccurrenceAt spec index = false)
    (query : QuerySatisfiedAt relEnv language spec ambient resultIndex
      relation arguments initial final) :
    (PremiseEvent.root index resultIndex, final) ∈
      FocusedRelationQueryExecution.queryResults (Evidence := Empty)
        relEnv language spec ambient index relation arguments initial := by
  cases query with
  | selected root alternative projected position reconciled =>
      have atResult : (relationQueryStep relEnv language root relation arguments)[resultIndex]? =
          some alternative.result := by
        rw [← queryAlternatives_readout, List.getElem?_map, position]
        rfl
      have selected : (alternative.result, resultIndex) ∈
          (relationQueryStep relEnv language root relation arguments).zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr atResult
      unfold FocusedRelationQueryExecution.queryResults
      simp only [supported, Bool.false_eq_true, if_false, projected]
      apply List.mem_filterMap.mpr
      exact ⟨(alternative.result, resultIndex), selected, by simp [reconciled]⟩

/-- Every satisfied row is returned by the finite query interpreter, with
its actual result-list ordinal retained. -/
theorem queryResults_complete (relEnv : RelationEnv) (language : LanguageDef)
    (spec : RuleBindingSpec) (ambient index : Nat) (relation : String)
    (arguments : List Pattern) (initial final : Assignment)
    (supported : ScopedPremiseExecution.hasOccurrenceAt spec index = false)
    (query : QuerySatisfied relEnv language spec ambient relation arguments initial final) :
    ∃ resultIndex, (PremiseEvent.root index resultIndex, final) ∈
      FocusedRelationQueryExecution.queryResults (Evidence := Empty)
        relEnv language spec ambient index relation arguments initial := by
  cases query with
  | row root tuple extension result projected provided matched merged reconciled =>
      have resultMember : result ∈ relationQueryStep relEnv language root relation arguments := by
        simp only [relationQueryStep, List.mem_flatMap, List.mem_filterMap]
        exact ⟨tuple, provided, extension, matched, merged⟩
      obtain ⟨ordinal, below, atOrdinal⟩ := List.mem_iff_getElem.mp resultMember
      have selected : (result, ordinal) ∈
          (relationQueryStep relEnv language root relation arguments).zipIdx := by
        apply List.mem_zipIdx_iff_getElem?.mpr
        simp [List.getElem?_eq_getElem below, atOrdinal]
      refine ⟨ordinal, ?_⟩
      unfold FocusedRelationQueryExecution.queryResults
      simp only [supported, Bool.false_eq_true, if_false, projected]
      apply List.mem_filterMap.mpr
      exact ⟨(result, ordinal), selected, by simp [reconciled]⟩

/-- The supported conditional profile has finite relation queries without
explicit premise occurrence substitutions. -/
def queryArgumentSupported : Pattern → Bool
  | .fvar _ => true
  | _ => false

def querySupported (spec : RuleBindingSpec) (index : Nat) : Premise → Bool
  | .relationQuery _ arguments =>
      !ScopedPremiseExecution.hasOccurrenceAt spec index && arguments.all queryArgumentSupported
  | _ => false

def queriesSupported (spec : RuleBindingSpec) : Nat → List Premise → Bool
  | _, [] => true
  | index, premise :: rest =>
      querySupported spec index premise && queriesSupported spec (index + 1) rest

/-- Ordered successful query events with their exact completed assignment. -/
def typedQueryResults (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (index : Nat) (relation : String)
    (arguments : List Pattern) (initial : Assignment) :
    List (PremiseEvent Empty × Assignment) :=
  if arguments.all queryArgumentSupported then
    (FocusedRelationQueryExecution.queryResults relEnv language spec bound.length
      index relation arguments initial).filter fun (_, completed) =>
        checkAssignment language free bound rule spec completed
  else []

theorem mem_typedQueryResults_iff (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (index : Nat) (relation : String)
    (arguments : List Pattern) (initial final : Assignment) (event : PremiseEvent Empty) :
    (event, final) ∈ typedQueryResults relEnv language free bound rule spec index
      relation arguments initial ↔
      arguments.all queryArgumentSupported = true ∧
        (event, final) ∈ FocusedRelationQueryExecution.queryResults relEnv language spec
          bound.length index relation arguments initial ∧
        checkAssignment language free bound rule spec final = true := by
  by_cases supported : arguments.all queryArgumentSupported = true
  · simp only [typedQueryResults, supported, if_true, List.mem_filter, true_and]
  · simp [typedQueryResults, supported]

def runQueries (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) :
    Nat → List Premise → Assignment → List (Assignment × List (PremiseEvent Empty))
  | _, [], assignment => [(assignment, [])]
  | index, .relationQuery relation arguments :: rest, assignment =>
      (typedQueryResults relEnv language free bound rule spec index
        relation arguments assignment).flatMap fun (event, completed) =>
          (runQueries relEnv language free bound rule spec (index + 1)
            rest completed).map fun (final, history) => (final, event :: history)
  | _, _ :: _, _ => []

/-- The semantic premises use actual relation rows, with one occurrence for
each authored position. The final assignment is typed at every stage. -/
inductive QueriesSatisfied (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) :
    Nat → List Premise → Assignment → Assignment → List (PremiseEvent Empty) → Prop where
  | nil (index : Nat) (assignment : Assignment) :
      QueriesSatisfied relEnv language free bound rule spec index [] assignment assignment []
  | cons (index resultIndex : Nat) (relation : String) (arguments : List Pattern)
      (rest : List Premise) (initial completed final : Assignment)
      (history : List (PremiseEvent Empty))
      (query : QuerySatisfiedAt relEnv language spec bound.length resultIndex
        relation arguments initial completed)
      (typed : AssignmentTyped language free bound rule spec completed)
      (objects : AssignmentObjects completed)
      (tail : QueriesSatisfied relEnv language free bound rule spec (index + 1)
        rest completed final history) :
      QueriesSatisfied relEnv language free bound rule spec index
        (.relationQuery relation arguments :: rest) initial final
        (.root index resultIndex :: history)

theorem runQueries_sound (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (index : Nat) (premises : List Premise)
    (initial final : Assignment) (history : List (PremiseEvent Empty))
    (member : (final, history) ∈ runQueries relEnv language free bound rule spec
      index premises initial) :
    QueriesSatisfied relEnv language free bound rule spec index premises initial final history := by
  induction premises generalizing index initial final history with
  | nil =>
      simp only [runQueries, List.mem_singleton, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact .nil index final
  | cons premise rest ih =>
      cases premise with
      | freshness _ => simp [runQueries] at member
      | congruence _ _ => simp [runQueries] at member
      | scopedStep _ => simp [runQueries] at member
      | forAll _ _ _ => simp [runQueries] at member
      | relationQuery relation arguments =>
        simp only [runQueries, List.mem_flatMap, List.mem_map] at member
        obtain ⟨⟨event, completed⟩, selected, ⟨next, tail⟩, tailMember, represented⟩ := member
        cases represented
        obtain ⟨_, queryMember, typed⟩ :=
          (mem_typedQueryResults_iff relEnv language free bound rule spec index
            relation arguments initial completed event).mp selected
        obtain ⟨resultIndex, eventEq, indexed⟩ :=
          queryResults_indexed_sound relEnv language spec bound.length index
            relation arguments initial completed event queryMember
        subst event
        exact .cons index resultIndex relation arguments rest initial completed next tail
          indexed
          (checkAssignment_sound typed)
          (checkAssignment_objects typed)
          (ih (index := index + 1) (initial := completed)
            (final := next) (history := tail) tailMember)

/-- Typed finite-query execution is a witness-preserving restriction of the
existing focused interpreter. Recursive step queries are outside this profile. -/
theorem runQueries_forget (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (index : Nat) (premises : List Premise)
    (initial final : Assignment) (history : List (PremiseEvent Empty))
    (member : (final, history) ∈ runQueries relEnv language free bound rule spec
      index premises initial) :
    (final, history) ∈ FocusedRelationQueryExecution.runPremises
      (fun _ _ => ([] : List (Empty × Pattern))) relEnv language rule spec
      bound.length index premises initial := by
  induction premises generalizing index initial final history with
  | nil => simpa [runQueries, FocusedRelationQueryExecution.runPremises] using member
  | cons premise rest ih =>
      cases premise with
      | freshness _ => simp [runQueries] at member
      | congruence _ _ => simp [runQueries] at member
      | scopedStep _ => simp [runQueries] at member
      | forAll _ _ _ => simp [runQueries] at member
      | relationQuery relation arguments =>
          simp only [runQueries, List.mem_flatMap, List.mem_map] at member
          obtain ⟨⟨event, completed⟩, selected, ⟨next, tail⟩, tailMember, represented⟩ := member
          cases represented
          have queryMember :=
            ((mem_typedQueryResults_iff relEnv language free bound rule spec index
              relation arguments initial completed event).mp selected).2.1
          have restMember := ih (index := index + 1) (initial := completed)
            (final := next) (history := tail) tailMember
          simp only [FocusedRelationQueryExecution.runPremises,
            FocusedRelationQueryExecution.premiseResults, List.mem_flatMap, List.mem_map]
          exact ⟨(event, completed), queryMember, (next, tail), restMember, rfl⟩

theorem QueriesSatisfied.history_length {relEnv : RelationEnv} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {rule : RewriteRule}
    {spec : RuleBindingSpec} {index : Nat} {premises : List Premise}
    {initial final : Assignment} {history : List (PremiseEvent Empty)}
    (satisfied : QueriesSatisfied relEnv language free bound rule spec index
      premises initial final history) : history.length = premises.length := by
  induction satisfied with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ _ _ _ ih => simpa using congrArg Nat.succ ih

/-- Semantic query derivations have executable realizations on the checked
finite-query profile with exactly the same authored/result ordinals. -/
theorem runQueries_complete {relEnv : RelationEnv} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {rule : RewriteRule}
    {spec : RuleBindingSpec} {index : Nat} {premises : List Premise}
    {initial final : Assignment} {history : List (PremiseEvent Empty)}
    (supported : queriesSupported spec index premises = true)
    (satisfied : QueriesSatisfied relEnv language free bound rule spec index
      premises initial final history) :
    (final, history) ∈ runQueries relEnv language free bound
      rule spec index premises initial := by
  induction satisfied with
  | nil index assignment => simp [runQueries]
  | cons index resultIndex relation arguments rest initial completed final history
      query typed objects tail ih =>
      simp only [queriesSupported, querySupported, Bool.and_eq_true] at supported
      have notOccurrence : ScopedPremiseExecution.hasOccurrenceAt spec index = false :=
        by simpa only [Bool.not_eq_true'] using supported.1.1
      have queryMember := queryResults_indexed_complete relEnv language spec
        bound.length index resultIndex relation arguments initial completed notOccurrence query
      have typedMember : (PremiseEvent.root index resultIndex, completed) ∈
          typedQueryResults relEnv language free bound rule spec index relation arguments initial := by
        apply (mem_typedQueryResults_iff relEnv language free bound rule spec index
          relation arguments initial completed (.root index resultIndex)).mpr
        exact ⟨supported.1.2, queryMember, checkAssignment_complete typed objects⟩
      have tailMember := ih supported.2
      simp only [runQueries, List.mem_flatMap, List.mem_map]
      exact ⟨(.root index resultIndex, completed), typedMember,
        (final, history), tailMember, rfl⟩

theorem QueriesSatisfied.final_typed {relEnv : RelationEnv} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {rule : RewriteRule}
    {spec : RuleBindingSpec} {index : Nat} {premises : List Premise}
    {initial final : Assignment} {history : List (PremiseEvent Empty)}
    (before : AssignmentTyped language free bound rule spec initial)
    (satisfied : QueriesSatisfied relEnv language free bound rule spec index
      premises initial final history) :
    AssignmentTyped language free bound rule spec final := by
  induction satisfied with
  | nil => exact before
  | cons _ _ _ _ _ _ _ _ _ _ typed _ _ ih => exact ih typed

/-- Incompleteness is distinct from a supported query with no matching row. -/
inductive Pending where
  | missingBinding
  | bindingRejected
  | sourceRejected
  | capturedAssignmentRejected (matchIndex : Nat)
  | unsupportedPremise (index : Nat) (premise : Premise)
  | explicitPremiseOccurrence (index : Nat)
  | unsupportedQueryArguments (index : Nat) (arguments : List Pattern)
  | unavailableProjection (index : Nat) (assignment : Assignment)
deriving Repr, DecidableEq

/-- Unsupported authored forms are retained even if the current source has
no capture. Semantic completeness still requires the admitted matcher profile. -/
def declarationPending (rule : RewriteRule) (spec : RuleBindingSpec) : List Pending :=
  rule.premises.zipIdx.filterMap fun (premise, index) =>
    match premise with
    | .relationQuery _ arguments =>
        if ScopedPremiseExecution.hasOccurrenceAt spec index then
          some (.explicitPremiseOccurrence index)
        else if arguments.all queryArgumentSupported then none
        else some (.unsupportedQueryArguments index arguments)
    | _ => some (.unsupportedPremise index premise)

def queryPending (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) : Nat → List Premise → Assignment → List Pending
  | _, [], _ => []
  | index, .relationQuery relation arguments :: rest, assignment =>
      if ScopedPremiseExecution.hasOccurrenceAt spec index then
        [.explicitPremiseOccurrence index]
      else if !arguments.all queryArgumentSupported then
        [.unsupportedQueryArguments index arguments]
      else
        match FocusedRelationQueryExecution.projectNames? bound.length assignment
          (arguments.flatMap Pattern.freeFvarNames).eraseDups with
        | none => [.unavailableProjection index assignment]
        | some _ =>
            (typedQueryResults relEnv language free bound rule spec index relation
              arguments assignment).flatMap fun (_, completed) =>
                queryPending relEnv language free bound rule spec (index + 1) rest completed
  | index, premise :: _, _ => [.unsupportedPremise index premise]

/-- A rule occurrence retains matching origin and all successful premise
positions, even when another occurrence reaches the same endpoint. -/
structure Receipt where
  matchIndex : Nat
  captured : Assignment
  completed : Assignment
  history : List (PremiseEvent Empty)
  target : Pattern
deriving Repr, DecidableEq

/-- The existing native execution receipt reads the same assignments and
ordered premise positions. Matching origin remains in the enclosing receipt. -/
def Receipt.asFiring (receipt : Receipt) : ScopedPremiseExecution.RuleFiring Empty :=
  { captured := receipt.captured, completed := receipt.completed,
    history := receipt.history, target := receipt.target }

structure Outcome where
  receipts : List Receipt
  pending : List Pending
deriving Repr, DecidableEq

def finishTyped? (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (matchIndex : Nat) (captured completed : Assignment)
    (history : List (PremiseEvent Empty)) : Option Receipt := do
  let target ← reduct? rule spec bound.length completed
  if checkOpenPatternWellSorted language free bound expected target then
    some { matchIndex, captured, completed, history, target }
  else none

theorem finishTyped?_readout (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (matchIndex : Nat) (captured completed : Assignment)
    (history : List (PremiseEvent Empty)) (receipt : Receipt)
    (finished : finishTyped? language free bound expected rule spec matchIndex
      captured completed history = some receipt) :
    receipt.matchIndex = matchIndex ∧ receipt.captured = captured ∧
      receipt.completed = completed ∧ receipt.history = history ∧
      reduct? rule spec bound.length completed = some receipt.target ∧
      OpenPatternWellSorted language free bound expected receipt.target := by
  unfold finishTyped? at finished
  cases readout : reduct? rule spec bound.length completed with
  | none => simp [readout] at finished
  | some target =>
      by_cases checked : checkOpenPatternWellSorted language free bound expected target = true
      · simp [readout, checked] at finished
        cases finished
        exact ⟨rfl, rfl, rfl, rfl, rfl,
          Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound checked⟩
      · simp [readout, checked] at finished

theorem finishTyped?_complete (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (receipt : Receipt)
    (readout : reduct? rule spec bound.length receipt.completed = some receipt.target)
    (sorted : OpenPatternWellSorted language free bound expected receipt.target) :
    finishTyped? language free bound expected rule spec receipt.matchIndex
      receipt.captured receipt.completed receipt.history = some receipt := by
  have checked := Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_complete sorted
  cases receipt
  dsimp only at readout checked ⊢
  simp [finishTyped?, readout, checked]

def receiptsFor (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (rule : RewriteRule) (spec : RuleBindingSpec) (source : Pattern) : List Receipt :=
  (matchRuleAt rule spec bound.length source).zipIdx.flatMap fun (captured, matchIndex) =>
    if checkAssignment language free bound rule spec captured then
      (runQueries relEnv language free bound rule spec 0 rule.premises captured).filterMap fun
        (completed, history) =>
          finishTyped? language free bound expected rule spec matchIndex captured completed history
    else []

def applyRuleAtOutcome (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (rule : RewriteRule) (source : Pattern) : Outcome :=
  if checkOpenPatternWellSorted language free bound expected source then
    match rule.bindings with
    | none => ⟨[], [.missingBinding]⟩
    | some spec =>
        if admittedFor rule spec then
          { receipts := receiptsFor relEnv language free bound expected rule spec source
            pending := declarationPending rule spec ++
              (matchRuleAt rule spec bound.length source).zipIdx.flatMap fun
              (captured, matchIndex) =>
                if checkAssignment language free bound rule spec captured then
                  queryPending relEnv language free bound rule spec 0 rule.premises captured
                else [.capturedAssignmentRejected matchIndex] }
        else ⟨[], [.bindingRejected]⟩
  else ⟨[], [.sourceRejected]⟩

/-- Independent typed root instances. Matching and query ordinals select
the fixed lists at their actual positions; dependent evidence retains the
complete assignments and the authored reduct. -/
inductive RuleInstance (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (rule : RewriteRule) (source : Pattern) (receipt : Receipt) : Prop where
  | fire (spec : RuleBindingSpec)
      (declared : rule.bindings = some spec)
      (admitted : admittedFor rule spec = true)
      (sourceSorted : OpenPatternWellSorted language free bound expected source)
      (position : (matchRuleAt rule spec bound.length source)[receipt.matchIndex]? =
        some receipt.captured)
      (capturedTyped : AssignmentTyped language free bound rule spec receipt.captured)
      (capturedObjects : AssignmentObjects receipt.captured)
      (premises : QueriesSatisfied relEnv language free bound rule spec 0
        rule.premises receipt.captured receipt.completed receipt.history)
      (readout : reduct? rule spec bound.length receipt.completed = some receipt.target)
      (targetSorted : OpenPatternWellSorted language free bound expected receipt.target) :
      RuleInstance relEnv language free bound expected rule source receipt

theorem applyRuleAtOutcome_sound (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (rule : RewriteRule) (source : Pattern) (receipt : Receipt)
    (member : receipt ∈ (applyRuleAtOutcome relEnv language free bound expected rule source).receipts) :
    RuleInstance relEnv language free bound expected rule source receipt := by
  unfold applyRuleAtOutcome at member
  split at member
  · rename_i checked
    cases declared : rule.bindings with
    | none => simp [declared] at member
    | some spec =>
        simp only [declared] at member
        split at member
        · rename_i admitted
          simp only [receiptsFor, List.mem_flatMap] at member
          obtain ⟨⟨captured, matchIndex⟩, selected, afterMatching⟩ := member
          split at afterMatching
          · rename_i capturedChecked
            simp only [List.mem_filterMap] at afterMatching
            obtain ⟨⟨completed, history⟩, queryMember, finished⟩ := afterMatching
            obtain ⟨origin, capture, complete, historyEq, readout, sorted⟩ :=
              finishTyped?_readout language free bound expected rule spec matchIndex
                captured completed history receipt finished
            have matcherPosition := List.mem_zipIdx_iff_getElem?.mp selected
            rw [← origin, ← capture] at matcherPosition
            have premises := runQueries_sound relEnv language free bound rule spec
              0 rule.premises captured completed history queryMember
            rw [← capture, ← complete, ← historyEq] at premises
            exact .fire spec declared admitted
              (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound checked)
              matcherPosition (capture ▸ checkAssignment_sound capturedChecked)
              (capture ▸ checkAssignment_objects capturedChecked) premises
              (complete ▸ readout) sorted
          · simp at afterMatching
        · simp at member
  · simp at member

/-- Completeness is earned for supported finite query profiles and the
same independent sorted carrier used by soundness. -/
theorem applyRuleAtOutcome_complete (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (rule : RewriteRule) (source : Pattern) (receipt : Receipt)
    (supported : ∀ spec, rule.bindings = some spec → queriesSupported spec 0 rule.premises = true)
    (hinstance : RuleInstance relEnv language free bound expected rule source receipt) :
    receipt ∈ (applyRuleAtOutcome relEnv language free bound expected rule source).receipts := by
  cases hinstance with
  | fire spec declared admitted sourceSorted position capturedTyped capturedObjects premises readout targetSorted =>
      have sourceChecked := Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_complete sourceSorted
      have capturedChecked := checkAssignment_complete capturedTyped capturedObjects
      have selected : (receipt.captured, receipt.matchIndex) ∈
          (matchRuleAt rule spec bound.length source).zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr position
      have queryMember := runQueries_complete (supported spec declared) premises
      have finished := finishTyped?_complete language free bound expected rule spec receipt readout targetSorted
      simp only [applyRuleAtOutcome, sourceChecked, if_true, declared, admitted, receiptsFor,
        List.mem_flatMap]
      refine ⟨(receipt.captured, receipt.matchIndex), selected, ?_⟩
      simp only [capturedChecked, if_true, List.mem_filterMap]
      exact ⟨(receipt.completed, receipt.history), queryMember, finished⟩

theorem applyRuleAtOutcome_iff (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (rule : RewriteRule) (source : Pattern) (receipt : Receipt)
    (supported : ∀ spec, rule.bindings = some spec → queriesSupported spec 0 rule.premises = true) :
    receipt ∈ (applyRuleAtOutcome relEnv language free bound expected rule source).receipts ↔
      RuleInstance relEnv language free bound expected rule source receipt :=
  ⟨applyRuleAtOutcome_sound relEnv language free bound expected rule source receipt,
    applyRuleAtOutcome_complete relEnv language free bound expected rule source receipt supported⟩

theorem applyRuleAtOutcome_native_readout (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (rule : RewriteRule) (source : Pattern) (receipt : Receipt)
    (supported : ∀ spec, rule.bindings = some spec → queriesSupported spec 0 rule.premises = true)
    (member : receipt ∈ (applyRuleAtOutcome relEnv language free bound expected rule source).receipts) :
    receipt.asFiring ∈ FocusedRelationQueryExecution.applyRuleWithOracle
      (fun _ _ => ([] : List (Empty × Pattern))) relEnv language bound.length rule source := by
  have hinstance := applyRuleAtOutcome_sound relEnv language free bound expected rule source receipt member
  cases hinstance with
  | fire spec declared admitted _ position _ _ premises readout targetSorted =>
      have queries := runQueries_complete (supported spec declared) premises
      have oldQueries := runQueries_forget relEnv language free bound rule spec 0
        rule.premises receipt.captured receipt.completed receipt.history queries
      have scopeChecked : receipt.target.isWellScopedAt bound.length = true := targetSorted.2.2.2
      apply (FocusedRelationQueryExecution.mem_applyRuleWithOracle_iff
        (fun _ _ => ([] : List (Empty × Pattern))) relEnv language bound.length rule source
        receipt.asFiring).mpr
      refine ⟨spec, receipt.captured, receipt.completed, receipt.history, declared,
        admitted, List.mem_of_getElem? position, oldQueries, ?_⟩
      simp [ScopedPremiseExecution.finish?, readout, scopeChecked, Receipt.asFiring]

/-- Typed oriented equation receipts do not assert directed reduction. -/
structure EquationReceipt extends Receipt where
  equationIndex : Nat
  orientation : Orientation
deriving Repr, DecidableEq

structure EquationOutcome where
  receipts : List EquationReceipt
  pending : List Pending
deriving Repr, DecidableEq

def applyAt (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (equationIndex : Nat) (equation : Equation) (orientation : Orientation)
    (source : Pattern) : EquationOutcome :=
  let outcome := applyRuleAtOutcome relEnv language free bound expected
    (orientedRule equation orientation) source
  { receipts := outcome.receipts.map fun receipt =>
      { toReceipt := receipt, equationIndex, orientation }
    pending := outcome.pending }

def EquationInstance (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (equationIndex : Nat) (equation : Equation) (orientation : Orientation)
    (source : Pattern) (receipt : EquationReceipt) : Prop :=
  receipt.equationIndex = equationIndex ∧ receipt.orientation = orientation ∧
    RuleInstance relEnv language free bound expected (orientedRule equation orientation)
      source receipt.toReceipt

theorem applyAt_sound (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (equationIndex : Nat) (equation : Equation) (orientation : Orientation)
    (source : Pattern) (receipt : EquationReceipt)
    (member : receipt ∈ (applyAt relEnv language free bound expected equationIndex
      equation orientation source).receipts) :
    EquationInstance relEnv language free bound expected equationIndex equation orientation source receipt := by
  simp only [applyAt, List.mem_map] at member
  obtain ⟨root, rootMember, represented⟩ := member
  cases represented
  exact ⟨rfl, rfl, applyRuleAtOutcome_sound relEnv language free bound expected
    (orientedRule equation orientation) source root rootMember⟩

theorem applyAt_complete (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (equationIndex : Nat) (equation : Equation) (orientation : Orientation)
    (source : Pattern) (receipt : EquationReceipt)
    (supported : ∀ spec, (orientedRule equation orientation).bindings = some spec →
      queriesSupported spec 0 equation.premises = true)
    (hinstance : EquationInstance relEnv language free bound expected equationIndex
      equation orientation source receipt) :
    receipt ∈ (applyAt relEnv language free bound expected equationIndex
      equation orientation source).receipts := by
  obtain ⟨origin, direction, hinstance⟩ := hinstance
  have member := applyRuleAtOutcome_complete relEnv language free bound expected
    (orientedRule equation orientation) source receipt.toReceipt
    (by simpa using supported) hinstance
  cases receipt
  subst_vars
  exact List.mem_map.mpr ⟨_, member, rfl⟩

/-- Pending equation work retains declaration and orientation alongside its
reason; a later driver can resume the exact obligation. -/
structure EquationPending where
  equationIndex : Nat
  orientation : Orientation
  reason : Pending
deriving Repr, DecidableEq

structure EquationsOutcome where
  receipts : List EquationReceipt
  pending : List EquationPending
deriving Repr, DecidableEq

def equationsAtOutcome (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) : EquationsOutcome :=
  { receipts := language.equations.zipIdx.flatMap fun (equation, equationIndex) =>
      [Orientation.forward, Orientation.reverse].flatMap fun orientation =>
        (applyAt relEnv language free bound expected equationIndex equation orientation source).receipts
    pending := language.equations.zipIdx.flatMap fun (equation, equationIndex) =>
      [Orientation.forward, Orientation.reverse].flatMap fun orientation =>
        (applyAt relEnv language free bound expected equationIndex equation orientation source).pending.map fun reason =>
          { equationIndex, orientation, reason } }

theorem equationsAtOutcome_sound (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (receipt : EquationReceipt)
    (member : receipt ∈ (equationsAtOutcome relEnv language free bound expected source).receipts) :
    ∃ equation equationIndex,
      (equation, equationIndex) ∈ language.equations.zipIdx ∧
      EquationInstance relEnv language free bound expected equationIndex
        equation receipt.orientation source receipt := by
  simp only [equationsAtOutcome, List.mem_flatMap] at member
  obtain ⟨⟨equation, equationIndex⟩, declared, orientation, _, firing⟩ := member
  obtain ⟨origin, direction, hinstance⟩ := applyAt_sound relEnv language free bound
    expected equationIndex equation orientation source receipt firing
  exact ⟨equation, equationIndex, declared, origin, rfl, direction ▸ hinstance⟩

theorem equationsAtOutcome_complete (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (receipt : EquationReceipt) (equation : Equation)
    (equationIndex : Nat)
    (declared : (equation, equationIndex) ∈ language.equations.zipIdx)
    (supported : ∀ spec, (orientedRule equation receipt.orientation).bindings = some spec →
      queriesSupported spec 0 equation.premises = true)
    (hinstance : EquationInstance relEnv language free bound expected equationIndex
      equation receipt.orientation source receipt) :
    receipt ∈ (equationsAtOutcome relEnv language free bound expected source).receipts := by
  have firing := applyAt_complete relEnv language free bound expected equationIndex
    equation receipt.orientation source receipt supported hinstance
  have orientationMember : receipt.orientation ∈ [Orientation.forward, Orientation.reverse] := by
    cases receipt.orientation <;> simp
  simp only [equationsAtOutcome, List.mem_flatMap]
  exact ⟨(equation, equationIndex), declared, receipt.orientation, orientationMember, firing⟩

structure LocatedReceipt extends Receipt where
  ruleIndex : Nat
deriving Repr, DecidableEq

structure RulePending where
  ruleIndex : Nat
  reason : Pending
deriving Repr, DecidableEq

structure RulesOutcome where
  receipts : List LocatedReceipt
  pending : List RulePending
deriving Repr, DecidableEq

def rulesAtOutcome (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) : RulesOutcome :=
  { receipts := language.rewrites.zipIdx.flatMap fun (rule, ruleIndex) =>
      (applyRuleAtOutcome relEnv language free bound expected rule source).receipts.map fun receipt =>
        { toReceipt := receipt, ruleIndex }
    pending := language.rewrites.zipIdx.flatMap fun (rule, ruleIndex) =>
      (applyRuleAtOutcome relEnv language free bound expected rule source).pending.map fun reason =>
        { ruleIndex, reason } }

theorem rulesAtOutcome_sound (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (receipt : LocatedReceipt)
    (member : receipt ∈ (rulesAtOutcome relEnv language free bound expected source).receipts) :
    ∃ rule ruleIndex,
      (rule, ruleIndex) ∈ language.rewrites.zipIdx ∧ receipt.ruleIndex = ruleIndex ∧
      RuleInstance relEnv language free bound expected rule source receipt.toReceipt := by
  simp only [rulesAtOutcome, List.mem_flatMap, List.mem_map] at member
  obtain ⟨⟨rule, ruleIndex⟩, declared, original, firing, represented⟩ := member
  cases represented
  exact ⟨rule, ruleIndex, declared, rfl,
    applyRuleAtOutcome_sound relEnv language free bound expected rule source original firing⟩

theorem rulesAtOutcome_complete (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (receipt : LocatedReceipt) (rule : RewriteRule)
    (ruleIndex : Nat) (declared : (rule, ruleIndex) ∈ language.rewrites.zipIdx)
    (origin : receipt.ruleIndex = ruleIndex)
    (supported : ∀ spec, rule.bindings = some spec → queriesSupported spec 0 rule.premises = true)
    (hinstance : RuleInstance relEnv language free bound expected rule source receipt.toReceipt) :
    receipt ∈ (rulesAtOutcome relEnv language free bound expected source).receipts := by
  have firing := applyRuleAtOutcome_complete relEnv language free bound expected rule source
    receipt.toReceipt supported hinstance
  simp only [rulesAtOutcome, List.mem_flatMap, List.mem_map]
  refine ⟨(rule, ruleIndex), declared, receipt.toReceipt, firing, ?_⟩
  cases receipt
  simp_all

theorem queryPending_forAll (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (index : Nat) (collection parameter : String)
    (body : Premise) (rest : List Premise) (assignment : Assignment) :
    queryPending relEnv language free bound rule spec index
      (.forAll collection parameter body :: rest) assignment =
        [.unsupportedPremise index (.forAll collection parameter body)] := rfl

theorem queryPending_unavailable (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (index : Nat) (relation : String)
    (arguments : List Pattern) (rest : List Premise) (assignment : Assignment)
    (supported : ScopedPremiseExecution.hasOccurrenceAt spec index = false)
    (argumentsSupported : arguments.all queryArgumentSupported = true)
    (unavailable : FocusedRelationQueryExecution.projectNames? bound.length assignment
      (arguments.flatMap Pattern.freeFvarNames).eraseDups = none) :
    queryPending relEnv language free bound rule spec index
      (.relationQuery relation arguments :: rest) assignment =
        [.unavailableProjection index assignment] := by
  simp only [queryPending, supported, argumentsSupported, Bool.not_true, Bool.false_eq_true,
    if_false, unavailable]

theorem applyRuleAtOutcome_source_rejected (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (rule : RewriteRule) (source : Pattern)
    (rejected : checkOpenPatternWellSorted language free bound expected source = false) :
    applyRuleAtOutcome relEnv language free bound expected rule source =
      ⟨[], [.sourceRejected]⟩ := by
  simp only [applyRuleAtOutcome, rejected, Bool.false_eq_true, if_false]

end Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding
open ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

def assignmentFreeNames (assignment : Assignment) : List String :=
  assignment.flatMap fun entry => entry.2.body.freeFvarNames

/-- Changing the free context away from stored bodies does not change the
assignment check. The rule and dependency contexts are kept literally. -/
theorem checkAssignment_congrFree (language : LanguageDef)
    (first second : FreeTypeContext) (bound : List TypeExpr)
    (rule : RewriteRule) (spec : RuleBindingSpec) (assignment : Assignment)
    (same : ∀ name value, (name, value) ∈ assignment →
      ∀ freeName ∈ value.body.freeFvarNames, first freeName = second freeName) :
    checkAssignment language first bound rule spec assignment =
      checkAssignment language second bound rule spec assignment := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro checked
    apply checkAssignment_complete
    · intro name value member
      obtain ⟨dependencies, expected, declared, sorted, metadata, ambient, typed⟩ :=
        checkAssignment_sound checked name value member
      refine ⟨dependencies, expected, declared, sorted, metadata, ambient, ?_⟩
      exact typed.recontextualizeFree fun variableMember lookup => by
        rw [← same name value member _ variableMember]
        exact lookup
    · exact checkAssignment_objects checked
  · intro checked
    apply checkAssignment_complete
    · intro name value member
      obtain ⟨dependencies, expected, declared, sorted, metadata, ambient, typed⟩ :=
        checkAssignment_sound checked name value member
      refine ⟨dependencies, expected, declared, sorted, metadata, ambient, ?_⟩
      exact typed.recontextualizeFree fun variableMember lookup => by
        rw [same name value member _ variableMember]
        exact lookup
    · exact checkAssignment_objects checked

/-- Arbitrary mathematical free contexts have an earned finite representation
for this particular complete assignment. Unused captures are included. -/
theorem checkAssignment_finiteFree (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr)
    (rule : RewriteRule) (spec : RuleBindingSpec) (assignment : Assignment) :
    checkAssignment language
      (FreeTypeContext.ofList (free.entriesOn (assignmentFreeNames assignment)))
      bound rule spec assignment =
      checkAssignment language free bound rule spec assignment := by
  apply checkAssignment_congrFree
  intro name value member freeName variableMember
  rw [FreeTypeContext.ofList_entriesOn]
  apply if_pos
  exact List.mem_flatMap.mpr ⟨(name, value), member, variableMember⟩


theorem checkAssignment_snapshot (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec)
    (assignment : Assignment) (footprint : List String)
    (covers : ∀ name ∈ assignmentFreeNames assignment, name ∈ footprint) :
    checkAssignment language (FreeTypeContext.ofList (free.entriesOn footprint))
      bound rule spec assignment = checkAssignment language free bound rule spec assignment := by
  apply checkAssignment_congrFree
  intro captureName value member name occurs
  rw [FreeTypeContext.ofList_entriesOn, if_pos]
  exact covers name (List.mem_flatMap.mpr ⟨(captureName, value), member, occurs⟩)
theorem assignment_free_names_covered (footprint : List String) (assignment : Assignment)
    (stored : assignmentFreeWithin footprint assignment) :
    ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames assignment, name ∈ footprint := by
  intro name occurs
  rcases List.mem_flatMap.mp occurs with ⟨entry, member, occurs⟩
  exact stored entry member name occurs

theorem assignment_covered_by_own_names (assignment : Assignment) :
    assignmentFreeWithin (ConditionalEquationExecution.assignmentFreeNames assignment) assignment := by
  intro entry member name occurs
  exact List.mem_flatMap.mpr ⟨entry, member, occurs⟩

theorem assignment_coverage_mono (first second : List String) (assignment : Assignment)
    (subset : ∀ name ∈ first, name ∈ second) (stored : assignmentFreeWithin first assignment) :
    assignmentFreeWithin second assignment := by
  intro entry member name occurs
  exact subset name (stored entry member name occurs)

#print axioms Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignmentFreeNames
#print axioms Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.checkAssignment_congrFree
#print axioms Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.checkAssignment_finiteFree
#print axioms Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.checkAssignment_snapshot
#print axioms Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_free_names_covered
#print axioms Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_covered_by_own_names
#print axioms Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_coverage_mono

end Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution
