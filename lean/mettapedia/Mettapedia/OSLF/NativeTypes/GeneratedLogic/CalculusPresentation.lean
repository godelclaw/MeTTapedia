import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Reference
import Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
import Mettapedia.GSLT.LanguageDef.CertificateGSLTStepAdequacyGeneral
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Proof calculi as goal-stack rewriting

Backward proof search in a calculus replaces the first outstanding judgment of a goal list by the
premises of a rule instance whose conclusion it is (`CalculusAsLanguage.Resolves`). When matching the
conclusion against the goal determines the whole instance, this is rewriting: the rule
`premises / conclusion` is the rewrite `[conclusion, ...rest] ⇒ [premises, ...rest]` on goal stacks,
vectors of judgments. Every formula of the generated logic then speaks about proof search, and the
front door decides it.

- **A moded rule** (`moded`): no side condition, formals at depth zero, conclusion and premises hole
  skeletons (constructors and metavariables, binders only around closed bodies), every formal occurring
  in the conclusion, and every metavariable of a premise occurring in the conclusion.
- **The presentation** (`presentation`): one rewrite per moded rule, and nothing else.
- **Exactness** on proper goal lists (ground, canonical binder metadata, object terms): a step of the
  presentation from a goal stack is a resolution step by a moded rule (`step_sound`), and every
  resolution step by a moded rule is a step of the presentation (`step_complete`). Proper goal lists
  stay proper (`step_sound`).
- **Derivability**: in any calculus, a stack that reaches the empty stack is derivable
  (`derivable_of_sat`). When only moded rules conclude the judgments in play (`modedHeads`), a proper goal
  list is derivable exactly when its stack reaches the empty stack (`derivable_iff_reaches`), which is the
  formula "some run reaches the empty stack" (`sat_reachesEmpty_iff`, `derivable_iff_sat`).

A rule with a premise metavariable that is not in its conclusion has infinitely many instances at a goal
(the middle term of transitivity, for example), so it is not a rewrite, and the presentation leaves it
out.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CalculusPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel matchPattern_iff_matchRel matchRel_vectorRest_iff_split)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage (GoalState Resolves proofSearchGSLT)
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
  (patternHoleSkeleton patternsHoleSkeleton patternClosedSkeleton patternsClosedSkeleton patternOccurrenceNames
    patternsOccurrenceNames bindingsValuesWellFormed zipBindings bindingsArguments matchPattern_holeSkeleton_sound
    matchPattern_own_instance instantiateSchemaAt?_eq_applyBindings instantiateSchemasAt?_eq_applyBindings
    argumentsValidAt_bindingsArguments zipBindings_bindingsArguments_lookup applyBindings_agree applyBindingsList_agree
    applyBindingsList_wellFormed depthAligned_of_holeSkeleton captureDepth_of_holeSkeleton applyBindings_closedSkeleton
    applyBindings_fvar zipBindings_covers bindingsAgreeWith bindingsAgreeWith_lookup mem_patternsOccurrenceNames
    argumentsValidAt_zip_values)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)

/-! ## The presentation -/

/-- The metavariable that carries the rest of a goal stack. -/
def restName : String := "goals:rest"

/-- The formal names of a rule. -/
def formalNames (rule : RuleSchema) : List String := rule.metavariables.map Prod.fst

/-- **A moded rule**: matching its conclusion determines its whole instance, and its premises are built
from that instance alone. -/
def moded (rule : RuleSchema) : Bool :=
  rule.sideConditions.isEmpty && rule.metavariables.all (fun formal => formal.2 == 0) &&
    !(formalNames rule).contains restName &&
    patternHoleSkeleton rule.conclusion && patternsHoleSkeleton rule.premises &&
    rule.conclusion.isWellScopedAt 0 && Pattern.isWellScopedListAt 0 rule.premises &&
    rule.conclusion.hasCanonicalBinderMetadata && Pattern.hasCanonicalBinderMetadataList rule.premises &&
    (patternOccurrenceNames rule.conclusion).all (formalNames rule).contains &&
    (formalNames rule).all (patternOccurrenceNames rule.conclusion).contains &&
    (patternsOccurrenceNames rule.premises).all (patternOccurrenceNames rule.conclusion).contains

/-- A goal stack: the outstanding judgments, first one first. -/
def stack (goals : List Pattern) : Pattern := .collection .vec goals none

/-- `[conclusion, ...rest] ⇒ [premises, ...rest]`. -/
def presentationRule (rule : RuleSchema) : RewriteRule :=
  { name := rule.id.value, typeContext := [], premises := [],
    left := .collection .vec [rule.conclusion] (some restName),
    right := .collection .vec rule.premises (some restName) }

/-- **The goal-stack presentation** of a calculus: one rewrite per moded rule. -/
def presentation (definition : CalculusLanguageDef) : LanguageDef :=
  { name := "goal-stacks", types := [], terms := [], equations := [],
    rewrites := (definition.rules.filter moded).map presentationRule }

/-- One resolution step by a moded rule. -/
def ModedResolves (definition : ValidatedCalculusLanguageDef) (source target : GoalState) : Prop :=
  ∃ rule ∈ definition.1.rules, moded rule = true ∧ ∃ arguments premises conclusion rest,
    instantiateRule? definition ⟨rule.id, arguments⟩ = some (premises, conclusion) ∧
      source = conclusion :: rest ∧ target = premises ++ rest

theorem ModedResolves.resolves {definition : ValidatedCalculusLanguageDef} {source target : GoalState}
    (step : ModedResolves definition source target) : Resolves definition source target := by
  obtain ⟨rule, _, _, arguments, premises, conclusion, rest, instantiated, rfl, rfl⟩ := step
  exact ⟨⟨rule.id, arguments⟩, premises, conclusion, rest, instantiated, rfl, rfl⟩

/-- **A proper goal**: ground, with canonical binder metadata, an object term. -/
def ProperGoal (goal : Pattern) : Prop :=
  goal.isGroundAt 0 = true ∧ goal.hasCanonicalBinderMetadata = true ∧ isObjectPattern goal = true

/-! ## What a moded rule provides -/

section Moded

variable {rule : RuleSchema} (isModed : moded rule = true)
include isModed

private theorem parts : rule.sideConditions = [] ∧ (∀ formal ∈ rule.metavariables, formal.2 = 0) ∧
    restName ∉ formalNames rule ∧ patternHoleSkeleton rule.conclusion = true ∧
    patternsHoleSkeleton rule.premises = true ∧ rule.conclusion.isWellScopedAt 0 = true ∧
    Pattern.isWellScopedListAt 0 rule.premises = true ∧ rule.conclusion.hasCanonicalBinderMetadata = true ∧
    Pattern.hasCanonicalBinderMetadataList rule.premises = true ∧
    (∀ name ∈ patternOccurrenceNames rule.conclusion, name ∈ formalNames rule) ∧
    (∀ name ∈ formalNames rule, name ∈ patternOccurrenceNames rule.conclusion) ∧
    (∀ name ∈ patternsOccurrenceNames rule.premises, name ∈ patternOccurrenceNames rule.conclusion) := by
  simp only [moded, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.elem_eq_mem, decide_eq_true_eq, decide_eq_false_iff_not] at isModed
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sides, depths⟩, fresh⟩, conclusionHole⟩, premisesHole⟩, conclusionScoped⟩, premisesScoped⟩,
    conclusionCanonical⟩, premisesCanonical⟩, conclusionNames⟩, formalsOccur⟩, premiseNames⟩ := isModed
  exact ⟨sides, depths, fresh, conclusionHole, premisesHole, conclusionScoped, premisesScoped, conclusionCanonical,
    premisesCanonical, conclusionNames, formalsOccur, premiseNames⟩

theorem rest_not_in_conclusion : restName ∉ patternOccurrenceNames rule.conclusion := fun inside =>
  (parts isModed).2.2.1 ((parts isModed).2.2.2.2.2.2.2.2.2.1 _ inside)

theorem rest_not_in_premises : restName ∉ patternsOccurrenceNames rule.premises := fun inside =>
  rest_not_in_conclusion isModed ((parts isModed).2.2.2.2.2.2.2.2.2.2.2 _ inside)

end Moded

/-! ## Object terms through binding application -/

theorem objectList_iff (patterns : List Pattern) :
    isObjectPatternList patterns = true ↔ ∀ pattern ∈ patterns, isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp [isObjectPatternList]
  | cons head tail ih => simp [isObjectPatternList, ih]

/-- A closed skeleton is an object term. -/
theorem closedSkeleton_object : ∀ {pattern : Pattern}, patternClosedSkeleton pattern = true →
    isObjectPattern pattern = true
  | .bvar _, _ => rfl
  | .fvar _, closed => by simp [patternClosedSkeleton] at closed
  | .apply _ arguments, closed => by
    simp only [isObjectPattern]
    refine (objectList_iff arguments).mpr fun argument member => ?_
    have : sizeOf argument < sizeOf (Pattern.apply "" arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact closedSkeleton_object (closedSkeletons_all closed argument member)
  | .lambda _ body, closed => by
    simp only [patternClosedSkeleton] at closed
    simp only [isObjectPattern]
    exact closedSkeleton_object closed
  | .multiLambda _ _ body, closed => by
    simp only [patternClosedSkeleton] at closed
    simp only [isObjectPattern]
    exact closedSkeleton_object closed
  | .subst _ _, closed => by simp [patternClosedSkeleton] at closed
  | .collection _ _ _, closed => by simp [patternClosedSkeleton] at closed
termination_by pattern => sizeOf pattern
where
  closedSkeletons_all {label : String} {arguments : List Pattern}
      (closed : patternClosedSkeleton (.apply label arguments) = true) :
      ∀ argument ∈ arguments, patternClosedSkeleton argument = true := by
    simp only [patternClosedSkeleton] at closed
    induction arguments with
    | nil => intro _ member; cases member
    | cons head tail ih =>
      simp only [patternsClosedSkeleton, Bool.and_eq_true] at closed
      intro argument member
      rcases List.mem_cons.mp member with rfl | inside
      · exact closed.1
      · exact ih closed.2 argument inside

theorem holeSkeletons_all {label : String} {arguments : List Pattern}
    (hole : patternHoleSkeleton (.apply label arguments) = true) :
    ∀ argument ∈ arguments, patternHoleSkeleton argument = true := by
  simp only [patternHoleSkeleton] at hole
  induction arguments with
  | nil => intro _ member; cases member
  | cons head tail ih =>
    simp only [patternsHoleSkeleton, Bool.and_eq_true] at hole
    intro argument member
    rcases List.mem_cons.mp member with rfl | inside
    · exact hole.1
    · exact ih hole.2 argument inside

/-- **Binding application to a hole skeleton gives an object term** when the values it uses are object
terms. -/
theorem applyBindings_object {bindings : Bindings} : ∀ {pattern : Pattern}, patternHoleSkeleton pattern = true →
    (∀ name ∈ patternOccurrenceNames pattern, ∀ value, Bindings.lookup bindings name = some value →
      isObjectPattern value = true) →
    isObjectPattern (applyBindings bindings pattern) = true
  | .bvar _, _, _ => by simp [applyBindings, isObjectPattern]
  | .fvar name, _, values => by
    rw [applyBindings_fvar]
    cases found : Bindings.lookup bindings name with
    | none => rfl
    | some value => exact values name (by simp) value found
  | .apply label arguments, hole, values => by
    simp only [applyBindings, isObjectPattern]
    refine (objectList_iff _).mpr fun argument member => ?_
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    have : sizeOf original < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem inside; simp only [Pattern.apply.sizeOf_spec]; omega
    exact applyBindings_object (holeSkeletons_all hole original inside) fun name occurs value found =>
      values name (by
        rw [CertificateGSLT.patternOccurrenceNames_apply]
        exact mem_patternsOccurrenceNames.mpr ⟨original, inside, occurs⟩) value found
  | .lambda binder body, hole, _ => by
    simp only [patternHoleSkeleton] at hole
    rw [applyBindings_closedSkeleton (pattern := .lambda binder body) (by simpa [patternClosedSkeleton] using hole)]
    exact closedSkeleton_object (by simpa [patternClosedSkeleton] using hole)
  | .multiLambda arity binders body, hole, _ => by
    simp only [patternHoleSkeleton] at hole
    rw [applyBindings_closedSkeleton (pattern := .multiLambda arity binders body)
      (by simpa [patternClosedSkeleton] using hole)]
    exact closedSkeleton_object (by simpa [patternClosedSkeleton] using hole)
  | .subst _ _, hole, _ => by simp [patternHoleSkeleton] at hole
  | .collection _ _ _, hole, _ => by simp [patternHoleSkeleton] at hole
termination_by pattern => sizeOf pattern

/-- **The values an object instance of a hole skeleton uses are object terms.** -/
theorem object_values {bindings : Bindings} : ∀ {pattern : Pattern}, patternHoleSkeleton pattern = true →
    isObjectPattern (applyBindings bindings pattern) = true →
    ∀ name ∈ patternOccurrenceNames pattern, ∀ value, Bindings.lookup bindings name = some value →
      isObjectPattern value = true
  | .bvar _, _, _ => by simp [patternOccurrenceNames, Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt]
  | .fvar name, _, object => by
    intro other occurs value found
    simp only [CertificateGSLT.patternOccurrenceNames_fvar, List.mem_singleton] at occurs
    subst occurs
    rw [applyBindings_fvar, found] at object
    exact object
  | .apply label arguments, hole, object => by
    intro name occurs value found
    rw [CertificateGSLT.patternOccurrenceNames_apply] at occurs
    obtain ⟨original, inside, occursThere⟩ := mem_patternsOccurrenceNames.mp occurs
    simp only [applyBindings, isObjectPattern] at object
    have : sizeOf original < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem inside; simp only [Pattern.apply.sizeOf_spec]; omega
    exact object_values (holeSkeletons_all hole original inside)
      ((objectList_iff _).mp object _ (List.mem_map_of_mem inside)) name occursThere value found
  | .lambda binder body, hole, _ => by
    intro name occurs
    simp only [patternHoleSkeleton] at hole
    have none := CertificateGSLT.patternOccurrenceNames_closed (pattern := .lambda binder body)
      (by simpa [patternClosedSkeleton] using hole)
    rw [none] at occurs
    cases occurs
  | .multiLambda arity binders body, hole, _ => by
    intro name occurs
    simp only [patternHoleSkeleton] at hole
    have none := CertificateGSLT.patternOccurrenceNames_closed (pattern := .multiLambda arity binders body)
      (by simpa [patternClosedSkeleton] using hole)
    rw [none] at occurs
    cases occurs
  | .subst _ _, hole, _ => by simp [patternHoleSkeleton] at hole
  | .collection _ _ _, hole, _ => by simp [patternHoleSkeleton] at hole
termination_by pattern => sizeOf pattern

/-! ## Instances read off a match -/

section Instances

variable {definition : ValidatedCalculusLanguageDef}

theorem lookup_rest_cons {value : Pattern} {bindings : Bindings} {name : String} (different : name ≠ restName) :
    Bindings.lookup ((restName, value) :: bindings) name = Bindings.lookup bindings name := by
  have : (restName == name) = false := by
    rw [beq_eq_false_iff_ne]; exact fun same => different same.symm
  simp [Bindings.lookup, this]

/-- **Matching a moded conclusion against a proper goal gives the instance**: the arguments read off the
match instantiate the conclusion to the goal and the premises to the premises under the match. -/
theorem instance_of_match {rule : RuleSchema} (inRules : rule ∈ definition.1.rules) (isModed : moded rule = true)
    {goal : Pattern} {bindings : Bindings} (proper : ProperGoal goal)
    (matched : bindings ∈ matchPattern rule.conclusion goal) :
    instantiateRule? definition ⟨rule.id, bindingsArguments rule.metavariables bindings⟩ =
        some (rule.premises.map (applyBindings bindings), goal) ∧
      (∀ pair ∈ bindings, pair.1 ≠ restName) ∧ bindingsValuesWellFormed bindings ∧
      (∀ name ∈ patternOccurrenceNames rule.conclusion, (Bindings.lookup bindings name).isSome) := by
  obtain ⟨sides, depths, fresh, conclusionHole, premisesHole, _, _, conclusionCanonical, _, conclusionNames,
    formalsOccur, premiseNames⟩ := parts isModed
  obtain ⟨reconstruct, keys, cover, values⟩ :=
    matchPattern_holeSkeleton_sound conclusionHole conclusionCanonical proper.1 proper.2.1 bindings matched
  have coverFormals : ∀ name ∈ rule.metavariables.map Prod.fst, (Bindings.lookup bindings name).isSome :=
    fun name member => cover name (formalsOccur name member)
  have lengths : rule.metavariables.length = (bindingsArguments rule.metavariables bindings).length := by
    simp [bindingsArguments]
  have zipCover : ∀ name ∈ rule.metavariables.map Prod.fst,
      (Bindings.lookup (zipBindings rule.metavariables (bindingsArguments rule.metavariables bindings)) name).isSome :=
    zipBindings_covers lengths
  have zipLookup := zipBindings_bindingsArguments_lookup rule.metavariables bindings coverFormals
  have premisesInstance : instantiateSchemas? rule.metavariables (bindingsArguments rule.metavariables bindings)
      rule.premises = some (rule.premises.map (applyBindings bindings)) := by
    rw [instantiateSchemas?, instantiateSchemasAt?_eq_applyBindings premisesHole depths
      (fun name member => zipCover name (conclusionNames name (premiseNames name member)))]
    congr 1
    exact applyBindingsList_agree premisesHole fun name member =>
      zipLookup name (conclusionNames name (premiseNames name member))
  have conclusionInstance : instantiateSchema? rule.metavariables (bindingsArguments rule.metavariables bindings)
      rule.conclusion = some goal := by
    rw [instantiateSchema?, instantiateSchemaAt?_eq_applyBindings conclusionHole depths
      (fun name member => zipCover name (conclusionNames name member))]
    congr 1
    rw [← reconstruct]
    exact applyBindings_agree conclusionHole fun name member => zipLookup name (conclusionNames name member)
  refine ⟨?_, fun pair member same => fresh (same ▸ conclusionNames _ (keys pair member)), values, cover⟩
  simp only [instantiateRule?, lookupRule?_eq_some_of_mem definition inRules,
    argumentsValidAt_bindingsArguments depths values coverFormals, ↓reduceIte,
    RuleSchema.sideConditionsHold_of_empty rule _ sides, premisesInstance, conclusionInstance]
  rfl

/-- **A rule instance of a moded rule** is binding application with its positional assignment. -/
theorem instance_parts {rule : RuleSchema} (inRules : rule ∈ definition.1.rules) (isModed : moded rule = true)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (instantiated : instantiateRule? definition ⟨rule.id, arguments⟩ = some (premises, conclusion)) :
    premises = rule.premises.map (applyBindings (zipBindings rule.metavariables arguments)) ∧
      conclusion = applyBindings (zipBindings rule.metavariables arguments) rule.conclusion ∧
      argumentsValidAt rule.metavariables arguments = true := by
  obtain ⟨_, depths, _, conclusionHole, premisesHole, _, _, _, _, conclusionNames, _, premiseNames⟩ := parts isModed
  simp only [instantiateRule?, lookupRule?_eq_some_of_mem definition inRules] at instantiated
  by_cases valid : argumentsValidAt rule.metavariables arguments = true
  · have zipCover : ∀ name ∈ rule.metavariables.map Prod.fst,
        (Bindings.lookup (zipBindings rule.metavariables arguments) name).isSome :=
      zipBindings_covers (argumentsValidAt_length valid)
    have premisesInstance : instantiateSchemas? rule.metavariables arguments rule.premises =
        some (rule.premises.map (applyBindings (zipBindings rule.metavariables arguments))) := by
      rw [instantiateSchemas?, instantiateSchemasAt?_eq_applyBindings premisesHole depths
        (fun name member => zipCover name (conclusionNames name (premiseNames name member)))]
    have conclusionInstance : instantiateSchema? rule.metavariables arguments rule.conclusion =
        some (applyBindings (zipBindings rule.metavariables arguments) rule.conclusion) := by
      rw [instantiateSchema?, instantiateSchemaAt?_eq_applyBindings conclusionHole depths
        (fun name member => zipCover name (conclusionNames name member))]
    cases sides : RuleSchema.sideConditionsHold rule arguments with
    | false => simp [valid, sides] at instantiated
    | true =>
      simp only [valid, sides, ↓reduceIte, premisesInstance, conclusionInstance] at instantiated
      change some (_, _) = some (premises, conclusion) at instantiated
      simp only [Option.some.injEq, Prod.mk.injEq] at instantiated
      exact ⟨instantiated.1.symm, instantiated.2.symm, valid⟩
  · simp [valid] at instantiated

end Instances

/-! ## One step -/

theorem groundList_iff (patterns : List Pattern) :
    Pattern.isGroundListAt 0 patterns = true ↔ ∀ pattern ∈ patterns, pattern.isGroundAt 0 = true := by
  induction patterns with
  | nil => simp [Pattern.isGroundListAt]
  | cons head tail ih => simp [Pattern.isGroundListAt, ih]

section Steps

variable {relEnv : RelationEnv} {definition : ValidatedCalculusLanguageDef}

theorem presentation_rule {index : ℕ} {rewrite : RewriteRule}
    (found : (presentation definition.1).rewrites[index]? = some rewrite) :
    ∃ rule ∈ definition.1.rules, moded rule = true ∧ rewrite = presentationRule rule := by
  simp only [presentation, List.getElem?_map, Option.map_eq_some_iff] at found
  obtain ⟨rule, found, rfl⟩ := found
  obtain ⟨inRules, isModed⟩ := List.mem_filter.mp (List.mem_of_getElem? found)
  exact ⟨rule, inRules, by simpa using isModed, rfl⟩

theorem presentation_index {rule : RuleSchema} (inRules : rule ∈ definition.1.rules) (isModed : moded rule = true) :
    ∃ index : ℕ, (presentation definition.1).rewrites[index]? = some (presentationRule rule) := by
  obtain ⟨index, within, found⟩ := List.getElem_of_mem (List.mem_filter.mpr ⟨inRules, by simpa using isModed⟩)
  exact ⟨index, by simp [presentation, List.getElem?_map, List.getElem?_eq_getElem within, found]⟩

/-- A match of a goal-stack rule splits the stack into its first goal and the rest. -/
theorem match_stack {rule : RuleSchema} {goals : List Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (presentationRule rule).left (stack goals)) :
    ∃ goal rest conclusionBindings, goals = goal :: rest ∧ conclusionBindings ∈ matchPattern rule.conclusion goal ∧
      mergeBindings conclusionBindings [(restName, stack rest)] = some bindings := by
  have relation : MatchRel (.collection .vec [rule.conclusion] (some restName)) (.collection .vec goals none) bindings :=
    matchPattern_iff_matchRel.mp matched
  obtain ⟨leading, trailing, prefixBindings, split, prefixMatch, merged⟩ := matchRel_vectorRest_iff_split.mp relation
  cases prefixMatch with
  | cons headMatch tailMatch headMerged =>
    cases tailMatch
    rename_i goal headBindings
    have same : headBindings = prefixBindings := by
      simpa [mergeBindings] using headMerged
    subst same
    exact ⟨goal, trailing, headBindings, by simpa using split, matchPattern_iff_matchRel.mpr headMatch, merged⟩

theorem merge_rest {bindings : Bindings} {value : Pattern} (fresh : ∀ pair ∈ bindings, pair.1 ≠ restName) :
    mergeBindings bindings [(restName, value)] = some ((restName, value) :: bindings) := by
  have none : bindings.find? (fun pair => pair.1 == restName) = none :=
    List.find?_eq_none.mpr fun pair member => by simpa using fresh pair member
  simp [mergeBindings, none]

/-- **Firing a goal-stack rule** puts the premises under the match in front of the rest. -/
theorem fire_stack {rule : RuleSchema} (isModed : moded rule = true) (bindings : Bindings) (rest : List Pattern) :
    applyBindingsScoped (captureSites (presentationRule rule)) ((restName, stack rest) :: bindings) 0
        (presentationRule rule).right =
      stack (rule.premises.map (applyBindings bindings) ++ rest) := by
  obtain ⟨_, _, _, conclusionHole, premisesHole, _⟩ := parts isModed
  have ambient : ∀ name captured, captureDepth name 0 (captureSites (presentationRule rule)) = some captured →
      captured = 0 := by
    intro name captured found
    simp only [captureSites, captureSitesOf, List.foldl_nil, presentationRule, captureDepth, captureDepthList] at found
    cases inConclusion : captureDepth name 0 rule.conclusion with
    | some depth =>
      rw [inConclusion] at found
      simp only [Option.some.injEq] at found
      exact found ▸ captureDepth_of_holeSkeleton conclusionHole name 0 depth inConclusion
    | none =>
      rw [inConclusion] at found
      by_cases same : restName = name
      · simp [same] at found; exact found.symm
      · simp [same] at found
  have premisesHoles : ∀ premise ∈ rule.premises, patternHoleSkeleton premise = true := by
    have := holeSkeletons_all (label := "") (arguments := rule.premises) (by simpa [patternHoleSkeleton] using premisesHole)
    exact this
  have mapped : rule.premises.map (applyBindingsScoped (captureSites (presentationRule rule))
      ((restName, stack rest) :: bindings) 0) = rule.premises.map (applyBindings bindings) := by
    refine List.map_congr_left fun premise member => ?_
    rw [applyBindingsScoped_eq_applyBindings _ _ 0 premise
      (depthAligned_of_holeSkeleton _ ambient (premisesHoles premise member))]
    refine applyBindings_agree (premisesHoles premise member) fun name occurs => lookup_rest_cons fun same => ?_
    exact rest_not_in_premises isModed (same ▸ mem_patternsOccurrenceNames.mpr ⟨premise, member, occurs⟩)
  simp only [presentationRule, stack] at mapped
  simp only [presentationRule, applyBindingsScoped, applyBindingsScopedList_eq_map, restSplice, List.find?_cons,
    beq_self_eq_true, ↓reduceIte, stack, mapped]
  congr 2
  split <;> simp [map_liftBVars_zero]

/-- **Moded resolution keeps goals proper.** -/
theorem moded_step_proper {goals goals' : List Pattern} (proper : ∀ goal ∈ goals, ProperGoal goal)
    (step : ModedResolves definition goals goals') : ∀ goal ∈ goals', ProperGoal goal := by
  obtain ⟨rule, inRules, isModed, arguments, premises, conclusion, rest, instantiated, rfl, rfl⟩ := step
  obtain ⟨premisesShape, conclusionShape, valid⟩ := instance_parts inRules isModed instantiated
  obtain ⟨_, depths, _, conclusionHole, premisesHole, _, premisesScoped, _, premisesCanonical, conclusionNames, _,
    premiseNames⟩ := parts isModed
  have conclusionProper := proper conclusion List.mem_cons_self
  have zipCover : ∀ name ∈ rule.metavariables.map Prod.fst,
      (Bindings.lookup (zipBindings rule.metavariables arguments) name).isSome :=
    zipBindings_covers (argumentsValidAt_length valid)
  have values : bindingsValuesWellFormed (zipBindings rule.metavariables arguments) :=
    argumentsValidAt_zip_values depths valid
  have objects := object_values conclusionHole (conclusionShape ▸ conclusionProper.2.2)
  intro goal member
  rcases List.mem_append.mp member with inside | inside
  · rw [premisesShape] at inside
    obtain ⟨premise, premiseMember, rfl⟩ := List.mem_map.mp inside
    have premisesHoles : ∀ premise ∈ rule.premises, patternHoleSkeleton premise = true :=
      holeSkeletons_all (label := "") (by simpa [patternHoleSkeleton] using premisesHole)
    have wellFormed := applyBindingsList_wellFormed premisesHole premisesScoped premisesCanonical values
      (fun name member => zipCover name (conclusionNames name (premiseNames name member)))
    have ground := (groundList_iff _).mp wellFormed.1 _ (List.mem_map_of_mem premiseMember)
    have canonical :=
      (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp wellFormed.2 _ (List.mem_map_of_mem premiseMember)
    refine ⟨ground, canonical, applyBindings_object (premisesHoles premise premiseMember) fun name occurs value found => ?_⟩
    exact objects name (premiseNames name (mem_patternsOccurrenceNames.mpr ⟨premise, premiseMember, occurs⟩)) value found
  · exact proper goal (List.mem_cons_of_mem _ inside)

/-- **Soundness**: a step of the presentation from a proper goal stack is a resolution step by a moded
rule, to a proper goal stack. -/
theorem step_sound {goals : List Pattern} {witness : Witness} {target : Pattern}
    (proper : ∀ goal ∈ goals, ProperGoal goal)
    (valid : StepValid relEnv (presentation definition.1) (stack goals) witness target) :
    ∃ goals', target = stack goals' ∧ ModedResolves definition goals goals' ∧ ∀ goal ∈ goals', ProperGoal goal := by
  cases valid with
  | rule found matched premises =>
    rename_i index rewrite initial final witnesses
    obtain ⟨rule, inRules, isModed, rfl⟩ := presentation_rule found
    cases premises
    rw [matchPatternForRule_eq_syntactic] at matched
    obtain ⟨goal, rest, conclusionBindings, rfl, conclusionMatched, merged⟩ := match_stack matched
    obtain ⟨instantiated, fresh, _, _⟩ :=
      instance_of_match inRules isModed (proper goal List.mem_cons_self) conclusionMatched
    rw [merge_rest fresh, Option.some.injEq] at merged
    subst merged
    have step : ModedResolves definition (goal :: rest) (rule.premises.map (applyBindings conclusionBindings) ++ rest) :=
      ⟨rule, inRules, isModed, _, _, _, rest, instantiated, rfl, rfl⟩
    exact ⟨_, fire_stack isModed conclusionBindings rest, step, moded_step_proper proper step⟩

/-- **Completeness**: a resolution step by a moded rule from a proper goal list is a step of the
presentation. -/
theorem step_complete {goals goals' : List Pattern} (proper : ∀ goal ∈ goals, ProperGoal goal)
    (step : ModedResolves definition goals goals') :
    ∃ witness, StepValid relEnv (presentation definition.1) (stack goals) witness (stack goals') := by
  obtain ⟨rule, inRules, isModed, arguments, premises, conclusion, rest, instantiated, rfl, rfl⟩ := step
  obtain ⟨premisesShape, conclusionShape, valid⟩ := instance_parts inRules isModed instantiated
  obtain ⟨_, _, _, conclusionHole, premisesHole, _, _, _, _, conclusionNames, _, premiseNames⟩ := parts isModed
  have zipCover : ∀ name ∈ rule.metavariables.map Prod.fst,
      (Bindings.lookup (zipBindings rule.metavariables arguments) name).isSome :=
    zipBindings_covers (argumentsValidAt_length valid)
  obtain ⟨bindings, matched, agree, cover⟩ := matchPattern_own_instance conclusionHole
    (fun name member => zipCover name (conclusionNames name member))
  rw [← conclusionShape] at matched
  obtain ⟨_, fresh, _, _⟩ := instance_of_match inRules isModed (proper conclusion List.mem_cons_self) matched
  obtain ⟨index, found⟩ := presentation_index inRules isModed
  have stackMatched : (restName, stack rest) :: bindings ∈
      matchPattern (presentationRule rule).left (stack (conclusion :: rest)) := by
    refine matchPattern_iff_matchRel.mpr (MatchRel.vectorRest (prefixBindings := bindings) ?_ (merge_rest fresh))
    exact .cons (matchPattern_iff_matchRel.mp matched) .nil (by simp [mergeBindings])
  have fired := StepValid.rule (relEnv := relEnv) found
    (by rw [matchPatternForRule_eq_syntactic]; exact stackMatched) (PremisesValid.nil _)
  rw [fire_stack isModed] at fired
  have samePremises : rule.premises.map (applyBindings bindings) = premises := by
    rw [premisesShape]
    refine applyBindingsList_agree premisesHole fun name occurs => ?_
    obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp (cover name (premiseNames name occurs))
    rw [found, bindingsAgreeWith_lookup agree found]
  rw [samePremises] at fired
  exact ⟨_, fired⟩

end Steps

/-! ## Judgments only moded rules conclude -/

/-- The constructor at the head of a judgment. -/
def head : Pattern → Option String
  | .apply constructor _ => some constructor
  | _ => none

/-- A judgment with one of these heads. -/
def headIn (heads : List String) (pattern : Pattern) : Bool := (head pattern).any heads.contains

/-- **Judgments only moded rules conclude**: every rule that can conclude a judgment with one of these heads
is moded, and its premises have such heads. -/
def modedHeads (definition : CalculusLanguageDef) (heads : List String) : Bool :=
  definition.rules.all fun rule =>
    !((head rule.conclusion).all heads.contains) || (moded rule && rule.premises.all (headIn heads))

theorem headIn_instance {heads : List String} {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schema result : Pattern} (instantiates : InstantiatesAt formals arguments depth schema result)
    (within : headIn heads schema = true) : headIn heads result = true := by
  cases schema with
  | apply constructor schemas =>
    cases instantiates
    exact within
  | _ => simp [headIn, head] at within

theorem headIn_instances {heads : List String} {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} : ∀ {schemas results : List Pattern}, InstantiatesListAt formals arguments depth schemas results →
      (∀ schema ∈ schemas, headIn heads schema = true) → ∀ result ∈ results, headIn heads result = true
  | [], _, instantiates, _ => by cases instantiates; intro _ member; cases member
  | _ :: _, _, instantiates, within => by
    cases instantiates with
    | cons first rest =>
      intro result member
      rcases List.mem_cons.mp member with rfl | inside
      · exact headIn_instance first (within _ List.mem_cons_self)
      · exact headIn_instances rest (fun schema member => within schema (List.mem_cons_of_mem _ member)) result inside

/-- **Where only moded rules conclude, resolution is moded resolution**, and stays there. -/
theorem resolves_moded {definition : ValidatedCalculusLanguageDef} {heads : List String}
    (headsModed : modedHeads definition.1 heads = true) {goals goals' : List Pattern}
    (within : ∀ goal ∈ goals, headIn heads goal = true) (step : Resolves definition goals goals') :
    ModedResolves definition goals goals' ∧ ∀ goal ∈ goals', headIn heads goal = true := by
  obtain ⟨⟨ruleId, arguments⟩, premises, conclusion, rest, instantiated, rfl, rfl⟩ := step
  obtain ⟨rule, lookup, _, _, premisesInstantiate, conclusionInstantiates⟩ :=
    instantiateRule?_eq_some_iff_application.mp instantiated
  have member : rule ∈ definition.1.rules := List.mem_of_find?_eq_some lookup
  have sameId : rule.id = ruleId := by simpa using List.find?_some lookup
  subst sameId
  have conclusionHead : (head rule.conclusion).all heads.contains = true := by
    have goalHead := within conclusion List.mem_cons_self
    cases shape : rule.conclusion with
    | apply constructor schemas =>
      rw [shape] at conclusionInstantiates
      cases conclusionInstantiates
      exact goalHead
    | _ => rfl
  have ruleOk := List.all_eq_true.mp headsModed rule member
  simp only [conclusionHead, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at ruleOk
  obtain ⟨isModed, premiseHeads⟩ := ruleOk
  refine ⟨⟨rule, member, isModed, arguments, premises, conclusion, rest, instantiated, rfl, rfl⟩, ?_⟩
  intro goal inside
  rcases List.mem_append.mp inside with inside | inside
  · exact headIn_instances premisesInstantiate premiseHeads goal inside
  · exact within goal (List.mem_cons_of_mem _ inside)

/-! ## Runs and derivability -/

section Runs

variable {relEnv : RelationEnv} {definition : ValidatedCalculusLanguageDef}

/-- One step of the presentation between goal lists. -/
def StackStep (relEnv : RelationEnv) (definition : ValidatedCalculusLanguageDef) (source target : List Pattern) :
    Prop :=
  ∃ witness, StepValid relEnv (presentation definition.1) (stack source) witness (stack target)

theorem stack_injective {first second : List Pattern} (same : stack first = stack second) : first = second := by
  simpa [stack] using same

/-- **A step of the presentation is a resolution step**, so reaching the empty stack yields derivations, in
any calculus. -/
theorem multiStep_of_reaches {goals goals' : List Pattern}
    (reaches : Relation.ReflTransGen (StackStep relEnv definition) goals goals') :
    (∀ goal ∈ goals, ProperGoal goal) → (proofSearchGSLT definition).MultiStep goals goals' := by
  induction reaches using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; exact Mettapedia.GSLT.GSLT.MultiStep.refl _
  | head step _ ih =>
    intro proper
    obtain ⟨witness, valid⟩ := step
    obtain ⟨next, same, moded, proper'⟩ := step_sound proper valid
    rw [stack_injective same] at ih
    exact .step moded.resolves (ih proper')

/-- **Where only moded rules conclude, resolution runs are runs of the presentation.** -/
theorem reaches_of_multiStep {heads : List String} (headsModed : modedHeads definition.1 heads = true)
    {goals goals' : List Pattern} (steps : (proofSearchGSLT definition).MultiStep goals goals')
    (proper : ∀ goal ∈ goals, ProperGoal goal) (within : ∀ goal ∈ goals, headIn heads goal = true) :
    Relation.ReflTransGen (StackStep relEnv definition) goals goals' :=
  match steps with
  | .refl _ => .refl
  | .step first rest =>
    have moded := resolves_moded headsModed within first
    .head (step_complete proper moded.1) (reaches_of_multiStep headsModed rest (moded_step_proper proper moded.1) moded.2)

/-- **Derivability is reaching the empty stack**, for proper goal lists where only moded rules conclude. -/
theorem derivable_iff_reaches {heads : List String} (headsModed : modedHeads definition.1 heads = true)
    {goals : List Pattern} (proper : ∀ goal ∈ goals, ProperGoal goal)
    (within : ∀ goal ∈ goals, headIn heads goal = true) :
    Nonempty (DerivationList definition goals) ↔ Relation.ReflTransGen (StackStep relEnv definition) goals [] := by
  rw [CalculusAsLanguage.derivationList_nonempty_iff_proofSearch]
  exact ⟨fun steps => reaches_of_multiStep headsModed steps proper within,
    fun reaches => multiStep_of_reaches reaches proper⟩

end Runs

/-! ## In the generated logic -/

section Logic

universe u

/-- **"Some run reaches `target`"** holds exactly where some run of `label`-steps reaches an element named
by `target`. -/
theorem sat_reaches_iff {Carrier : Type u} (S : NativeStructure Carrier) (label : StepLabel) (target : Pattern)
    (element : Carrier) :
    S.sat Env.closed (.mu (.or (.is target) (.possibly label (.var 0)))) element ↔
      ∃ last, Relation.ReflTransGen (fun first second => S.step first label second) element last ∧
        S.named last target := by
  constructor
  · intro holds
    refine holds {other | ∃ last, Relation.ReflTransGen (fun first second => S.step first label second) other last ∧
      S.named last target} ?_
    intro other prefixed
    rcases prefixed with named | ⟨next, step, inside⟩
    · exact ⟨other, .refl, named⟩
    · obtain ⟨last, path, named⟩ := inside
      exact ⟨last, .head step path, named⟩
  · rintro ⟨last, path, named⟩ closed prefixed
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact prefixed last (Or.inl named)
    | head step _ inside => exact prefixed _ (Or.inr ⟨_, step, inside⟩)

/-- Some run reaches the empty goal stack. -/
def reachesEmpty : Formula 0 := .mu (.or (.is (stack [])) (.possibly .any (.var 0)))

variable {relEnv : RelationEnv} {definition : ValidatedCalculusLanguageDef}

theorem presentation_equationFree (definition : CalculusLanguageDef) :
    (presentation definition).isEquationFree = true := rfl

theorem wellScopedList_of_ground : ∀ {patterns : List Pattern}, (∀ pattern ∈ patterns, pattern.isGroundAt 0 = true) →
    Pattern.isWellScopedListAt 0 patterns = true
  | [], _ => rfl
  | pattern :: patterns, ground => by
    simp only [Pattern.isWellScopedListAt, Bool.and_eq_true]
    exact ⟨Mettapedia.OSLF.MeTTaIL.Substitution.isWellScopedAt_of_isGroundAt (ground pattern List.mem_cons_self),
      wellScopedList_of_ground fun other member => ground other (List.mem_cons_of_mem _ member)⟩

/-- A proper goal stack is a state. -/
theorem stack_state {goals : List Pattern} (proper : ∀ goal ∈ goals, ProperGoal goal) : IsState (stack goals) :=
  ⟨by simpa [stack, Pattern.isWellScopedAt] using wellScopedList_of_ground fun goal member => (proper goal member).1,
    by
      show isObjectPattern (.collection .vec goals none) = true
      simpa [isObjectPattern] using (objectList_iff goals).mpr fun goal member => (proper goal member).2.2⟩

/-- A step of the presentation's structure from a proper goal stack. -/
theorem reference_step {goals : List Pattern} (proper : ∀ goal ∈ goals, ProperGoal goal) {label : StepLabel}
    {element : Pattern} (step : (referenceStructure relEnv (presentation definition.1)).step (stack goals) label element) :
    ∃ goals', element = stack goals' ∧ StackStep relEnv definition goals goals' ∧ ∀ goal ∈ goals', ProperGoal goal := by
  obtain ⟨_, _, redex, contractum, witness, before, _, valid, _, after, _⟩ := step
  rw [objectEquivalent_iff_eq_of_isEquationFree (presentation_equationFree definition.1)] at before after
  subst before
  subst after
  obtain ⟨goals', rfl, _, proper'⟩ := step_sound proper valid
  exact ⟨goals', rfl, ⟨witness, valid⟩, proper'⟩

/-- A step of the presentation is a step of its structure. -/
theorem stack_step {goals goals' : List Pattern} (proper : ∀ goal ∈ goals, ProperGoal goal)
    (step : StackStep relEnv definition goals goals') :
    (referenceStructure relEnv (presentation definition.1)).step (stack goals) .any (stack goals') ∧
      ∀ goal ∈ goals', ProperGoal goal := by
  obtain ⟨witness, valid⟩ := step
  obtain ⟨goals'', same, _, proper''⟩ := step_sound proper valid
  rw [← stack_injective same] at proper''
  exact ⟨⟨stack_state proper, stack_state proper'', stack goals, stack goals', witness, Relation.EqvGen.refl _,
    stack_state proper, valid, stack_state proper'', Relation.EqvGen.refl _, rfl⟩, proper''⟩

theorem path_of_reaches {goals goals' : List Pattern} (proper : ∀ goal ∈ goals, ProperGoal goal)
    (reaches : Relation.ReflTransGen (StackStep relEnv definition) goals goals') :
    Relation.ReflTransGen (fun first second => (referenceStructure relEnv (presentation definition.1)).step first .any second)
        (stack goals) (stack goals') ∧ ∀ goal ∈ goals', ProperGoal goal := by
  induction reaches with
  | refl => exact ⟨.refl, proper⟩
  | tail _ step ih =>
    obtain ⟨path, middle⟩ := ih
    obtain ⟨last, proper'⟩ := stack_step middle step
    exact ⟨.tail path last, proper'⟩

theorem reaches_of_path {goals : List Pattern} (proper : ∀ goal ∈ goals, ProperGoal goal) {element : Pattern}
    (path : Relation.ReflTransGen (fun first second =>
      (referenceStructure relEnv (presentation definition.1)).step first .any second) (stack goals) element) :
    ∃ goals', element = stack goals' ∧ Relation.ReflTransGen (StackStep relEnv definition) goals goals' ∧
      ∀ goal ∈ goals', ProperGoal goal := by
  induction path with
  | refl => exact ⟨goals, rfl, .refl, proper⟩
  | tail _ step ih =>
    obtain ⟨middle, rfl, reaches, properMiddle⟩ := ih
    obtain ⟨last, rfl, stackStep, properLast⟩ := reference_step properMiddle step
    exact ⟨last, rfl, .tail reaches stackStep, properLast⟩

/-- **"Some run reaches the empty stack" is reaching it by steps of the presentation**, from a proper goal
stack. -/
theorem sat_reachesEmpty_iff {goals : List Pattern} (proper : ∀ goal ∈ goals, ProperGoal goal) :
    (referenceStructure relEnv (presentation definition.1)).sat Env.closed reachesEmpty (stack goals) ↔
      Relation.ReflTransGen (StackStep relEnv definition) goals [] := by
  rw [reachesEmpty, sat_reaches_iff]
  constructor
  · rintro ⟨last, path, named⟩
    have empty : last = stack [] :=
      (objectEquivalent_iff_eq_of_isEquationFree (presentation_equationFree definition.1)).mp named.2
    subst empty
    obtain ⟨goals', same, reaches, _⟩ := reaches_of_path proper path
    rw [stack_injective same.symm] at reaches
    exact reaches
  · intro reaches
    exact ⟨stack [], (path_of_reaches proper reaches).1, (stack_state (by simp)).2, Relation.EqvGen.refl _⟩

/-- **A stack the generated logic sees reach the empty stack is derivable**, in any calculus. -/
theorem derivable_of_sat {goals : List Pattern} (proper : ∀ goal ∈ goals, ProperGoal goal)
    (holds : (referenceStructure relEnv (presentation definition.1)).sat Env.closed reachesEmpty (stack goals)) :
    Nonempty (DerivationList definition goals) :=
  (CalculusAsLanguage.derivationList_nonempty_iff_proofSearch definition goals).mpr
    (multiStep_of_reaches ((sat_reachesEmpty_iff proper).mp holds) proper)

/-- **Derivability is the formula "some run reaches the empty stack"**, for proper goal lists where only
moded rules conclude. -/
theorem derivable_iff_sat {heads : List String} (headsModed : modedHeads definition.1 heads = true)
    {goals : List Pattern} (proper : ∀ goal ∈ goals, ProperGoal goal)
    (within : ∀ goal ∈ goals, headIn heads goal = true) :
    Nonempty (DerivationList definition goals) ↔
      (referenceStructure relEnv (presentation definition.1)).sat Env.closed reachesEmpty (stack goals) := by
  rw [sat_reachesEmpty_iff proper]
  exact derivable_iff_reaches headsModed proper within

end Logic

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CalculusPresentation
