import Mettapedia.OSLF.Framework.GeneralCanonicalQueryAgreement
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionOrder
import Mettapedia.OSLF.MeTTaIL.ContextualStepFuel

/-!
# Agreement for first-order rules with premises

A congruence premise `s ~> t` asks for a step of the instantiated source and
matches its result against `t`. The canonical engine takes that step with the
whole language, one contextual layer down; the general semantics fires a child
rule at the instantiated source. A relation query reads a provider row in the
general semantics and a tuple of the relation environment in the canonical one.
This module proves the two step relations agree for every language whose rules
are first-order, constructor-headed and typed, and whose premises are
first-order congruences, freshness conditions and relation queries, when the
relation environment reads the provider.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.Match MeTTaIL.ContextualStep

open MeTTaIL.ScopedRuleMatching MeTTaIL.RuleBinding MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

/-! ## The congruence profile -/

/-- A first-order congruence premise, a freshness premise with a first-order
subject, or a query of a provided relation with first-order arguments. The
relation `eq` is excluded: the canonical engine answers it itself. -/
def SupportedPremise (premise : Premise) : Prop :=
  (∃ source target, premise = .congruence source target ∧ FirstOrder source ∧ FirstOrder target) ∨
    (∃ condition, premise = .freshness condition ∧ FirstOrder condition.term) ∨
    ∃ relation arguments, premise = .relationQuery relation arguments ∧ relation ≠ "eq" ∧
      ∀ argument ∈ arguments, FirstOrder argument

/-- The parts of a rule that the canonical step reads. -/
def ruleCore (rule : RewriteRule) : Pattern × Pattern × List Premise :=
  (rule.left, rule.right, rule.premises)

/-- The admitted first-order row facts shared by headed and variable-root
rules. Selection at an invocation sort is a separate computation. -/
structure FirstOrderRowFacts (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (index : Nat) (rule : RewriteRule) : Prop where
  specified : GeneralPremise.specification? (environment language provider) index =
    some (GeneralRuleBindingInference.inferredSpec rule)
  admitted : admittedFor rule (GeneralRuleBindingInference.inferredSpec rule) = true
  left : FirstOrder rule.left
  right : FirstOrder rule.right
  premises : ∀ premise ∈ rule.premises, SupportedPremise premise
  flow : GeneralPremise.rulePremisesAdmitted (environment language provider).language
    (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule) = true
  unique : (rule.typeContext.map Prod.fst).Nodup
  aligned : ruleDepthAligned rule = true
  typed : ∃ type,
    Mettapedia.GSLT.LanguageDef.WellSorted.HasType (environment language provider).language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList rule.typeContext) []
        rule.left type ∧
      Mettapedia.GSLT.LanguageDef.WellSorted.HasType (environment language provider).language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList rule.typeContext) []
        rule.right type

/-- The rows of the unguarded canonical comparison retain their constructor
head restriction. A variable root instead needs the checked sort guard. -/
structure FirstOrderRow (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (index : Nat) (rule : RewriteRule) : Prop extends FirstOrderRowFacts language provider index rule where
  headed : ∃ label arguments, rule.left = .apply label arguments

/-- A language whose rules are first-order and typed, and conditioned only on
first-order congruences, freshness conditions and queries, run at the root over
a provider whose rows are closed and typed. -/
structure FirstOrderProfileFacts (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot) : Prop where
  valid : (environment language provider).language.validate = []
  providerClosed : GeneralPremise.checkProviderClosed (environment language provider).language
    (environment language provider).free (environment language provider).provider = true
  equationFree : language.isEquationFree = true
  equations : (rootPlan language provider).equations = []
  sameRules : (environment language provider).language.rewrites.map ruleCore = language.rewrites.map ruleCore
  rowFacts : ∀ {index : Nat} {rule : RewriteRule},
    (environment language provider).language.rewrites[index]? = some rule → FirstOrderRowFacts language provider index rule
  noDynamic : provider.dynamicRelations = []

/-- Constructor-headed presentations retain the unguarded canonical theorem.
The common profile facts also admit checked variable-root rules. -/
structure FirstOrderProfile (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot) : Prop
    extends FirstOrderProfileFacts language provider where
  headed : ∀ {index : Nat} {rule : RewriteRule},
    (environment language provider).language.rewrites[index]? = some rule →
      ∃ label arguments, rule.left = .apply label arguments

theorem FirstOrderProfile.rows {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}
    (profile : FirstOrderProfile language provider) {index : Nat} {rule : RewriteRule}
    (declared : (environment language provider).language.rewrites[index]? = some rule) :
    FirstOrderRow language provider index rule :=
  ⟨profile.rowFacts declared, profile.headed declared⟩

instance {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot} :
    Coe (FirstOrderProfile language provider) (FirstOrderProfileFacts language provider) :=
  ⟨FirstOrderProfile.toFirstOrderProfileFacts⟩

/-! ## From the general firing to the canonical step -/

open MeTTaIL.MatchSpec MeTTaIL.ReflectiveCanonical MeTTaIL.ReflectiveSubstitution

/-- Supported premises keep the assignment typed. -/
theorem premisesHold_typed {environment : GeneralPremise.Environment} :
    ∀ {context : GeneralPremise.Context} {premises : List Premise} {initial final : Assignment}
      {events : List GeneralPremise.Event},
      GeneralPremise.PremisesHold environment context premises initial final events →
      (∀ premise ∈ premises, SupportedPremise premise) →
      GeneralPremise.TypedAssignment environment context initial →
      GeneralPremise.TypedAssignment environment context final := by
  intro context premises
  induction premises generalizing context with
  | nil => intro initial final events held _ typed; cases held; exact typed
  | cons premise premises inductionHypothesis =>
    intro initial final events held congruent initialTyped
    cases held with
    | cons head tail =>
      have rest := fun other member => congruent other (List.mem_cons_of_mem _ member)
      rcases congruent premise (by simp) with ⟨source, target, same, _, _⟩ | ⟨condition, same, _⟩ |
          ⟨relation, arguments, same, _, _⟩
      · subst same
        cases head with
        | step _ _ _ _ middleTyped =>
          exact inductionHypothesis (context := context.next) tail rest middleTyped
      · subst same
        cases head with
        | freshness _ _ => exact inductionHypothesis (context := context.next) tail rest initialTyped
      · subst same
        cases head with
        | query traced =>
          exact inductionHypothesis (context := context.next) tail rest traced.final_typed

/-- The rule-local sort lookup used by admission is the rule's type context. -/
theorem lookupRuleType_eq (rule : RewriteRule) :
    (fun name => GeneralPremise.lookupRuleType? rule name) =
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList rule.typeContext := by
  funext name
  rw [context_ofList_lookup]
  unfold GeneralPremise.lookupRuleType?
  generalize rule.typeContext = context
  induction context with
  | nil => rfl
  | cons pair rest inductionHypothesis =>
    obtain ⟨key, value⟩ := pair
    by_cases same : key = name
    · subst same
      simp [List.find?, List.lookup]
    · have left : (key == name) = false := by simp [same]
      have right : (name == key) = false := by simp [Ne.symm same]
      simp only [List.find?, left, List.lookup, right]
      exact inductionHypothesis

theorem lookupRuleType_isSome {rule : RewriteRule} {name : String} {type : TypeExpr}
    (declared : rule.typeContext.lookup name = some type) :
    (GeneralPremise.lookupRuleType? rule name).isSome = true := by
  have read := congrFun (lookupRuleType_eq rule) name
  rw [read, context_ofList_lookup, declared]
  rfl

private theorem constructor_filter_unique (declarations : List GrammarRule) (rule : GrammarRule)
    (unique : (declarations.map GrammarRule.label).Nodup) (declared : rule ∈ declarations) :
    declarations.filter (fun candidate => candidate.label == rule.label) = [rule] := by
  induction declarations with
  | nil => cases declared
  | cons head rest inductionHypothesis =>
    have names := List.nodup_cons.mp (by simpa only [List.map_cons] using unique)
    rcases List.mem_cons.mp declared with rfl | later
    · have remaining : rest.filter (fun candidate => candidate.label == rule.label) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro candidate member accepted
        have same := beq_iff_eq.mp accepted
        exact names.1 (same ▸ List.mem_map_of_mem member)
      simp [remaining]
    · have distinct : (head.label == rule.label) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro same
        exact names.1 (same.symm ▸ List.mem_map_of_mem later)
      simp only [List.filter_cons, distinct, Bool.false_eq_true, if_false]
      exact inductionHypothesis names.2 later

/-- The actual admission synthesizer recovers the sort of any typed
first-order schema in the authored context. -/
theorem sourceType_of_typed_firstOrder {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}
    {rule : RewriteRule} {schema : Pattern} {type : TypeExpr}
    (valid : (environment language provider).language.validate = []) (shape : FirstOrder schema)
    (typed : HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext)
      [] schema type) :
    GeneralPremise.sourceType? (environment language provider).language rule schema = some type := by
  cases shape with
  | metavariable name =>
    cases typed with
    | fvar found =>
      simpa only [GeneralPremise.sourceType?, congrFun (lookupRuleType_eq rule) name] using found
  | constructor label arguments _ =>
    cases typed with
    | constructor declared _ _ =>
      rw [GeneralPremise.sourceType?, constructor_filter_unique _ _
        (LanguageDef.constructorLabels_nodup_of_validate_eq_nil _ valid) declared]

open private resolveFreshVarName from Mettapedia.OSLF.MeTTaIL.Engine

theorem lookup_eq_none_of_absent {bindings : Bindings} {name : String}
    (absent : name ∉ bindings.map Prod.fst) : bindings.lookup name = none := by
  unfold Bindings.lookup
  rw [List.find?_eq_none.mpr]
  · rfl
  · intro entry member hit
    exact absent (List.mem_map.mpr ⟨entry, member, by simpa using hit⟩)

variable {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}

theorem environment_provider (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot) :
    (environment language provider).provider = provider := rfl

/-- The rule the canonical engine runs at a position of the executed language. -/
theorem FirstOrderProfileFacts.authored (profile : FirstOrderProfileFacts language provider) {index : Nat}
    {rule : RewriteRule} (declared : (environment language provider).language.rewrites[index]? = some rule) :
    ∃ authored, language.rewrites[index]? = some authored ∧ ruleCore authored = ruleCore rule := by
  have mapped := congrArg (fun rules => rules[index]?) profile.sameRules
  simp only [List.getElem?_map, declared, Option.map_some] at mapped
  cases found : language.rewrites[index]? with
  | none => simp [found] at mapped
  | some authored =>
    simp only [found, Option.map_some, Option.some.injEq] at mapped
    exact ⟨authored, rfl, mapped.symm⟩

theorem FirstOrderProfile.authored (profile : FirstOrderProfile language provider) {index : Nat}
    {rule : RewriteRule} (declared : (environment language provider).language.rewrites[index]? = some rule) :
    ∃ authored, language.rewrites[index]? = some authored ∧ ruleCore authored = ruleCore rule :=
  profile.toFirstOrderProfileFacts.authored declared

mutual
 theorem firing_toCanonical (profile : FirstOrderProfile language provider) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv provider) {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List GeneralPremise.Event}
    (firing : GeneralPremise.RootFiring (environment language provider) bound type source index trace
      captured completed history target) :
    ∃ fuel, StepAt (engineBasePremises relEnv) language fuel source target :=
  match firing with
  | .fire (rule := rule) (spec := spec) declared specified _ _ traced capturedTyped premises reduct _ => by
    have row := profile.rows declared
    have specSame : spec = GeneralRuleBindingInference.inferredSpec rule :=
      Option.some.inj (specified.symm.trans row.specified)
    have congruent := row.premises
    have completedTyped := premisesHold_typed premises congruent capturedTyped
    have roots : GeneralPremise.RootValues bound.length completed :=
      completedTyped.rootValues (by
        show GeneralPremise.checkZeroDependencies spec = true
        rw [specSame]; exact GeneralFirstOrderProjection.inferred_zero rule)
    have extension : GeneralScopedMatch.Extends captured completed :=
      fun name value found => premises.extension name value found
    have declaredNames : ∀ name value, lookup completed name = some value →
        (GeneralPremise.lookupRuleType? rule name).isSome = true := by
      intro name value found
      obtain ⟨_, _, _, declared, _⟩ := completedTyped.1 name value
        (ConditionalEquationExecution.lookup_assignment_member completed name value found)
      exact lookupRuleType_isSome declared
    have matching : GeneralScopedMatch.Matches rule (GeneralRuleBindingInference.inferredSpec rule)
        bound.length .left [] 0 [] rule.left source captured := specSame ▸ traced.matching
    have leftSame : applyBindings (ordinary completed) rule.left = source :=
      matching_reconstructs row.left matching extension roots
    have leftDefined : Defined (ordinary completed) rule.left.freeFvarNames := by
      intro name member
      obtain ⟨value, found⟩ := GeneralPremise.matching_bound_names matching name member
      exact ⟨value.body, by rw [ordinary_lookup, extension name value found]; rfl⟩
    obtain ⟨initialBindings, leftMatched, leftCompatible, leftUnique, leftNames⟩ :=
      match_instance (ordinary completed) row.left leftDefined
    rw [leftSame] at leftMatched
    have flow := row.flow
    simp only [GeneralPremise.rulePremisesAdmitted, Bool.and_eq_true] at flow
    obtain ⟨supported, rhsAvailable⟩ := flow
    rw [← specSame] at supported rhsAvailable
    obtain ⟨fuel, finalBindings, premisesAt, finalCompatible, _, finalNames⟩ :=
      premises_toCanonical profile relEnv reads premises congruent specSame (GeneralScopedMatch.Extends.refl _)
        roots declaredNames (GeneralPremise.matching_bound_names matching) supported leftCompatible
        leftUnique (fun name => leftNames name)
    have rhsRead : instantiateWith? (ScopedReflectiveExecution.binderOperation
        (environment language provider).reflection rule) rule (GeneralRuleBindingInference.inferredSpec rule)
        bound.length .right [] 0 completed rule.right = some target := specSame ▸ reduct
    have rhsSame : applyBindings (ordinary completed) rule.right = target :=
      instantiation_readout row.right roots rhsRead
    have rhsBound : ∀ name ∈ rule.right.freeFvarNames, name ∈ finalBindings.map Prod.fst := by
      intro name member
      exact (finalNames name).mpr
        (GeneralPremise.namesAvailable_sound _ _ rhsAvailable name member)
    have finalRhs : applyBindings finalBindings rule.right = target :=
      (compatible_readout row.right finalCompatible rhsBound).trans rhsSame
    obtain ⟨authored, authoredDeclared, core⟩ := profile.authored declared
    simp only [ruleCore, Prod.mk.injEq] at core
    obtain ⟨leftCore, rightCore, premisesCore⟩ := core
    have aligned : ruleDepthAligned authored = true := by
      simpa only [ruleDepthAligned, leftCore, rightCore] using row.aligned
    refine ⟨fuel + 1, .rule (initialBindings := initialBindings) (finalBindings := finalBindings)
      (List.mem_of_getElem? authoredDeclared) ?_ ?_ ?_⟩
    · simpa only [matchPatternForRule, matchPatternForRule_eq_syntactic_of_no_presentations
        (rfl : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile.empty.presentations = []),
        leftCore] using matchRel_complete leftMatched
    · simpa only [premisesCore] using premisesAt
    · simpa only [applyBindingsForRule, applyBindingsForRuleUsing_empty_eq_applyBindings _ _ aligned,
        rightCore] using finalRhs
 termination_by structural firing

 theorem premises_toCanonical (profile : FirstOrderProfile language provider) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv provider) {context : GeneralPremise.Context} {premises : List Premise} {initial final : Assignment}
    {events : List GeneralPremise.Event}
    (held : GeneralPremise.PremisesHold (environment language provider) context premises initial final events)
    (congruent : ∀ premise ∈ premises, SupportedPremise premise)
    (zero : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    {chosen : Assignment} (later : GeneralScopedMatch.Extends final chosen)
    (roots : GeneralPremise.RootValues context.bound.length chosen)
    (declaredNames : ∀ name value, lookup chosen name = some value →
      (GeneralPremise.lookupRuleType? context.rule name).isSome = true)
    {available : List String} (boundAvailable : GeneralPremise.BoundNames initial available)
    (supported : (GeneralPremise.premisesFlow (environment language provider).language
      (environment language provider).provider context.rule context.spec available premises).supported = true)
    {bindings : Bindings} (compatible : Compatible (ordinary chosen) bindings)
    (unique : (bindings.map Prod.fst).Nodup)
    (names : ∀ name, name ∈ bindings.map Prod.fst ↔ name ∈ available) :
    ∃ fuel result, PremisesAt (engineBasePremises relEnv) language fuel bindings premises result ∧
      Compatible (ordinary chosen) result ∧ (result.map Prod.fst).Nodup ∧
      ∀ name, name ∈ result.map Prod.fst ↔ name ∈ (GeneralPremise.premisesFlow
        (environment language provider).language (environment language provider).provider context.rule context.spec
        available premises).available :=
  match held with
  | .nil => ⟨0, bindings, .nil bindings, compatible, unique, names⟩
  | .cons (premise := premise) (premises := rest) head tail => by
    simp only [GeneralPremise.premisesFlow, Bool.and_eq_true] at supported
    obtain ⟨headSupported, tailSupported⟩ := supported
    have middleLater : GeneralScopedMatch.Extends _ chosen :=
      fun name value found => later name value (tail.extension name value found)
    obtain ⟨headFuel, middle, headAt, middleCompatible, middleUnique, middleNames, middleBound⟩ :=
      premise_toCanonical profile relEnv reads head (congruent premise (by simp)) zero middleLater roots
        declaredNames boundAvailable headSupported compatible unique names
    obtain ⟨tailFuel, result, tailAt, resultCompatible, resultUnique, resultNames⟩ :=
      premises_toCanonical profile relEnv reads tail
        (fun other member => congruent other (List.mem_cons_of_mem _ member)) zero later roots
        declaredNames middleBound tailSupported middleCompatible middleUnique middleNames
    exact ⟨max headFuel tailFuel, result,
      .cons (headAt.mono_fuel (le_max_left _ _)) (tailAt.mono_fuel (le_max_right _ _)),
      resultCompatible, resultUnique, resultNames⟩
 termination_by structural held

 theorem premise_toCanonical (profile : FirstOrderProfile language provider) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv provider) {context : GeneralPremise.Context} {premise : Premise} {initial final : Assignment}
    {event : GeneralPremise.Event}
    (held : GeneralPremise.PremiseHolds (environment language provider) context premise initial final event)
    (congruent : SupportedPremise premise)
    (zero : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    {chosen : Assignment} (later : GeneralScopedMatch.Extends final chosen)
    (roots : GeneralPremise.RootValues context.bound.length chosen)
    (declaredNames : ∀ name value, lookup chosen name = some value →
      (GeneralPremise.lookupRuleType? context.rule name).isSome = true)
    {available : List String} (boundAvailable : GeneralPremise.BoundNames initial available)
    (supported : (GeneralPremise.premiseFlow (environment language provider).language
      (environment language provider).provider context.rule context.spec available premise).supported = true)
    {bindings : Bindings} (compatible : Compatible (ordinary chosen) bindings)
    (unique : (bindings.map Prod.fst).Nodup)
    (names : ∀ name, name ∈ bindings.map Prod.fst ↔ name ∈ available) :
    ∃ fuel result, PremiseAt (engineBasePremises relEnv) language fuel bindings premise result ∧
      Compatible (ordinary chosen) result ∧ (result.map Prod.fst).Nodup ∧
      (∀ name, name ∈ result.map Prod.fst ↔ name ∈ (GeneralPremise.premiseFlow
        (environment language provider).language (environment language provider).provider context.rule context.spec
        available premise).available) ∧
      GeneralPremise.BoundNames final (GeneralPremise.premiseFlow (environment language provider).language
        (environment language provider).provider context.rule context.spec available premise).available :=
  match held with
  | .query (relation := relation) (arguments := arguments) traced => by
    rcases congruent with ⟨_, _, same, _, _⟩ | ⟨_, same, _⟩ | ⟨_, _, same, _, shapes⟩
    · cases same
    · cases same
    injection same with sameRelation sameArguments
    subst sameRelation sameArguments
    match traced with
    | .row (row := row) (signature := signature) selected signatureFound rowTyped argumentsHeld _ =>
    have flowEq : GeneralPremise.premiseFlow (environment language provider).language
        (environment language provider).provider context.rule context.spec available
        (.relationQuery relation arguments) =
          ⟨(GeneralPremise.queryOutputNames arguments signature.modes ++ available).eraseDups,
            GeneralPremise.namesAvailable available (GeneralPremise.queryInputNames arguments signature.modes) &&
              GeneralPremise.schemaValuesChecked (environment language provider).language context.rule []
                arguments signature.argumentTypes⟩ := by
      simp only [GeneralPremise.premiseFlow, signatureFound]
    rw [flowEq] at supported ⊢
    simp only [Bool.and_eq_true] at supported
    obtain ⟨inputsAvailable, _⟩ := supported
    obtain ⟨signatureMember, signatureRelation, _, modesLength⟩ :=
      GeneralPremise.signature?_readout _ _ _ _ signatureFound
    have lengths : arguments.length = signature.modes.length := modesLength.symm
    have initialLater : GeneralScopedMatch.Extends initial chosen :=
      fun name value found => later name value (argumentsHeld.readout.extension name value found)
    have readback : arguments.map (applyBindings (ordinary chosen)) = row.values :=
      tracedArguments_readout zero roots argumentsHeld shapes later
    have defined : Defined (ordinary chosen) (arguments.flatMap Pattern.freeFvarNames) := by
      intro name member
      obtain ⟨value, found⟩ : ∃ value, lookup chosen name = some value := by
        rcases query_names_cover lengths name member with input | output
        · obtain ⟨value, found⟩ := boundAvailable name
            (GeneralPremise.namesAvailable_sound _ _ inputsAvailable name input)
          exact ⟨value, initialLater name value found⟩
        · obtain ⟨value, found⟩ := tracedArguments_bound argumentsHeld name output
          exact ⟨value, later name value found⟩
      exact ⟨value.body, by rw [ordinary_lookup, found]; rfl⟩
    obtain ⟨extension, matched, extensionCompatible, _, extensionNames, covers⟩ :=
      relationArgs_instance (ordinary chosen) shapes defined compatible unique
    rw [readback] at matched
    obtain ⟨result, merged, resultCompatible, resultUnique, resultNames⟩ :=
      merge_compatible (ordinary chosen) bindings extension compatible extensionCompatible unique
    have tuple : row.values ∈ relEnv.tuples relation (arguments.map (applyBindings bindings)) := by
      rw [← signatureRelation]
      exact (reads signature signatureMember _ _).mpr
        ⟨row, List.mem_of_getElem? selected, rowTyped.1, rfl⟩
    refine ⟨0, result, .relationQuery
      (RelationQueryAdmission.premiseStepWithEnv_relationQuery_of_env_tuple tuple matched merged),
      resultCompatible, resultUnique, ?_, ?_⟩
    · intro name
      rw [resultNames name, names name, List.mem_eraseDups, List.mem_append]
      constructor
      · rintro (inAvailable | inExtension)
        · exact Or.inr inAvailable
        · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp inExtension
          rcases query_names_cover lengths _ (extensionNames entry entryMember) with input | output
          · exact Or.inr (GeneralPremise.namesAvailable_sound _ _ inputsAvailable _ input)
          · exact Or.inl output
      · rintro (output | inAvailable)
        · rcases covers name (queryOutputNames_subset output) with inBindings | inExtension
          · exact Or.inl ((names name).mp inBindings)
          · exact Or.inr inExtension
        · exact Or.inl inAvailable
    · intro name member
      rw [List.mem_eraseDups, List.mem_append] at member
      rcases member with output | inAvailable
      · exact tracedArguments_bound argumentsHeld name output
      · obtain ⟨value, found⟩ := boundAvailable name inAvailable
        exact ⟨value, argumentsHeld.readout.extension name value found⟩
  | .scopedStep _ _ _ _ => by
    rcases congruent with ⟨_, _, same, _, _⟩ | ⟨_, same, _⟩ | ⟨_, _, same, _, _⟩ <;> cases same
  | .quantified _ _ => by
    rcases congruent with ⟨_, _, same, _, _⟩ | ⟨_, same, _⟩ | ⟨_, _, same, _, _⟩ <;> cases same
  | .freshness (condition := condition) (atom := atom) (subject := subject) found fresh => by
    rcases congruent with ⟨_, _, same, _, _⟩ | ⟨condition', same, termShape⟩ | ⟨_, _, same, _, _⟩
    · cases same
    rotate_left
    · cases same
    cases same
    simp only [GeneralPremise.premiseFlow, Bool.and_eq_true] at supported
    obtain ⟨⟨nameAllowed, termAvailable⟩, _⟩ := supported
    obtain ⟨named, subjectRead⟩ : GeneralPremise.freshnessName? context.bound.length initial
          condition.varName = some atom ∧
        instantiateAt? context.rule context.spec context.bound.length
          (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial condition.term =
            some subject := by
      unfold GeneralPremise.freshnessSubject? at found
      cases nameRead : GeneralPremise.freshnessName? context.bound.length initial condition.varName with
      | none => simp [nameRead] at found
      | some foundAtom =>
        cases termRead : instantiateAt? context.rule context.spec context.bound.length
            (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial condition.term with
        | none => simp [nameRead, termRead] at found
        | some foundSubject =>
          simp only [nameRead, termRead, Option.bind_eq_bind, Option.bind_some, Option.some.injEq,
            Prod.mk.injEq] at found
          obtain ⟨rfl, rfl⟩ := found
          exact ⟨rfl, rfl⟩
    have subjectRead' : instantiateWith? Substitution.instantiateBVar context.rule
        (GeneralRuleBindingInference.inferredSpec context.rule) context.bound.length
        (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial condition.term =
          some subject := by
      rw [← zero]; exact subjectRead
    have subjectSame : applyBindings (ordinary chosen) condition.term = subject :=
      readout_chosen termShape later roots subjectRead'
    have termBound : ∀ name ∈ condition.term.freeFvarNames, name ∈ bindings.map Prod.fst :=
      fun name member => (names name).mpr (GeneralPremise.namesAvailable_sound _ _ termAvailable name member)
    have canonicalSubject : applyBindings bindings condition.term = subject :=
      (compatible_readout termShape compatible termBound).trans subjectSame
    have resolved : resolveFreshVarName bindings condition.varName = some atom := by
      unfold GeneralPremise.freshnessName? at named
      unfold resolveFreshVarName
      cases foundInitial : lookup initial condition.varName with
      | none =>
        rw [foundInitial] at named
        cases named
        have notAvailable : condition.varName ∉ available := fun member => by
          obtain ⟨value, found⟩ := boundAvailable _ member
          rw [found] at foundInitial
          cases foundInitial
        rw [lookup_eq_none_of_absent (fun member => notAvailable ((names _).mp member))]
      | some value =>
        simp only [foundInitial] at named
        rw [root_value_readout (roots_of_extends later roots _ value foundInitial)] at named
        have body : value.body = .fvar atom := by
          revert named
          cases value.body <;> simp
        by_cases member : condition.varName ∈ available
        · rw [compatible_lookup compatible ((names _).mpr member), ordinary_lookup,
            later _ _ foundInitial, Option.map_some, body]
        · have literal : (GeneralPremise.lookupRuleType? context.rule condition.varName).isNone = true := by
            simp only [Bool.or_eq_true, List.contains_iff_mem] at nameAllowed
            exact nameAllowed.resolve_left member
          have declared := declaredNames _ _ (later _ _ foundInitial)
          simp only [Option.isNone_iff_eq_none] at literal
          simp [literal] at declared
    have holds : bindings ∈ engineBasePremises relEnv language bindings (.freshness condition) := by
      show bindings ∈ Engine.premiseStepWithEnv relEnv language bindings (.freshness condition)
      simp only [Engine.premiseStepWithEnv, resolved, canonicalSubject]
      rw [if_pos (show Substitution.checkFreshness ⟨atom, subject⟩ = true from
        (GeneralPremise.syntactic_freshness_iff atom subject).mpr fresh)]
      exact List.mem_singleton_self _
    exact ⟨0, bindings, .freshness holds, compatible, unique, names, boundAvailable⟩
  | .step (source := source) (target := target) (actualSource := actualSource)
      (actualTarget := actualTarget) _ instantiated child targetMatched _ => by
    rcases congruent with ⟨_, _, same, sourceShape, targetShape⟩ | ⟨_, same, _⟩ | ⟨_, _, same, _, _⟩
    rotate_left
    · cases same
    · cases same
    cases same
    simp only [GeneralPremise.premiseFlow, Bool.and_eq_true] at supported ⊢
    obtain ⟨sourceAvailable, _⟩ := supported
    have matching := targetMatched.matching
    have initialLater : GeneralScopedMatch.Extends initial chosen :=
      fun name value found => later name value (matching.extends name value found)
    have sourceRead : instantiateWith? Substitution.instantiateBVar context.rule
        (GeneralRuleBindingInference.inferredSpec context.rule) context.bound.length
        (context.site 0) [] 0 initial source = some actualSource := by
      rw [← zero]; exact instantiated
    have sourceSame : applyBindings (ordinary chosen) source = actualSource :=
      readout_chosen sourceShape initialLater roots sourceRead
    have sourceBound : ∀ name ∈ source.freeFvarNames, name ∈ bindings.map Prod.fst := fun name member =>
      (names name).mpr (GeneralPremise.namesAvailable_sound _ _ sourceAvailable name member)
    have canonicalSource : applyBindings bindings source = actualSource :=
      (compatible_readout sourceShape compatible sourceBound).trans sourceSame
    obtain ⟨childFuel, childStep⟩ := firing_toCanonical profile relEnv reads child
    have targetSame : applyBindings (ordinary chosen) target = actualTarget := by
      rw [zero] at matching
      exact matching_reconstructs targetShape matching later roots
    have targetDefined : Defined (ordinary chosen) target.freeFvarNames := by
      intro name member
      obtain ⟨value, found⟩ := GeneralPremise.matching_bound_names matching name member
      exact ⟨value.body, by rw [ordinary_lookup, later name value found]; rfl⟩
    obtain ⟨extension, targetMatchedRaw, extensionCompatible, _, extensionNames⟩ :=
      match_instance (ordinary chosen) targetShape targetDefined
    rw [targetSame] at targetMatchedRaw
    obtain ⟨result, merged, resultCompatible, resultUnique, resultNames⟩ :=
      merge_compatible (ordinary chosen) bindings extension compatible extensionCompatible unique
    refine ⟨childFuel, result, .congruence (by rw [canonicalSource]; exact childStep)
      (matchRel_complete targetMatchedRaw) merged, resultCompatible, resultUnique, ?_, ?_⟩
    · intro name
      rw [resultNames name, names name, extensionNames name, List.mem_eraseDups, List.mem_append]
      exact or_comm
    · intro name member
      simp only [List.mem_eraseDups, List.mem_append] at member
      rcases member with fromTarget | earlier
      · exact GeneralPremise.matching_bound_names targetMatched.matching name fromTarget
      · obtain ⟨value, found⟩ := boundAvailable name earlier
        exact ⟨value, targetMatched.matching.extends name value found⟩
 termination_by structural held
end

/-! ## From the canonical step to the general firing -/

open Mettapedia.GSLT.LanguageDef.WellSorted

/-- In a valid language an application has one sort, whatever its context. -/
theorem apply_types_agree {language : LanguageDef} (valid : language.validate = [])
    {firstFree secondFree : FreeTypeContext} {firstBound secondBound : List TypeExpr}
    {label : String} {firstArguments secondArguments : List Pattern}
    {firstType secondType : TypeExpr}
    (first : HasType language firstFree firstBound (.apply label firstArguments) firstType)
    (second : HasType language secondFree secondBound (.apply label secondArguments) secondType) :
    firstType = secondType := by
  obtain ⟨firstRule, firstMember, firstLabel, firstSort⟩ := declared_constructor_of_hasType_apply first
  obtain ⟨secondRule, secondMember, secondLabel, secondSort⟩ :=
    declared_constructor_of_hasType_apply second
  have same : firstRule = secondRule :=
    List.inj_on_of_nodup_map (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid)
      firstMember secondMember (firstLabel.trans secondLabel.symm)
  rw [firstSort, secondSort, same]

theorem FirstOrderProfileFacts.executed (profile : FirstOrderProfileFacts language provider) {index : Nat}
    {authored : RewriteRule} (declared : language.rewrites[index]? = some authored) :
    ∃ rule, (environment language provider).language.rewrites[index]? = some rule ∧
      ruleCore rule = ruleCore authored := by
  have mapped := congrArg (fun rules => rules[index]?) profile.sameRules
  simp only [List.getElem?_map, declared, Option.map_some] at mapped
  cases found : (environment language provider).language.rewrites[index]? with
  | none => simp [found] at mapped
  | some rule =>
    simp only [found, Option.map_some, Option.some.injEq] at mapped
    exact ⟨rule, rfl, mapped⟩

theorem FirstOrderProfile.executed (profile : FirstOrderProfile language provider) {index : Nat}
    {authored : RewriteRule} (declared : language.rewrites[index]? = some authored) :
    ∃ rule, (environment language provider).language.rewrites[index]? = some rule ∧
      ruleCore rule = ruleCore authored :=
  profile.toFirstOrderProfileFacts.executed declared

theorem sitePattern_congruence_source {rule : RewriteRule} {index : Nat} {source target : Pattern}
    (declared : rule.premises[index]? = some (.congruence source target)) :
    sitePattern? rule (.premise index 0 0) = some source := by
  simp [sitePattern?, declared, quantifiedBody?]

theorem sitePattern_congruence_target {rule : RewriteRule} {index : Nat} {source target : Pattern}
    (declared : rule.premises[index]? = some (.congruence source target)) :
    sitePattern? rule (.premise index 0 1) = some target := by
  simp [sitePattern?, declared, quantifiedBody?]

/-- **Canonical to general.** Every canonical step from a well-sorted source of a
congruence-profile language is a general root firing at the source's sort. -/
theorem step_toGeneral (profile : FirstOrderProfile language provider) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv provider) :
    ∀ (fuel : Nat) {source target : Pattern},
      StepAt (engineBasePremises relEnv) language fuel source target →
      ∀ {bound : List TypeExpr} {type : TypeExpr},
        OpenPatternWellSorted (environment language provider).language (environment language provider).free bound type
          source →
        ∃ index trace captured completed history,
          GeneralPremise.RootFiring (environment language provider) bound type source index trace captured
            completed history target := by
  intro fuel
  induction fuel with
  | zero => intro _ _ evidence; cases evidence
  | succ fuel childStep =>
    intro source target evidence bound type sourceTyped
    cases evidence with
    | rule member matched premises reduct =>
    rename_i authored initial final
    obtain ⟨index, authoredDeclared⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨rule, declared, core⟩ := profile.executed authoredDeclared
    have row := profile.rows declared
    simp only [ruleCore, Prod.mk.injEq] at core
    obtain ⟨leftCore, rightCore, premisesCore⟩ := core
    have aligned : ruleDepthAligned authored = true := by
      simpa only [ruleDepthAligned, leftCore, rightCore] using row.aligned
    have leftMatched : MatchRel rule.left source initial := by
      have read := matched
      simp only [matchPatternForRule, matchPatternForRule_eq_syntactic_of_no_presentations
        (rfl : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile.empty.presentations = []),
        ← leftCore] at read
      exact matchPattern_sound read
    rw [← premisesCore] at premises
    have rhsSame : applyBindings final rule.right = target := by
      simpa only [applyBindingsForRule, applyBindingsForRuleUsing_empty_eq_applyBindings _ _ aligned,
        rightCore] using reduct
    have leftSource : applyBindings initial rule.left = source :=
      matchRel_correct leftMatched row.left.isMatchCorrect
    obtain ⟨label, arguments, headed⟩ := row.headed
    obtain ⟨ruleType, leftTyped, rightTyped⟩ := row.typed
    have sameType : ruleType = type := by
      have sourceHas := sourceTyped.1
      rw [← leftSource, headed] at sourceHas
      rw [headed] at leftTyped
      simp only [applyBindings] at sourceHas
      exact apply_types_agree profile.valid leftTyped sourceHas
    subst sameType
    have initialTyped : CapturesTyped (environment language provider).language (environment language provider).free bound
        rule.typeContext initial :=
      matching_captures_typed profile.valid row.left leftMatched leftTyped sourceTyped.1
        sourceTyped.2.1 sourceTyped.2.2.1
    have leftDefined : Defined initial rule.left.freeFvarNames := raw_matching_defined row.left leftMatched
    obtain ⟨captured, leftMatches, leftCompatible⟩ := scoped_instance (initial := [])
      row.left (NameCoherent.left rule) leftDefined initialTyped row.unique
      (fun _ member => by cases member)
    rw [leftSource] at leftMatches
    have flow := row.flow
    simp only [GeneralPremise.rulePremisesAdmitted, Bool.and_eq_true] at flow
    obtain ⟨supported, rhsAvailable⟩ := flow
    -- the premises, left to right
    have inner : ∀ (pending : List Premise) (position : Nat) {current : Bindings}
        {assignment : Assignment} {available : List String},
        (∀ offset premise, pending[offset]? = some premise →
          rule.premises[position + offset]? = some premise) →
        PremisesAt (engineBasePremises relEnv) language fuel current pending final →
        CapturesTyped (environment language provider).language (environment language provider).free bound
          rule.typeContext current →
        ScopedCompatible bound.length current assignment →
        GeneralPremise.BoundNames assignment available →
        (∀ name ∈ current.map Prod.fst, name ∈ available) →
        (GeneralPremise.premisesFlow (environment language provider).language (environment language provider).provider rule
          (GeneralRuleBindingInference.inferredSpec rule) available pending).supported = true →
        ∃ completed events,
          GeneralPremise.PremisesHold (environment language provider)
            ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩
            pending assignment completed events ∧
          ScopedCompatible bound.length final completed ∧
          CapturesTyped (environment language provider).language (environment language provider).free bound
            rule.typeContext final ∧
          GeneralPremise.BoundNames completed (GeneralPremise.premisesFlow (environment language provider).language
            (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule)
            available pending).available := by
      intro pending
      induction pending with
      | nil =>
        intro position current assignment available _ chain currentTyped compatible bound' _ _
        cases chain
        exact ⟨assignment, [], .nil, compatible, currentTyped, bound'⟩
      | cons premise pending pendingHypothesis =>
        intro position current assignment available located chain currentTyped compatible bound'
          currentNames supported
        have here : rule.premises[position]? = some premise := by
          simpa using located 0 premise rfl
        have locatedRest : ∀ offset later, pending[offset]? = some later →
            rule.premises[position + 1 + offset]? = some later := fun offset later selected => by
          simpa [Nat.add_assoc, Nat.add_comm 1 offset] using located (offset + 1) later selected
        rcases row.premises premise (List.mem_of_getElem? here) with
          ⟨sourceSchema, targetSchema, same, sourceShape, targetShape⟩ | ⟨condition, same, termShape⟩ |
            ⟨relation, arguments, same, distinct, shapes⟩
        rotate_left
        · subst same
          cases chain with
          | cons first rest =>
          rename_i middle
          cases first with
          | freshness member =>
          have member' : middle ∈ Engine.premiseStepWithEnv relEnv language current
              (.freshness condition) := member
          have sameBindings := Engine.premiseStepWithEnv_freshness_mem member'
          subst sameBindings
          obtain ⟨atom, resolvedMatch, freshCheck⟩ := Engine.premiseStepWithEnv_freshness_check member'
          simp only [GeneralPremise.premisesFlow, Bool.and_eq_true] at supported
          obtain ⟨headSupported, tailSupported⟩ := supported
          simp only [GeneralPremise.premiseFlow, Bool.and_eq_true] at headSupported
          obtain ⟨⟨_, termAvailable⟩, _⟩ := headSupported
          have termBound : GeneralPremise.BoundNames assignment condition.term.freeFvarNames :=
            fun name member => bound' name (GeneralPremise.namesAvailable_sound _ _ termAvailable name member)
          have termDefined : Defined middle condition.term.freeFvarNames :=
            compatible_defined compatible termBound
          have roots : GeneralPremise.RootValues bound.length assignment :=
            compatible.rootValues currentTyped
          obtain ⟨subject, subjectRead⟩ := instantiation_total
            (operation := Substitution.instantiateBVar) termShape
            (nameCoherent_premise (sitePattern_freshness here)) termBound roots
            (dependencies_of_typed row.unique termDefined currentTyped)
          have subjectSame : applyBindings middle condition.term = subject :=
            (compatible_apply_eq compatible termShape termBound).symm.trans
              (instantiation_readout termShape roots subjectRead)
          have named : GeneralPremise.freshnessName? bound.length assignment condition.varName =
              some atom := by
            unfold GeneralPremise.freshnessName?
            cases foundAssignment : lookup assignment condition.varName with
            | none =>
              have absent : middle.lookup condition.varName = none := by
                cases present : middle.lookup condition.varName with
                | none => rfl
                | some value =>
                  exfalso
                  have inMiddle : condition.varName ∈ middle.map Prod.fst :=
                    List.mem_map.mpr ⟨(condition.varName, value), raw_lookup_member present, rfl⟩
                  obtain ⟨_, found⟩ := bound' _ (currentNames _ inMiddle)
                  rw [found] at foundAssignment
                  cases foundAssignment
              rw [absent] at resolvedMatch
              simpa using resolvedMatch
            | some value =>
              obtain ⟨_, _, read⟩ := compatible (condition.varName, value)
                (ConditionalEquationExecution.lookup_assignment_member assignment _ value foundAssignment)
              rw [read] at resolvedMatch
              dsimp only
              rw [root_value_readout (roots _ _ foundAssignment)]
              revert resolvedMatch
              cases value.body <;> simp
          have found : GeneralPremise.freshnessSubject? rule (GeneralRuleBindingInference.inferredSpec rule)
              bound position 0 assignment condition = some (atom, subject) := by
            have subjectAt : instantiateAt? rule (GeneralRuleBindingInference.inferredSpec rule) bound.length
                (.premise position 0 0) [] 0 assignment condition.term = some subject := subjectRead
            simp only [GeneralPremise.freshnessSubject?, named, subjectAt, Option.bind_eq_bind,
              Option.bind_some]
          have fresh : GeneralPremise.SyntacticallyFresh atom subject := by
            rw [← subjectSame]
            exact (GeneralPremise.syntactic_freshness_iff _ _).mp freshCheck
          obtain ⟨completed, events, held, finalCompatible, finalTyped, finalBound⟩ :=
            pendingHypothesis (position + 1) locatedRest rest currentTyped compatible bound' currentNames
              tailSupported
          exact ⟨completed, _ :: events, .cons (.freshness found fresh) held, finalCompatible, finalTyped,
            finalBound⟩
        · subst same
          cases chain with
          | cons first rest =>
          rename_i middle
          cases first with
          | relationQuery member =>
          have member' : middle ∈ Engine.relationQueryStep relEnv language current relation arguments := member
          obtain ⟨tuple, extension, provided, matched, merged⟩ :=
            ConditionalEquationExecution.relationQueryStep_readout relEnv language current middle relation
              arguments member'
          rw [builtinRelationTuples_eq_nil distinct, List.nil_append] at provided
          simp only [GeneralPremise.premisesFlow, Bool.and_eq_true] at supported
          obtain ⟨headSupported, tailSupported⟩ := supported
          cases signatureFound : GeneralPremise.signature? (environment language provider).provider relation
              arguments.length with
          | none => simp [GeneralPremise.premiseFlow, signatureFound] at headSupported
          | some signature =>
          have flowEq : GeneralPremise.premiseFlow (environment language provider).language
              (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule) available
              (.relationQuery relation arguments) =
                ⟨(GeneralPremise.queryOutputNames arguments signature.modes ++ available).eraseDups,
                  GeneralPremise.namesAvailable available
                      (GeneralPremise.queryInputNames arguments signature.modes) &&
                    GeneralPremise.schemaValuesChecked (environment language provider).language rule []
                      arguments signature.argumentTypes⟩ := by
            simp only [GeneralPremise.premiseFlow, signatureFound]
          rw [flowEq] at headSupported tailSupported
          simp only [Bool.and_eq_true] at headSupported
          obtain ⟨inputsAvailable, schemasChecked⟩ := headSupported
          obtain ⟨signatureMember, signatureRelation, _, modesLength⟩ :=
            GeneralPremise.signature?_readout _ _ _ _ signatureFound
          have lengths : arguments.length = signature.modes.length := modesLength.symm
          rw [← signatureRelation] at provided
          obtain ⟨providerRow, rowMember, rowRelation, rowValues⟩ := (reads signature signatureMember _ _).mp provided
          subst rowValues
          obtain ⟨readback, middleDefined⟩ := relationArgs_sound shapes matched
            (fun _ _ found => mergeBindings_subsumed_left merged found)
            (fun _ _ found => mergeBindings_subsumed_right merged found)
          obtain ⟨closedSignature, closedFound, closedTyped⟩ :=
            GeneralPremise.checkProviderClosed_row _ _ _ profile.providerClosed providerRow rowMember
          have sameSignature : closedSignature = signature := by
            rw [rowRelation, signatureRelation, ← readback, List.length_map, signatureFound] at closedFound
            exact (Option.some.inj closedFound).symm
          subst sameSignature
          have rowTyped := GeneralPremise.closed_row_in_bound closedTyped bound
          have schemasTyped := GeneralPremise.schemaValuesChecked_sound schemasChecked
          rw [lookupRuleType_eq] at schemasTyped
          have extensionTyped := relationArgs_typed profile.valid shapes matched schemasTyped rowTyped.2
          have middleTyped := capturesTyped_merge currentTyped extensionTyped merged
          have lifted : ScopedCompatible bound.length middle assignment :=
            compatible_lift compatible (fun _ _ read => merge_lookup_left merged read)
          obtain ⟨next, origins, argumentsHeld, nextCompatible, outputsBound, nextExtends⟩ :=
            tracedArguments_construct (ruleIndex := index) row.unique here middleTyped arguments
              closedSignature.modes 0 (fun _ _ selected => by simpa using selected) shapes lengths middleDefined
              (fun name member => bound' name (GeneralPremise.namesAvailable_sound _ _ inputsAvailable name member))
              lifted
          rw [readback] at argumentsHeld
          obtain ⟨rowIndex, selected⟩ := List.mem_iff_getElem?.mp rowMember
          have traced : GeneralPremise.TracedQuery (environment language provider)
              ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, position, 0⟩ relation arguments
              assignment rowIndex next origins :=
            .row selected signatureFound rowTyped argumentsHeld (nextCompatible.typed middleTyped row.unique)
          have nextBound : GeneralPremise.BoundNames next
              (GeneralPremise.queryOutputNames arguments closedSignature.modes ++ available).eraseDups := by
            intro name member
            rw [List.mem_eraseDups, List.mem_append] at member
            rcases member with output | inAvailable
            · exact outputsBound name output
            · obtain ⟨value, found⟩ := bound' name inAvailable
              exact ⟨value, nextExtends name value found⟩
          have middleNames : ∀ name ∈ middle.map Prod.fst,
              name ∈ (GeneralPremise.queryOutputNames arguments closedSignature.modes ++ available).eraseDups := by
            intro name member
            obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
            rw [List.mem_eraseDups, List.mem_append]
            rcases List.mem_append.mp (merge_members merged entryMember) with earlier | later
            · exact Or.inr (currentNames _ (List.mem_map_of_mem earlier))
            · rcases query_names_cover lengths _ (relationArgs_names shapes matched entry later) with
                input | output
              · exact Or.inr (GeneralPremise.namesAvailable_sound _ _ inputsAvailable _ input)
              · exact Or.inl output
          obtain ⟨completed, events, held, finalCompatible, finalTyped, finalBound⟩ :=
            pendingHypothesis (position + 1) locatedRest rest middleTyped nextCompatible nextBound middleNames
              tailSupported
          refine ⟨completed, _ :: events, .cons (.query traced) held, finalCompatible, finalTyped, ?_⟩
          simp only [GeneralPremise.premisesFlow, flowEq]
          exact finalBound
        subst same
        cases chain with
        | cons first rest =>
        rename_i middle
        cases first with
        | congruence recursive extensionMember merged =>
        rename_i extension candidate
        simp only [GeneralPremise.premisesFlow, Bool.and_eq_true] at supported
        obtain ⟨headSupported, tailSupported⟩ := supported
        simp only [GeneralPremise.premiseFlow, Bool.and_eq_true] at headSupported
        obtain ⟨sourceAvailable, sortChecked⟩ := headSupported
        cases sortFound : GeneralPremise.sourceType? (environment language provider).language rule sourceSchema with
        | none => simp [sortFound] at sortChecked
        | some childType =>
        simp only [sortFound] at sortChecked
        have schemasTyped := GeneralPremise.schemaValuesChecked_sound sortChecked
        rw [lookupRuleType_eq] at schemasTyped
        obtain ⟨sourceSchemaTyped, targetSchemaTyped⟩ : HasType (environment language provider).language
            (FreeTypeContext.ofList rule.typeContext) [] sourceSchema childType ∧
            HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) []
              targetSchema childType := by
          cases schemasTyped with
          | cons first rest => cases rest with | cons second _ => exact ⟨first, second⟩
        have sourceBound : GeneralPremise.BoundNames assignment sourceSchema.freeFvarNames :=
          fun name member => bound' name (GeneralPremise.namesAvailable_sound _ _ sourceAvailable name member)
        have sourceDefined : Defined current sourceSchema.freeFvarNames := compatible_defined compatible sourceBound
        have roots : GeneralPremise.RootValues bound.length assignment :=
          compatible.rootValues currentTyped
        obtain ⟨actualSource, instantiated⟩ := instantiation_total
          (operation := Substitution.instantiateBVar) sourceShape
          (nameCoherent_premise (sitePattern_congruence_source here)) sourceBound roots
          (dependencies_of_typed row.unique sourceDefined currentTyped)
        have sourceRead : applyBindings (ordinary assignment) sourceSchema = actualSource :=
          instantiation_readout sourceShape roots instantiated
        have sourceSame : applyBindings current sourceSchema = actualSource :=
          (compatible_apply_eq compatible sourceShape sourceBound).symm.trans sourceRead
        have childTyped : OpenPatternWellSorted (environment language provider).language
            (environment language provider).free bound childType actualSource := by
          rw [← sourceSame]
          exact substituted_open sourceShape sourceSchemaTyped sourceDefined currentTyped
        rw [sourceSame] at recursive
        obtain ⟨childIndex, childTrace, childCaptured, childCompleted, childHistory, child⟩ :=
          childStep recursive childTyped
        have candidateTyped : OpenPatternWellSorted (environment language provider).language
            (environment language provider).free bound childType candidate := by
          cases child with
          | fire _ _ _ _ _ _ _ _ sorted => exact sorted
        have extensionMatched : MatchRel targetSchema candidate extension :=
          matchPattern_sound extensionMember
        have extensionTyped : CapturesTyped (environment language provider).language (environment language provider).free
            bound rule.typeContext extension :=
          matching_captures_typed profile.valid targetShape extensionMatched targetSchemaTyped
            candidateTyped.1 candidateTyped.2.1 candidateTyped.2.2.1
        have middleTyped := capturesTyped_merge currentTyped extensionTyped merged
        have lifted : ScopedCompatible bound.length middle assignment :=
          compatible_lift compatible (fun _ _ read => merge_lookup_left merged read)
        have targetDefined : Defined middle targetSchema.freeFvarNames := by
          intro name member
          obtain ⟨value, read⟩ := raw_matching_defined targetShape extensionMatched name member
          exact ⟨value, merge_lookup_right merged read⟩
        obtain ⟨next, targetMatches, nextCompatible⟩ := scoped_instance (initial := assignment)
          targetShape (nameCoherent_premise (sitePattern_congruence_target here)) targetDefined
          middleTyped row.unique lifted
        have targetSame : applyBindings middle targetSchema = candidate := by
          rw [apply_eq_of_preserved targetShape (raw_matching_defined targetShape extensionMatched)
            (fun _ _ read => merge_lookup_right merged read)]
          exact matchRel_correct extensionMatched targetShape.isMatchCorrect
        rw [targetSame] at targetMatches
        obtain ⟨targetTrace, traced⟩ := GeneralScopedMatchMachine.matches_trace targetMatches
        have nextTyped := nextCompatible.typed middleTyped row.unique
        have nextBound : GeneralPremise.BoundNames next
            (GeneralPremise.premiseFlow (environment language provider).language (environment language provider).provider
              rule (GeneralRuleBindingInference.inferredSpec rule) available
              (.congruence sourceSchema targetSchema)).available := by
          intro name member
          simp only [GeneralPremise.premiseFlow, List.mem_eraseDups, List.mem_append] at member
          rcases member with fromTarget | earlier
          · exact GeneralPremise.matching_bound_names targetMatches name fromTarget
          · obtain ⟨value, found⟩ := bound' name earlier
            exact ⟨value, targetMatches.extends name value found⟩
        have middleNames : ∀ name ∈ middle.map Prod.fst,
            name ∈ (GeneralPremise.premiseFlow (environment language provider).language
              (environment language provider).provider rule (GeneralRuleBindingInference.inferredSpec rule) available
              (.congruence sourceSchema targetSchema)).available := by
          intro name member
          obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
          simp only [GeneralPremise.premiseFlow, List.mem_eraseDups, List.mem_append]
          rcases List.mem_append.mp (merge_members merged entryMember) with earlier | later
          · exact Or.inr (currentNames _ (List.mem_map_of_mem earlier))
          · exact Or.inl (matchRel_names targetShape extensionMatched entry later)
        obtain ⟨completed, events, held, finalCompatible, finalTyped, finalBound⟩ :=
          pendingHypothesis (position + 1) locatedRest rest middleTyped nextCompatible nextBound
            middleNames tailSupported
        refine ⟨completed, _ :: events, .cons (.step sortFound instantiated child traced nextTyped) held,
          finalCompatible, finalTyped, finalBound⟩
    obtain ⟨completed, history, premisesHeld, completedCompatible, finalTyped, completedBound⟩ :=
      inner rule.premises 0 (fun offset premise selected => by simpa using selected) premises
        initialTyped leftCompatible (GeneralPremise.matching_bound_names leftMatches)
        (fun name member => by
          obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
          exact matchRel_names row.left leftMatched entry entryMember) supported
    have rhsBound : GeneralPremise.BoundNames completed rule.right.freeFvarNames := fun name member =>
      completedBound name (GeneralPremise.namesAvailable_sound _ _ rhsAvailable name member)
    have rhsDefined : Defined final rule.right.freeFvarNames := compatible_defined completedCompatible rhsBound
    have completedRoots : GeneralPremise.RootValues bound.length completed :=
      completedCompatible.rootValues finalTyped
    obtain ⟨reductTarget, reductRead⟩ := instantiation_total
      (operation := ScopedReflectiveExecution.binderOperation (environment language provider).reflection rule)
      row.right (NameCoherent.right rule) rhsBound completedRoots
      (dependencies_of_typed row.unique rhsDefined finalTyped)
    have reductSame : reductTarget = target := by
      rw [← instantiation_readout row.right completedRoots reductRead,
        compatible_apply_eq completedCompatible row.right rhsBound, rhsSame]
    subst reductSame
    obtain ⟨leftTrace, leftTraced⟩ := GeneralScopedMatchMachine.matches_trace leftMatches
    have targetTyped : OpenPatternWellSorted (environment language provider).language
        (environment language provider).free bound ruleType reductTarget := by
      rw [← rhsSame]
      exact substituted_open row.right rightTyped rhsDefined finalTyped
    exact ⟨index, leftTrace, captured, completed, history,
      .fire declared row.specified row.admitted sourceTyped leftTraced
        (leftCompatible.typed initialTyped row.unique) premisesHeld reductRead targetTyped⟩

/-! ## The two step relations agree -/

open MeTTaIL.GeneralTypedSites

/-- **Agreement with first-order premises.** For a language with the first-order
profile, the general step from a well-sorted source is the canonical step, in
every relation environment that reads the provider. -/
theorem FirstOrderProfile.general_step_iff_canonical (profile : FirstOrderProfile language provider)
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv provider) (bound : List TypeExpr) (type : TypeExpr) {source target : Pattern}
    (typed : OpenPatternWellSorted (rootPlan language provider).snapshot.language
      (rootPlan language provider).snapshot.free bound type source) :
    (GeneralOccurrenceSemantics.gslt (rootPlan language provider) bound type).Step source target ↔
      (TypeSynthesis.langGSLTUsing relEnv language).Step source target := by
  have equality : ∀ {first second : Pattern},
      (GeneralOccurrenceSemantics.gslt (rootPlan language provider) bound type).Equiv first second →
        first = second := fun {first _} equivalent =>
    GeneralOccurrenceFrontier.LocalEquationFree.equation_equivalence_is_equality
      (request := ⟨rootPlan language provider, bound, type, first⟩) profile.equations equivalent
  have canonical : (TypeSynthesis.langGSLTUsing relEnv language).Step source target ↔
      ∃ fuel, StepAt (engineBasePremises relEnv) language fuel source target :=
    TypeSynthesis.langSemanticReducesUsing_iff_langReducesUsing_of_equation_free relEnv
      profile.equationFree source target
  rw [canonical]
  constructor
  · rintro ⟨representative, receipt, before, fired, after⟩
    have sourceSame := equality before
    have targetSame := equality after
    subst representative
    rw [← targetSame]
    have site := rootOnly_site fired.1.2
    have firing : GeneralPremise.RootFiring (environment language provider) bound type source
        receipt.job.ordinal receipt.matcherTrace receipt.captured receipt.completed
        receipt.premiseHistory receipt.localTarget := by
      simpa only [site, SiteData.here, environment, GeneralPlanEnvironment.environmentWith_empty] using fired.2.1
    have same : receipt.target = receipt.localTarget := by
      simpa only [site, SiteData.here, DerivedContexts.OneHoleContext.fill] using fired.2.2.2.1
    rw [same]
    exact firing_toCanonical profile relEnv reads firing
  · rintro ⟨fuel, step⟩
    have sourceTyped : OpenPatternWellSorted (environment language provider).language
        (environment language provider).free bound type source :=
      (GeneralPlanEnvironment.typing_iff (rootPlan language provider) bound type source).mpr typed
    obtain ⟨index, trace, captured, completed, history, firing⟩ :=
      step_toGeneral profile relEnv reads fuel step sourceTyped
    obtain ⟨rule, declared⟩ : ∃ rule, (environment language provider).language.rewrites[index]? = some rule := by
      cases firing with
      | fire declared _ _ _ _ _ _ _ _ => exact ⟨_, declared⟩
    obtain ⟨declaration, selected, _⟩ : ∃ declaration,
        (rootPlan language provider).rules[index]? = some declaration ∧ declaration.rule = rule := by
      have row : ((rootPlan language provider).rules.map GeneralExecutionAdmission.RulePlan.rule)[index]? = some rule := declared
      simp only [List.getElem?_map, Option.map_eq_some_iff] at row
      exact row
    let job : GeneralRuleJobs.Job := ⟨index, declaration, SiteData.here bound type source⟩
    have jobValid : job.Valid (rootPlan language provider) bound type source :=
      ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, .here rfl sourceTyped.2.2.1 sourceTyped.1⟩
    let receipt : GeneralRuleJobs.Receipt := ⟨job, trace, captured, completed, history, target, target⟩
    refine ⟨source, receipt, .refl source, ⟨jobValid, firing, rfl, rfl, ?_⟩, .refl target⟩
    cases firing with
    | fire _ _ _ _ _ _ _ _ sorted => exact sorted

/-! ## A decidable profile -/

def checkSupportedPremise : Premise → Bool
  | .congruence source target => checkFirstOrder source && checkFirstOrder target
  | .freshness condition => checkFirstOrder condition.term
  | .relationQuery relation arguments => relation != "eq" && arguments.all checkFirstOrder
  | _ => false

theorem checkCongruencePremise_sound {premise : Premise}
    (checked : checkSupportedPremise premise = true) : SupportedPremise premise := by
  cases premise with
  | congruence source target =>
    simp only [checkSupportedPremise, Bool.and_eq_true] at checked
    exact Or.inl ⟨source, target, rfl, checkFirstOrder_sound checked.1, checkFirstOrder_sound checked.2⟩
  | freshness condition =>
    simp only [checkSupportedPremise] at checked
    exact Or.inr (Or.inl ⟨condition, rfl, checkFirstOrder_sound checked⟩)
  | relationQuery relation arguments =>
    simp only [checkSupportedPremise, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at checked
    exact Or.inr (Or.inr ⟨relation, arguments, rfl, checked.1,
      fun argument member => checkFirstOrder_sound (checked.2 argument member)⟩)
  | _ => simp [checkSupportedPremise] at checked

def checkHeaded : Pattern → Bool
  | .apply _ _ => true
  | _ => false

theorem checkHeaded_sound {pattern : Pattern} (checked : checkHeaded pattern = true) :
    ∃ label arguments, pattern = .apply label arguments := by
  cases pattern with
  | apply label arguments => exact ⟨label, arguments, rfl⟩
  | _ => simp [checkHeaded] at checked

def checkRuleTyped (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (rule : RewriteRule) : Bool :=
  match GeneralPremise.sourceType? (environment language provider).language rule rule.left with
  | some type =>
      checkHasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) []
          rule.left type &&
        checkHasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) []
          rule.right type
  | none => false

theorem checkRuleTyped_sound {rule : RewriteRule} (checked : checkRuleTyped language provider rule = true) :
    ∃ type, HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) []
        rule.left type ∧
      HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) []
        rule.right type := by
  unfold checkRuleTyped at checked
  split at checked
  · rename_i type _
    simp only [Bool.and_eq_true] at checked
    exact ⟨type, checkHasType_sound checked.1, checkHasType_sound checked.2⟩
  · cases checked

/-- A rule's synthesized root sort is retained only after both authored sides
pass the existing type checker at that same sort. -/
def checkedRuleSort? (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (rule : RewriteRule) : Option TypeExpr :=
  if checkRuleTyped language provider rule then
    GeneralPremise.sourceType? (environment language provider).language rule rule.left
  else none

theorem checkedRuleSort?_sound {rule : RewriteRule} {type : TypeExpr}
    (checked : checkedRuleSort? language provider rule = some type) :
    HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) []
        rule.left type ∧
      HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) []
        rule.right type := by
  unfold checkedRuleSort? at checked
  split at checked
  · rename_i accepted
    unfold checkRuleTyped at accepted
    rw [checked] at accepted
    simp only [Bool.and_eq_true] at accepted
    exact ⟨checkHasType_sound accepted.1, checkHasType_sound accepted.2⟩
  · cases checked

theorem checkedRuleSort?_complete {rule : RewriteRule} {type : TypeExpr}
    (valid : (environment language provider).language.validate = [])
    (left : FirstOrder rule.left) (right : FirstOrder rule.right)
    (leftTyped : HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext)
      [] rule.left type)
    (rightTyped : HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext)
      [] rule.right type) : checkedRuleSort? language provider rule = some type := by
  have found := sourceType_of_typed_firstOrder valid left leftTyped
  have leftChecked := checkHasType_complete_of_object leftTyped left.isObject
  have rightChecked := checkHasType_complete_of_object rightTyped right.isObject
  simp [checkedRuleSort?, checkRuleTyped, found, leftChecked, rightChecked]

theorem FirstOrderRowFacts.checked_sort {index : Nat} {rule : RewriteRule}
    (row : FirstOrderRowFacts language provider index rule)
    (valid : (environment language provider).language.validate = []) :
    ∃ type, checkedRuleSort? language provider rule = some type := by
  obtain ⟨type, leftTyped, rightTyped⟩ := row.typed
  exact ⟨type, checkedRuleSort?_complete valid row.left row.right leftTyped rightTyped⟩

/-- Invocation selection compares the checked authored sort with the caller
sort. It neither changes declaration indices nor reorders matching results. -/
def rootSortGuard (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (rule : RewriteRule) (type : TypeExpr) : Bool :=
  checkedRuleSort? language provider rule == some type

theorem rootSortGuard_sound {rule : RewriteRule} {type : TypeExpr}
    (checked : rootSortGuard language provider rule type = true) :
    HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) []
        rule.left type ∧
      HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) []
        rule.right type :=
  checkedRuleSort?_sound (beq_iff_eq.mp checked)

theorem rootSortGuard_iff {rule : RewriteRule} {type : TypeExpr}
    (valid : (environment language provider).language.validate = [])
    (left : FirstOrder rule.left) (right : FirstOrder rule.right) :
    rootSortGuard language provider rule type = true ↔
      HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) []
          rule.left type ∧
        HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext) []
          rule.right type :=
  ⟨rootSortGuard_sound, fun typed => beq_iff_eq.mpr
    (checkedRuleSort?_complete valid left right typed.1 typed.2)⟩

def guardedRootMatches (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (rule : RewriteRule) (type : TypeExpr) (source : Pattern) : List Bindings :=
  if rootSortGuard language provider rule type then matchPattern rule.left source else []

theorem guardedRootMatches_accepted {rule : RewriteRule} {type : TypeExpr} {source : Pattern}
    (accepted : rootSortGuard language provider rule type = true) :
    guardedRootMatches language provider rule type source = matchPattern rule.left source := by
  simp [guardedRootMatches, accepted]

theorem guardedRootMatches_rejected {rule : RewriteRule} {type : TypeExpr} {source : Pattern}
    (rejected : rootSortGuard language provider rule type = false) :
    guardedRootMatches language provider rule type source = [] := by
  simp [guardedRootMatches, rejected]

theorem matching_captures_typed_of_rootSortGuard {rule : RewriteRule} {type : TypeExpr}
    {bound : List TypeExpr} {source : Pattern} {initial : Bindings}
    (valid : (environment language provider).language.validate = []) (left : FirstOrder rule.left)
    (accepted : rootSortGuard language provider rule type = true)
    (sourceTyped : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source)
    (matched : MatchRel rule.left source initial) :
    CapturesTyped (environment language provider).language (environment language provider).free bound
      rule.typeContext initial :=
  matching_captures_typed valid left matched (rootSortGuard_sound accepted).1 sourceTyped.1
    sourceTyped.2.1 sourceTyped.2.2.1

/-- A successful scoped root match that passes the actual assignment checker
has the invocation sort. Variable roots use their captured body's declared
sort; constructor roots use the validated grammar declaration. -/
theorem root_match_sort_of_typed {rule : RewriteRule} {index : Nat} {bound : List TypeExpr}
    {source : Pattern} {ruleType invocationType : TypeExpr} {captured : Assignment}
    (valid : (environment language provider).language.validate = [])
    (left : FirstOrder rule.left) (sourceShape : FirstOrder source)
    (leftTyped : HasType (environment language provider).language (FreeTypeContext.ofList rule.typeContext)
      [] rule.left ruleType)
    (sourceTyped : HasType (environment language provider).language (environment language provider).free
      bound source invocationType)
    (matching : GeneralScopedMatch.Matches rule (GeneralRuleBindingInference.inferredSpec rule)
      bound.length .left [] 0 [] rule.left source captured)
    (capturedTyped : GeneralPremise.TypedAssignment (environment language provider)
      ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩ captured) :
    ruleType = invocationType := by
  have roots := capturedTyped.rootValues (inferred_zero rule)
  have reconstructed := matching_reconstructs left matching (GeneralScopedMatch.Extends.refl _) roots
  generalize schemaEqual : rule.left = schema at left leftTyped matching reconstructed
  cases left with
  | metavariable name =>
    cases leftTyped with
    | fvar declared =>
      obtain ⟨value, found⟩ := GeneralPremise.matching_bound_names matching name
        (by simp [Pattern.freeFvarNames])
      obtain ⟨dependencies, expected, dependenciesFound, contextFound, _, _, valueTyped⟩ :=
        capturedTyped.1 name value (ConditionalEquationExecution.lookup_assignment_member _ _ _ found)
      have empty := GeneralPremise.checkZeroDependencies_sound _ (inferred_zero rule)
        name dependencies dependenciesFound
      have same : expected = ruleType := Option.some.inj
        (contextFound.symm.trans ((context_ofList_lookup rule.typeContext name) ▸ declared))
      have body : value.body = source := (ordinary_variable found).symm.trans reconstructed
      subst expected
      rw [empty, List.nil_append, body] at valueTyped
      exact sourceShape.type_unique valid valueTyped sourceTyped
  | constructor label arguments _ =>
    rw [← reconstructed] at sourceTyped
    simp only [applyBindings] at sourceTyped
    exact apply_types_agree valid leftTyped sourceTyped

theorem FirstOrderRowFacts.guard_of_typed_match {index : Nat} {rule : RewriteRule}
    {bound : List TypeExpr} {source : Pattern} {type : TypeExpr} {captured : Assignment}
    (row : FirstOrderRowFacts language provider index rule)
    (valid : (environment language provider).language.validate = [])
    (sourceShape : FirstOrder source)
    (sourceTyped : HasType (environment language provider).language (environment language provider).free
      bound source type)
    (matching : GeneralScopedMatch.Matches rule (GeneralRuleBindingInference.inferredSpec rule)
      bound.length .left [] 0 [] rule.left source captured)
    (capturedTyped : GeneralPremise.TypedAssignment (environment language provider)
      ⟨index, rule, GeneralRuleBindingInference.inferredSpec rule, bound, 0, 0⟩ captured) :
    rootSortGuard language provider rule type = true := by
  obtain ⟨ruleType, checked⟩ := row.checked_sort valid
  have same := root_match_sort_of_typed valid row.left sourceShape
    (checkedRuleSort?_sound checked).1 sourceTyped matching capturedTyped
  simp only [rootSortGuard, checked, same, beq_self_eq_true]

theorem FirstOrderRowFacts.guard_of_rootFiring {index : Nat} {rule : RewriteRule}
    {bound : List TypeExpr} {source target : Pattern} {type : TypeExpr}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List GeneralPremise.Event}
    (row : FirstOrderRowFacts language provider index rule)
    (valid : (environment language provider).language.validate = [])
    (declared : (environment language provider).language.rewrites[index]? = some rule)
    (sourceShape : FirstOrder source)
    (fired : GeneralPremise.RootFiring (environment language provider) bound type source index
      trace captured completed history target) : rootSortGuard language provider rule type = true := by
  cases fired with
  | fire actualDeclared actualSpecified _ sourceTyped matching capturedTyped _ _ _ =>
    have same := Option.some.inj (actualDeclared.symm.trans declared)
    subst same
    have specSame := Option.some.inj (actualSpecified.symm.trans row.specified)
    subst specSame
    exact row.guard_of_typed_match valid sourceShape sourceTyped.1 matching.matching capturedTyped

/-- A rejected source sort has no authored root results, including when the
untyped wildcard matcher would have produced a capture. -/
theorem root_results_eq_nil_of_rootSortGuard_false {index : Nat} {rule : RewriteRule}
    {bound : List TypeExpr} {source : Pattern} {type : TypeExpr}
    (row : FirstOrderRowFacts language provider index rule)
    (valid : (environment language provider).language.validate = [])
    (declared : (environment language provider).language.rewrites[index]? = some rule)
    (sourceShape : FirstOrder source) (rejected : rootSortGuard language provider rule type = false) :
    GeneralPremise.Execution.results (environment language provider) (.root bound type source index) = [] := by
  cases results : GeneralPremise.Execution.results (environment language provider)
      (.root bound type source index) with
  | nil => rfl
  | cons result rest =>
    cases result with
    | root _ _ _ _ _ fired =>
      have accepted := row.guard_of_rootFiring valid declared sourceShape fired
      rw [rejected] at accepted
      cases accepted

def checkFirstOrderRowFacts (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (entry : RewriteRule × Nat) : Bool :=
  GeneralPremise.specification? (environment language provider) entry.2 ==
      some (GeneralRuleBindingInference.inferredSpec entry.1) &&
    admittedFor entry.1 (GeneralRuleBindingInference.inferredSpec entry.1) &&
    checkFirstOrder entry.1.left && checkFirstOrder entry.1.right &&
    entry.1.premises.all checkSupportedPremise &&
    GeneralPremise.rulePremisesAdmitted (environment language provider).language
      (environment language provider).provider entry.1 (GeneralRuleBindingInference.inferredSpec entry.1) &&
    decide (entry.1.typeContext.map Prod.fst).Nodup &&
    ruleDepthAligned entry.1 && checkRuleTyped language provider entry.1

theorem FirstOrderRowFacts.of_check {index : Nat} {rule : RewriteRule}
    (checked : checkFirstOrderRowFacts language provider (rule, index) = true) :
    FirstOrderRowFacts language provider index rule := by
  simp only [checkFirstOrderRowFacts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at checked
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨specified, admitted⟩, left⟩, right⟩, premises⟩, flow⟩, unique⟩, aligned⟩,
    typed⟩ := checked
  exact ⟨specified, admitted, checkFirstOrder_sound left, checkFirstOrder_sound right,
    fun premise member => checkCongruencePremise_sound (premises premise member), flow, unique,
    aligned, checkRuleTyped_sound typed⟩

def checkFirstOrderRow (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (entry : RewriteRule × Nat) : Bool :=
  checkFirstOrderRowFacts language provider entry && checkHeaded entry.1.left

theorem FirstOrderRow.of_check {index : Nat} {rule : RewriteRule}
    (checked : checkFirstOrderRow language provider (rule, index) = true) :
    FirstOrderRow language provider index rule := by
  simp only [checkFirstOrderRow, Bool.and_eq_true] at checked
  exact ⟨FirstOrderRowFacts.of_check checked.1, checkHeaded_sound checked.2⟩

/-- The common first-order profile as one computation, including variable roots. -/
def checkFirstOrderProfileFacts (language : LanguageDef)
    (provider : GeneralPremise.ProviderSnapshot := { signatures := [], rows := [] }) : Bool :=
  provider.dynamicRelations.isEmpty &&
    (environment language provider).language.validate.isEmpty &&
    GeneralPremise.checkProviderClosed (environment language provider).language
      (environment language provider).free (environment language provider).provider &&
    language.isEquationFree &&
    (rootPlan language provider).equations.isEmpty &&
    ((environment language provider).language.rewrites.map ruleCore == language.rewrites.map ruleCore) &&
    (environment language provider).language.rewrites.zipIdx.all (checkFirstOrderRowFacts language provider)

theorem FirstOrderProfileFacts.of_check (checked : checkFirstOrderProfileFacts language provider = true) :
    FirstOrderProfileFacts language provider := by
  simp only [checkFirstOrderProfileFacts, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at checked
  obtain ⟨⟨⟨⟨⟨⟨finiteProvider, valid⟩, providerClosed⟩, equationFree⟩, equations⟩, sameRules⟩, rows⟩ := checked
  refine ⟨valid, providerClosed, equationFree, equations, sameRules, ?_, finiteProvider⟩
  intro index rule declared
  have row := List.all_eq_true.mp rows (rule, index) (List.mk_mem_zipIdx_iff_getElem?.mpr declared)
  exact FirstOrderRowFacts.of_check row

/-- The legacy unguarded profile additionally requires every root to carry a
constructor head. -/
def checkFirstOrderProfile (language : LanguageDef)
    (provider : GeneralPremise.ProviderSnapshot := { signatures := [], rows := [] }) : Bool :=
  checkFirstOrderProfileFacts language provider &&
    (environment language provider).language.rewrites.all (fun rule => checkHeaded rule.left)

theorem FirstOrderProfile.of_check (checked : checkFirstOrderProfile language provider = true) :
    FirstOrderProfile language provider := by
  simp only [checkFirstOrderProfile, Bool.and_eq_true] at checked
  refine ⟨FirstOrderProfileFacts.of_check checked.1, ?_⟩
  intro index rule declared
  exact checkHeaded_sound (List.all_eq_true.mp checked.2 rule (List.mem_of_getElem? declared))

namespace RootSortControls

def terms : List GrammarRule := [
  { label := "NZero", category := "Nat", params := [], syntaxPattern := [] },
  { label := "NSucc", category := "Nat", params := [.simple "n" (.base "Nat")],
    syntaxPattern := [.nonTerminal "n"] },
  { label := "BoolF", category := "Bool", params := [], syntaxPattern := [] }]

def natWildcard : RewriteRule :=
  { name := "NatWildcard", typeContext := [("x", .base "Nat")], premises := [],
    left := .fvar "x", right := .fvar "x", bindings := some {dependencies := [("x", [])]} }

def boolWildcard : RewriteRule :=
  { name := "BoolWildcard", typeContext := [("b", .base "Bool")], premises := [],
    left := .fvar "b", right := .fvar "b", bindings := some {dependencies := [("b", [])]} }

def natHead : RewriteRule :=
  { name := "NatHead", typeContext := [], premises := [], left := .apply "NZero" [],
    right := .apply "NSucc" [.apply "NZero" []], bindings := some {dependencies := []} }

def natCopy : RewriteRule := {natWildcard with name := "NatCopy"}

def mixedLanguage : LanguageDef :=
  LanguageDef.ofCore "MixedRootSorts" ["Nat", "Bool"] terms []
    [natWildcard, boolWildcard, natHead, natCopy]

def emptyProvider : GeneralPremise.ProviderSnapshot := { signatures := [], rows := [] }

theorem mixed_profile : checkFirstOrderProfileFacts mixedLanguage emptyProvider = true := by cbv

theorem unguarded_profile_refuses_wildcards : checkFirstOrderProfile mixedLanguage emptyProvider = false := by cbv

theorem nat_declared : (environment mixedLanguage emptyProvider).language.rewrites[0]? = some natWildcard := by cbv

theorem bool_declared : (environment mixedLanguage emptyProvider).language.rewrites[1]? = some boolWildcard := by cbv

theorem nat_sort : checkedRuleSort? mixedLanguage emptyProvider natWildcard = some (.base "Nat") := by cbv

theorem bool_sort : checkedRuleSort? mixedLanguage emptyProvider boolWildcard = some (.base "Bool") := by cbv

theorem nat_guard_accepts : rootSortGuard mixedLanguage emptyProvider natWildcard (.base "Nat") = true := by cbv

theorem nat_guard_refuses_bool : rootSortGuard mixedLanguage emptyProvider natWildcard (.base "Bool") = false := by cbv

def guardedOccurrences (type : TypeExpr) (subject : Pattern) : List (Nat × Pattern) :=
  mixedLanguage.rewrites.zipIdx.flatMap fun (rule, index) =>
    (guardedRootMatches mixedLanguage emptyProvider rule type subject).map fun bindings =>
      (index, applyBindings bindings rule.right)

/-- Same-sort overlap and equal targets retain the original declaration indices. -/
theorem nat_order_and_duplicates : guardedOccurrences (.base "Nat") (.apply "NZero" []) =
    [(0, .apply "NZero" []), (2, .apply "NSucc" [.apply "NZero" []]), (3, .apply "NZero" [])] := by cbv

theorem bool_selection : guardedOccurrences (.base "Bool") (.apply "BoolF" []) =
    [(1, .apply "BoolF" [])] := by cbv

/-- The untyped matcher really accepts this cross-sort capture. -/
theorem raw_cross_sort_match : matchPattern natWildcard.left (.apply "BoolF" []) =
    [[("x", .apply "BoolF" [])]] := by cbv

theorem cross_sort_authored_empty :
    GeneralPremise.Execution.results (environment mixedLanguage emptyProvider)
      (.root [] (.base "Bool") (.apply "BoolF" []) 0) = [] :=
  root_results_eq_nil_of_rootSortGuard_false
    ((FirstOrderProfileFacts.of_check mixed_profile).rowFacts nat_declared)
    (FirstOrderProfileFacts.of_check mixed_profile).valid nat_declared
    (.constructor _ _ (by simp)) nat_guard_refuses_bool

theorem nat_authored_firing : ∃ trace captured,
    GeneralPremise.RootFiring (environment mixedLanguage emptyProvider) [] (.base "Nat")
      (.apply "NZero" []) 0 trace captured captured [] (.apply "NZero" []) := by
  have profile := FirstOrderProfileFacts.of_check mixed_profile
  have row := profile.rowFacts nat_declared
  have typed := rootSortGuard_sound nat_guard_accepts
  exact rootFiring_construct profile.valid nat_declared row.specified row.admitted (by cbv)
    typed.1 typed.2 (checkOpenPatternWellSorted_sound (by cbv))
    (MatchRel.fvar (x := "x") (t := .apply "NZero" [])) (by cbv)

theorem bool_authored_firing : ∃ trace captured,
    GeneralPremise.RootFiring (environment mixedLanguage emptyProvider) [] (.base "Bool")
      (.apply "BoolF" []) 1 trace captured captured [] (.apply "BoolF" []) := by
  have profile := FirstOrderProfileFacts.of_check mixed_profile
  have row := profile.rowFacts bool_declared
  have typed := checkedRuleSort?_sound bool_sort
  exact rootFiring_construct profile.valid bool_declared row.specified row.admitted (by cbv)
    typed.1 typed.2 (checkOpenPatternWellSorted_sound (by cbv))
    (MatchRel.fvar (x := "b") (t := .apply "BoolF" [])) (by cbv)

end RootSortControls

end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
