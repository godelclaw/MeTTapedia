import Mettapedia.Languages.Megalodon.EtaConversionKernel
import Mettapedia.Languages.MM0.Translation.CalculusSimulation
import Mettapedia.GSLT.LanguageDef.TierLattice

/-!
# The Mathdata conversion profile, elaborated into an explicit calculus

The Lean Mathdata kernel model decides conversion by computing: it unfolds definitions
(`deltaNormalize`), then repeats bottom-up beta-eta passes (`Tm.normalizeOne`) until a pass
finds no redex, and compares normal forms. An explicit calculus checks conversion without
computing: an article lists every reduction step, with the substitution, shift and
membership evidence each step needs.

The explicit calculus is that of `DefinitionConversionKernel`. It has a rule for each
contraction of the normalizer, type-level eta included, and a congruence rule for each
constructor.

This module instruments the normalizer so that it writes its own article.

* **One pass.** `elaboratePass` runs the pass of `Tm.normalizeOne` and records each
  contraction as a step, moved through the congruence rules to the position where it
  happens (`Frame`). It returns exactly what the pass returns, its steps lead from the
  input to the output, and the calculus accepts each step (`elaboratePass_spec`).
* **Definitions.** `elaborateDelta` does the same for `deltaNormalize`. A delta step cites
  the position of the definition in the declarations (`elaborateDelta_spec`), and every
  unfolding elaborates (`elaborateDelta_complete`).
* **Runs and conversion.** Passes compose into runs (`elaborateRun_spec`,
  `elaborateRun_complete`), a run's steps into a reduction path article
  (`pathArticle_checked`), and two normalizations with the same normal form into a
  conversion article (`conversionArticle_checked`).
* **Exact elaboration.** The modeled conversion test elaborates into the calculus's
  conversion judgment, and accepts exactly when the elaborated article is accepted
  (`conversionElaboration`). Soundness of the calculus therefore gives soundness of the
  native test, with no trust in the normalizer (`nativeChecker_sound`).
* **The load.** One step of `reductionGSLT` is a reduction the calculus accepts. A pass
  that changes its term is one step of the coarsening of that system, and its load is the
  number of contractions it writes (`elaboratePass_coarse`). A run reaches its normal form
  in as many steps as it writes (`elaborateRun_reaches`).
* **On to MM0.** The calculus is first-order (`calculus_firstOrder`). Its
  `mm0Equivalent` supplies size simulations with declared polynomial accounts,
  not executed translation-time bounds. Every conversion the modeled test
  accepts has an MM0 witness (`native_mm0`).

Beta steps use the checked substitution compiler of `EnvironmentKernel`, type-level beta
its checked type substitution compiler, eta the checked shift witness of
`EtaConversionKernel`, and type-level eta the checked type shift of
`DefinitionConversionKernel`.

The budget is a count of passes and unfoldings, as in the Lean model of the kernel;
The upstream Proofgold/Megalodon beta counter and lazy conversion algorithm
are not executions of this pass-based model. The profile theorem is not a
verification of those source algorithms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ConversionElaboration

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Mettapedia.Languages.Megalodon
open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.OSLF.MeTTaIL.Syntax
open DefinitionConversionKernel

/-- Terms, types and numerals as patterns of the calculus. -/
abbrev ETm := TermQuantifiedKernel.encodeTm
abbrev ETp := TermQuantifiedKernel.encodeTp
abbrev ENat := TermQuantifiedKernel.encodeNat


/-! ## Articles node by node -/

/-- One node of an article. -/
def node (id : String) (arguments : List Pattern) (children : List RawProof := []) : RawProof :=
  .node { ruleId := ruleId id, arguments } children

/-- A node whose rule instantiates to given premises and conclusion is accepted for that
conclusion exactly when its children are accepted for those premises. -/
theorem checkRaw_node {ruleInstance : RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (children : List RawProof)
    (instantiated : instantiateRule? validated ruleInstance = some (premises, conclusion)) :
    checkRaw validated conclusion (.node ruleInstance children) =
      checkRawChildren validated premises children := by
  rw [checkRaw, instantiated]
  simp

theorem checkRawChildren_one (premise : Pattern) (child : RawProof) :
    checkRawChildren validated [premise] [child] = checkRaw validated premise child := by
  simp [checkRawChildren]

theorem checkRawChildren_two (first second : Pattern) (firstChild secondChild : RawProof) :
    checkRawChildren validated [first, second] [firstChild, secondChild] =
      (checkRaw validated first firstChild && checkRaw validated second secondChild) := by
  simp [checkRawChildren]


/-! ## Instances of the rules -/

section Instances

variable (declarations : List TermDecl)

/-- The declarations as the calculus reads them. -/
abbrev encoded : Pattern := encodeTermDeclarations declarations

set_option maxRecDepth 100000

theorem instantiate_appFunction (function functionResult argument : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-app-function",
          arguments := [encoded declarations, ETm function, ETm functionResult, ETm argument] } =
      some ([reduces (encoded declarations) (ETm function) (ETm functionResult)],
        reduces (encoded declarations) (ETm (.app function argument))
          (ETm (.app functionResult argument))) := by
  simp only [instantiateRule?, validated, lookup_reduceAppFunctionRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, reduceAppFunctionRule, rule, ruleId, reduces, a, m,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a]

theorem instantiate_appArgument (function argument argumentResult : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-app-argument",
          arguments := [encoded declarations, ETm function, ETm argument, ETm argumentResult] } =
      some ([reduces (encoded declarations) (ETm argument) (ETm argumentResult)],
        reduces (encoded declarations) (ETm (.app function argument))
          (ETm (.app function argumentResult))) := by
  simp only [instantiateRule?, validated, lookup_reduceAppArgumentRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, DefinitionConversionKernel.reduceAppArgumentRule, rule,
    ruleId, reduces, a, m, TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a]

theorem instantiate_lamBody (type : Tp) (body bodyResult : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-lam-body",
          arguments := [encoded declarations, ETp type, ETm body, ETm bodyResult] } =
      some ([reduces (encoded declarations) (ETm body) (ETm bodyResult)],
        reduces (encoded declarations) (ETm (.lam type body)) (ETm (.lam type bodyResult))) := by
  simp only [instantiateRule?, validated, lookup_reduceLamBodyRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, reduceLamBodyRule, rule, ruleId, reduces, a, m,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a]

theorem instantiate_impDomain (domain domainResult codomain : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-imp-domain",
          arguments := [encoded declarations, ETm domain, ETm domainResult, ETm codomain] } =
      some ([reduces (encoded declarations) (ETm domain) (ETm domainResult)],
        reduces (encoded declarations) (ETm (.imp domain codomain))
          (ETm (.imp domainResult codomain))) := by
  simp only [instantiateRule?, validated, lookup_reduceImpDomainRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, reduceImpDomainRule, rule, ruleId, reduces, a, m,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a]

theorem instantiate_impCodomain (domain codomain codomainResult : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-imp-codomain",
          arguments := [encoded declarations, ETm domain, ETm codomain, ETm codomainResult] } =
      some ([reduces (encoded declarations) (ETm codomain) (ETm codomainResult)],
        reduces (encoded declarations) (ETm (.imp domain codomain))
          (ETm (.imp domain codomainResult))) := by
  simp only [instantiateRule?, validated, lookup_reduceImpCodomainRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, DefinitionConversionKernel.reduceImpCodomainRule, rule,
    ruleId, reduces, a, m, TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a]

theorem instantiate_allBody (type : Tp) (body bodyResult : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-all-body",
          arguments := [encoded declarations, ETp type, ETm body, ETm bodyResult] } =
      some ([reduces (encoded declarations) (ETm body) (ETm bodyResult)],
        reduces (encoded declarations) (ETm (.all type body)) (ETm (.all type bodyResult))) := by
  simp only [instantiateRule?, validated, lookup_reduceAllBodyRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, reduceAllBodyRule, rule, ruleId, reduces, a, m,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a]

theorem instantiate_typeAppFunction (function functionResult : Tm) (type : Tp) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-type-app-function",
          arguments := [encoded declarations, ETm function, ETm functionResult, ETp type] } =
      some ([reduces (encoded declarations) (ETm function) (ETm functionResult)],
        reduces (encoded declarations) (ETm (.typeApp function type))
          (ETm (.typeApp functionResult type))) := by
  simp only [instantiateRule?, validated, lookup_reduceTypeAppFunctionRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, reduceTypeAppFunctionRule, rule, ruleId, reduces, a, m,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a]

theorem instantiate_typeLamBody (body bodyResult : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-type-lam-body",
          arguments := [encoded declarations, ETm body, ETm bodyResult] } =
      some ([reduces (encoded declarations) (ETm body) (ETm bodyResult)],
        reduces (encoded declarations) (ETm (.typeLam body)) (ETm (.typeLam bodyResult))) := by
  simp only [instantiateRule?, validated, lookup_reduceTypeLamBodyRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, reduceTypeLamBodyRule, rule, ruleId, reduces, a, m,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a]

theorem instantiate_typeAllBody (body bodyResult : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-type-all-body",
          arguments := [encoded declarations, ETm body, ETm bodyResult] } =
      some ([reduces (encoded declarations) (ETm body) (ETm bodyResult)],
        reduces (encoded declarations) (ETm (.typeAll body)) (ETm (.typeAll bodyResult))) := by
  simp only [instantiateRule?, validated, lookup_reduceTypeAllBodyRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, reduceTypeAllBodyRule, rule, ruleId, reduces, a, m,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a]

theorem instantiate_beta (type : Tp) (body argument result : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-beta",
          arguments := [encoded declarations, ETp type, ETm body, ETm argument, ETm result] } =
      some ([EnvironmentKernel.substituteTerm (ENat 0) (ETm argument) (ETm body) (ETm result)],
        reduces (encoded declarations) (ETm (.app (.lam type body) argument)) (ETm result)) := by
  simp only [instantiateRule?, validated, lookup_reduceBetaRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, reduceBetaRule, rule, ruleId, reduces, a, m,
    substituteTerm, EnvironmentKernel.substituteTerm, EnvironmentKernel.a,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.a]

theorem instantiate_typeBeta (body : Tm) (type : Tp) (result : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-type-beta",
          arguments := [encoded declarations, ETm body, ETp type, ETm result] } =
      some ([EnvironmentKernel.substituteTypeInTerm (ENat 0) (ETp type) (ETm body) (ETm result)],
        reduces (encoded declarations) (ETm (.typeApp (.typeLam body) type)) (ETm result)) := by
  simp only [instantiateRule?, validated, lookup_reduceTypeBetaRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, reduceTypeBetaRule, rule, ruleId, reduces, a, m,
    substituteTypeInTerm, EnvironmentKernel.substituteTypeInTerm, EnvironmentKernel.a,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.a]

theorem instantiate_delta (name : Name) (type : Tp) (body : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-reduce-delta",
          arguments := [encoded declarations, a name, ETp type, ETm body] } =
      some ([definitionMember (encoded declarations) (a name) (ETp type) (ETm body)],
        reduces (encoded declarations) (ETm (.named name)) (ETm body)) := by
  simp only [instantiateRule?, validated, lookup_reduceDeltaRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, reduceDeltaRule, definitionMember, rule, ruleId, reduces,
    a, m, Pattern.isGroundAt, Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, TermQuantifiedKernel.encodeTm,
    TermQuantifiedKernel.a]

theorem instantiate_pathRefl (term : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-path-refl",
          arguments := [encoded declarations, ETm term] } =
      some ([], reductionPath (encoded declarations) (ETm term) (ETm term)) := by
  simp only [instantiateRule?, validated, lookup_pathReflRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, DefinitionConversionKernel.pathReflRule, rule, ruleId,
    reductionPath, a, m]

theorem instantiate_pathStep (source middle target : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-path-step",
          arguments := [encoded declarations, ETm source, ETm middle, ETm target] } =
      some ([reduces (encoded declarations) (ETm source) (ETm middle),
          reductionPath (encoded declarations) (ETm middle) (ETm target)],
        reductionPath (encoded declarations) (ETm source) (ETm target)) := by
  simp only [instantiateRule?, validated, lookup_pathStepRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, DefinitionConversionKernel.pathStepRule, rule, ruleId,
    reductionPath, reduces, a, m]

theorem instantiate_conversionCommon (left right common : Tm) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-conversion-common",
          arguments := [encoded declarations, ETm left, ETm right, ETm common] } =
      some ([reductionPath (encoded declarations) (ETm left) (ETm common),
          reductionPath (encoded declarations) (ETm right) (ETm common)],
        converts (encoded declarations) (ETm left) (ETm right)) := by
  simp only [instantiateRule?, validated, lookup_conversionCommonRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, DefinitionConversionKernel.conversionCommonRule, rule,
    ruleId, reductionPath, converts, scopedTerm, a, m]

end Instances


/-! ## Steps and paths -/

/-- One reduction step and the article that proves it. -/
structure Step where
  source : Tm
  target : Tm
  article : RawProof

section Paths

variable (declarations : List TermDecl)

/-- The step's article proves that its source reduces to its target. -/
def Step.Valid (step : Step) : Prop :=
  checkRaw validated (reduces (encoded declarations) (ETm step.source) (ETm step.target))
    step.article = true

/-- Steps that lead from one term to another, each starting where the previous one ended. -/
def Chain : Tm → List Step → Tm → Prop
  | start, [], finish => start = finish
  | start, step :: steps, finish => step.source = start ∧ Chain step.target steps finish

theorem Chain.append {start middle finish : Tm} {first second : List Step}
    (left : Chain start first middle) (right : Chain middle second finish) :
    Chain start (first ++ second) finish := by
  induction first generalizing start with
  | nil =>
      simp only [Chain] at left
      subst left
      simpa using right
  | cons step steps ih =>
      obtain ⟨same, rest⟩ := left
      exact ⟨same, ih rest⟩

/-- A reduction path article: one step node per step, then reflexivity. -/
def pathArticle (finish : Tm) : List Step → RawProof
  | [] => node "megalodon-def-path-refl" [encoded declarations, ETm finish]
  | step :: steps =>
      node "megalodon-def-path-step"
        [encoded declarations, ETm step.source, ETm step.target, ETm finish]
        [step.article, pathArticle finish steps]

/-- **A chain of valid steps is a reduction path the calculus accepts.** -/
theorem pathArticle_checked {start finish : Tm} {steps : List Step}
    (chain : Chain start steps finish) (valid : ∀ step ∈ steps, step.Valid declarations) :
    checkRaw validated (reductionPath (encoded declarations) (ETm start) (ETm finish))
      (pathArticle declarations finish steps) = true := by
  induction steps generalizing start with
  | nil =>
      simp only [Chain] at chain
      subst chain
      rw [pathArticle, node, checkRaw_node [] (instantiate_pathRefl declarations start)]
      simp [checkRawChildren]
  | cons step steps ih =>
      obtain ⟨same, rest⟩ := chain
      subst same
      rw [pathArticle, node,
        checkRaw_node _ (instantiate_pathStep declarations step.source step.target finish),
        checkRawChildren_two, Bool.and_eq_true]
      exact ⟨valid step (by simp), ih rest (fun other member => valid other (by simp [member]))⟩

end Paths

/-! ## Congruence -/

/-- A position under one constructor, with a hole in one argument. -/
inductive Frame where
  | appFunction (argument : Tm)
  | appArgument (function : Tm)
  | lamBody (type : Tp)
  | impDomain (codomain : Tm)
  | impCodomain (domain : Tm)
  | allBody (type : Tp)
  | typeAppFunction (type : Tp)
  | typeLamBody
  | typeAllBody

namespace Frame

/-- The term with the hole filled. -/
def plug : Frame → Tm → Tm
  | .appFunction argument, term => .app term argument
  | .appArgument function, term => .app function term
  | .lamBody type, term => .lam type term
  | .impDomain codomain, term => .imp term codomain
  | .impCodomain domain, term => .imp domain term
  | .allBody type, term => .all type term
  | .typeAppFunction type, term => .typeApp term type
  | .typeLamBody, term => .typeLam term
  | .typeAllBody, term => .typeAll term

/-- The congruence node that moves a step of the hole into the frame. -/
def article (declarations : List TermDecl) : Frame → Tm → Tm → RawProof → RawProof
  | .appFunction argument, source, target, proof =>
      node "megalodon-def-reduce-app-function"
        [encoded declarations, ETm source, ETm target, ETm argument] [proof]
  | .appArgument function, source, target, proof =>
      node "megalodon-def-reduce-app-argument"
        [encoded declarations, ETm function, ETm source, ETm target] [proof]
  | .lamBody type, source, target, proof =>
      node "megalodon-def-reduce-lam-body"
        [encoded declarations, ETp type, ETm source, ETm target] [proof]
  | .impDomain codomain, source, target, proof =>
      node "megalodon-def-reduce-imp-domain"
        [encoded declarations, ETm source, ETm target, ETm codomain] [proof]
  | .impCodomain domain, source, target, proof =>
      node "megalodon-def-reduce-imp-codomain"
        [encoded declarations, ETm domain, ETm source, ETm target] [proof]
  | .allBody type, source, target, proof =>
      node "megalodon-def-reduce-all-body"
        [encoded declarations, ETp type, ETm source, ETm target] [proof]
  | .typeAppFunction type, source, target, proof =>
      node "megalodon-def-reduce-type-app-function"
        [encoded declarations, ETm source, ETm target, ETp type] [proof]
  | .typeLamBody, source, target, proof =>
      node "megalodon-def-reduce-type-lam-body"
        [encoded declarations, ETm source, ETm target] [proof]
  | .typeAllBody, source, target, proof =>
      node "megalodon-def-reduce-type-all-body"
        [encoded declarations, ETm source, ETm target] [proof]

/-- A step of the hole, moved into the frame. -/
def lift (declarations : List TermDecl) (frame : Frame) (step : Step) : Step where
  source := frame.plug step.source
  target := frame.plug step.target
  article := frame.article declarations step.source step.target step.article

theorem lift_valid (declarations : List TermDecl) (frame : Frame) {step : Step}
    (valid : step.Valid declarations) : (frame.lift declarations step).Valid declarations := by
  cases frame with
  | appFunction argument =>
      rw [Step.Valid, lift, plug, plug, article, node,
        checkRaw_node _ (instantiate_appFunction declarations _ _ _), checkRawChildren_one]
      exact valid
  | appArgument function =>
      rw [Step.Valid, lift, plug, plug, article, node,
        checkRaw_node _ (instantiate_appArgument declarations _ _ _), checkRawChildren_one]
      exact valid
  | lamBody type =>
      rw [Step.Valid, lift, plug, plug, article, node,
        checkRaw_node _ (instantiate_lamBody declarations _ _ _), checkRawChildren_one]
      exact valid
  | impDomain codomain =>
      rw [Step.Valid, lift, plug, plug, article, node,
        checkRaw_node _ (instantiate_impDomain declarations _ _ _), checkRawChildren_one]
      exact valid
  | impCodomain domain =>
      rw [Step.Valid, lift, plug, plug, article, node,
        checkRaw_node _ (instantiate_impCodomain declarations _ _ _), checkRawChildren_one]
      exact valid
  | allBody type =>
      rw [Step.Valid, lift, plug, plug, article, node,
        checkRaw_node _ (instantiate_allBody declarations _ _ _), checkRawChildren_one]
      exact valid
  | typeAppFunction type =>
      rw [Step.Valid, lift, plug, plug, article, node,
        checkRaw_node _ (instantiate_typeAppFunction declarations _ _ _), checkRawChildren_one]
      exact valid
  | typeLamBody =>
      rw [Step.Valid, lift, plug, plug, article, node,
        checkRaw_node _ (instantiate_typeLamBody declarations _ _), checkRawChildren_one]
      exact valid
  | typeAllBody =>
      rw [Step.Valid, lift, plug, plug, article, node,
        checkRaw_node _ (instantiate_typeAllBody declarations _ _), checkRawChildren_one]
      exact valid

theorem chain_lift (declarations : List TermDecl) (frame : Frame) {start finish : Tm}
    {steps : List Step} (chain : Chain start steps finish) :
    Chain (frame.plug start) (steps.map (frame.lift declarations)) (frame.plug finish) := by
  induction steps generalizing start with
  | nil =>
      simp only [Chain] at chain
      subst chain
      rfl
  | cons step steps ih =>
      obtain ⟨same, rest⟩ := chain
      exact ⟨by rw [lift, same], ih rest⟩

theorem valid_lift (declarations : List TermDecl) (frame : Frame) {steps : List Step}
    (valid : ∀ step ∈ steps, step.Valid declarations) :
    ∀ step ∈ steps.map (frame.lift declarations), step.Valid declarations := by
  intro step member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact frame.lift_valid declarations (valid original originalMember)

end Frame


/-! ## Contractions -/

section Contractions

variable (declarations : List TermDecl)

set_option maxRecDepth 100000

theorem instantiate_definitionHere (name : Name) (type : Tp) (body : Tm) (tail : Pattern)
    (tailGround : tail.isGroundAt 0 = true) (tailCanonical : tail.hasCanonicalBinderMetadata = true) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-member-here",
          arguments := [a name, ETp type, ETm body, tail] } =
      some ([], definitionMember (a "MDeclDefinition" [a name, ETp type, ETm body, tail])
        (a name) (ETp type) (ETm body)) := by
  simp only [instantiateRule?, validated, lookup_definitionHereRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, definitionHereRule, definitionMember, rule, ruleId, a, m,
    Pattern.isGroundAt, Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, tailGround, tailCanonical]

theorem instantiate_definitionThereParameter (headName : Name) (headType : Tp) (tail : Pattern)
    (name : Name) (type : Tp) (body : Tm)
    (tailGround : tail.isGroundAt 0 = true) (tailCanonical : tail.hasCanonicalBinderMetadata = true) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-member-there-parameter",
          arguments := [a headName, ETp headType, tail, a name, ETp type, ETm body] } =
      some ([definitionMember tail (a name) (ETp type) (ETm body)],
        definitionMember (a "MDeclParameter" [a headName, ETp headType, tail])
          (a name) (ETp type) (ETm body)) := by
  simp only [instantiateRule?, validated, lookup_definitionThereParameterRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, definitionThereParameterRule, definitionMember, rule, ruleId,
    a, m, Pattern.isGroundAt, Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, tailGround, tailCanonical]

theorem instantiate_definitionThereDefinition (headName : Name) (headType : Tp) (headBody : Tm)
    (tail : Pattern) (name : Name) (type : Tp) (body : Tm)
    (tailGround : tail.isGroundAt 0 = true) (tailCanonical : tail.hasCanonicalBinderMetadata = true) :
    instantiateRule? validated
        { ruleId := ruleId "megalodon-def-member-there-definition",
          arguments := [a headName, ETp headType, ETm headBody, tail, a name, ETp type, ETm body] } =
      some ([definitionMember tail (a name) (ETp type) (ETm body)],
        definitionMember (a "MDeclDefinition" [a headName, ETp headType, ETm headBody, tail])
          (a name) (ETp type) (ETm body)) := by
  simp only [instantiateRule?, validated, lookup_definitionThereDefinitionRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    RuleSchema.sideConditionsHold, definitionThereDefinitionRule, definitionMember, rule, ruleId,
    a, m, Pattern.isGroundAt, Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, tailGround, tailCanonical]

/-- The membership article for the first declaration of a name. -/
def memberArticle (name : Name) (type : Tp) (body : Tm) : List TermDecl → RawProof
  | [] => node "megalodon-def-member-here" []
  | declaration :: rest =>
      if declaration.name = name then
        node "megalodon-def-member-here" [a name, ETp type, ETm body, encoded rest]
      else
        match declaration.definition with
        | none =>
            node "megalodon-def-member-there-parameter"
              [a declaration.name, ETp declaration.type, encoded rest, a name, ETp type, ETm body]
              [memberArticle name type body rest]
        | some headBody =>
            node "megalodon-def-member-there-definition"
              [a declaration.name, ETp declaration.type, ETm headBody, encoded rest, a name,
                ETp type, ETm body]
              [memberArticle name type body rest]

theorem memberArticle_checked {name found : Name} {type : Tp} {body : Tm} :
    ∀ {declarations : List TermDecl},
      lookupTermList? declarations name = some ⟨found, type, some body⟩ →
        checkRaw validated (definitionMember (encoded declarations) (a name) (ETp type) (ETm body))
          (memberArticle name type body declarations) = true
  | [], lookup => by simp [lookupTermList?] at lookup
  | declaration :: rest, lookup => by
      by_cases same : declaration.name = name
      · have declared : declaration = ⟨found, type, some body⟩ := by
          simpa [lookupTermList?, same] using lookup
        subst declared
        simp only at same
        subst same
        have encodedEq : encoded ({ name := found, type := type, definition := some body } :: rest) =
            a "MDeclDefinition" [a found, ETp type, ETm body, encoded rest] := rfl
        rw [encodedEq, memberArticle, if_pos rfl, node,
          checkRaw_node [] (instantiate_definitionHere found type body (encoded rest)
            (by simp) (by simp))]
        simp [checkRawChildren]
      · have later : lookupTermList? rest name = some ⟨found, type, some body⟩ := by
          simpa [lookupTermList?, same] using lookup
        obtain ⟨headName, headType, headDefinition⟩ := declaration
        cases headDefinition with
        | none =>
            have encodedEq : encoded ({ name := headName, type := headType, definition := none } :: rest) =
                a "MDeclParameter" [a headName, ETp headType, encoded rest] := rfl
            rw [encodedEq, memberArticle, if_neg same]
            simp only
            rw [node, checkRaw_node _ (instantiate_definitionThereParameter headName headType
              (encoded rest) name type body (by simp) (by simp)), checkRawChildren_one]
            exact memberArticle_checked later
        | some headBody =>
            have encodedEq :
                encoded ({ name := headName, type := headType, definition := some headBody } :: rest) =
                  a "MDeclDefinition" [a headName, ETp headType, ETm headBody, encoded rest] := rfl
            rw [encodedEq, memberArticle, if_neg same]
            simp only
            rw [node, checkRaw_node _ (instantiate_definitionThereDefinition headName headType
              headBody (encoded rest) name type body (by simp) (by simp)), checkRawChildren_one]
            exact memberArticle_checked later

/-- A delta step: a named definition unfolds to its body. -/
def deltaStep (name : Name) (type : Tp) (body : Tm) : Step where
  source := .named name
  target := body
  article := node "megalodon-def-reduce-delta" [encoded declarations, a name, ETp type, ETm body]
    [memberArticle name type body declarations]

theorem deltaStep_valid {name found : Name} {type : Tp} {body : Tm}
    (lookup : lookupTermList? declarations name = some ⟨found, type, some body⟩) :
    (deltaStep declarations name type body).Valid declarations := by
  rw [Step.Valid, deltaStep, node, checkRaw_node _ (instantiate_delta declarations name type body),
    checkRawChildren_one]
  exact memberArticle_checked lookup

/-- A beta step, with the checked substitution as its evidence. -/
def betaStep (type : Tp) (body argument : Tm) : Step where
  source := .app (.lam type body) argument
  target := (EnvironmentKernel.compileTermSubstitute 0 argument body).1
  article := node "megalodon-def-reduce-beta"
    [encoded declarations, ETp type, ETm body, ETm argument,
      ETm (EnvironmentKernel.compileTermSubstitute 0 argument body).1]
    [(EnvironmentKernel.compileTermSubstitute 0 argument body).2]

theorem betaStep_target (type : Tp) (body argument : Tm) :
    (betaStep declarations type body argument).target = Tm.instantiate argument body :=
  EnvironmentKernel.compileTermSubstitute_result 0 argument body

theorem betaStep_valid (type : Tp) (body argument : Tm) :
    (betaStep declarations type body argument).Valid declarations := by
  rw [Step.Valid, betaStep, node, checkRaw_node _ (instantiate_beta declarations type body argument _),
    checkRawChildren_one]
  exact checkRaw_true_of_ruleLookupRefines DefinitionConversionKernel.environment_ruleLookupRefines
    (EnvironmentKernel.compileTermSubstitute_checked 0 argument body)

/-- A type-level beta step, with the checked type substitution as its evidence. -/
def typeBetaStep (body : Tm) (type : Tp) : Step where
  source := .typeApp (.typeLam body) type
  target := (EnvironmentKernel.compileTypeSubstituteTerm 0 type body).1
  article := node "megalodon-def-reduce-type-beta"
    [encoded declarations, ETm body, ETp type,
      ETm (EnvironmentKernel.compileTypeSubstituteTerm 0 type body).1]
    [(EnvironmentKernel.compileTypeSubstituteTerm 0 type body).2]

theorem typeBetaStep_target (body : Tm) (type : Tp) :
    (typeBetaStep declarations body type).target = Tm.typeInstantiate type body :=
  EnvironmentKernel.compileTypeSubstituteTerm_result 0 type body

theorem typeBetaStep_valid (body : Tm) (type : Tp) :
    (typeBetaStep declarations body type).Valid declarations := by
  rw [Step.Valid, typeBetaStep, node,
    checkRaw_node _ (instantiate_typeBeta declarations body type _), checkRawChildren_one]
  exact checkRaw_true_of_ruleLookupRefines DefinitionConversionKernel.environment_ruleLookupRefines
    (EnvironmentKernel.compileTypeSubstituteTerm_checked 0 type body)

/-- An eta step, with the checked shift of the result as its evidence. -/
def etaStep (type : Tp) (function result : Tm) : Step where
  source := .lam type (.app function (.db 0))
  target := result
  article := node "megalodon-def-reduce-eta" [encoded declarations, ETp type, ETm function, ETm result]
    [(EnvironmentKernel.compileTermShift 1 0 result).2]

theorem etaStep_valid {type : Tp} {function result : Tm}
    (drop : Tm.dropAt? 0 function = some result) :
    (etaStep declarations type function result).Valid declarations :=
  EtaConversionKernel.compileEtaReduction_checked (encoded declarations) type function result drop
    (by simp) (by simp)


/-- A type-level eta step, with the checked type shift of the result as its evidence. -/
def typeEtaStep (function result : Tm) : Step where
  source := .typeLam (.typeApp function (.var 0))
  target := result
  article := node "megalodon-def-reduce-type-eta" [encoded declarations, ETm function, ETm result]
    [(DefinitionConversionKernel.compileTypeShiftTerm 1 0 result).2]

theorem typeEtaStep_valid {function result : Tm}
    (drop : Tm.typeDropAt? 0 function = some result) :
    (typeEtaStep declarations function result).Valid declarations :=
  DefinitionConversionKernel.compileTypeEtaReduction_checked (encoded declarations) function result
    drop (by simp) (by simp)

end Contractions


/-! ## One pass -/

section Pass

variable (declarations : List TermDecl)

theorem valid_append {first second : List Step} (firstValid : ∀ step ∈ first, step.Valid declarations)
    (secondValid : ∀ step ∈ second, step.Valid declarations) :
    ∀ step ∈ first ++ second, step.Valid declarations := by
  intro step member
  rcases List.mem_append.mp member with member | member
  · exact firstValid step member
  · exact secondValid step member

theorem valid_singleton {step : Step} (valid : step.Valid declarations) :
    ∀ other ∈ [step], other.Valid declarations := by
  intro other member
  rw [List.mem_singleton.mp member]
  exact valid

/-- One pass of `Tm.normalizeOne` that writes its steps. -/
def elaboratePass : Tm → (Tm × Bool) × List Step
  | .app function argument =>
      let ((functionResult, functionStable), functionSteps) := elaboratePass function
      let ((argumentResult, argumentStable), argumentSteps) := elaboratePass argument
      match functionResult with
      | .lam type body =>
          ((Tm.instantiate argumentResult body, false),
            functionSteps.map ((Frame.appFunction argument).lift declarations) ++
              argumentSteps.map ((Frame.appArgument (.lam type body)).lift declarations) ++
                [betaStep declarations type body argumentResult])
      | _ =>
          ((.app functionResult argumentResult, functionStable && argumentStable),
            functionSteps.map ((Frame.appFunction argument).lift declarations) ++
              argumentSteps.map ((Frame.appArgument functionResult).lift declarations))
  | .lam type body =>
      let ((bodyResult, bodyStable), bodySteps) := elaboratePass body
      match bodyResult with
      | .app function (.db 0) =>
          match Tm.dropAt? 0 function with
          | some contracted =>
              ((contracted, false),
                bodySteps.map ((Frame.lamBody type).lift declarations) ++
                  [etaStep declarations type function contracted])
          | none =>
              ((.lam type bodyResult, bodyStable),
                bodySteps.map ((Frame.lamBody type).lift declarations))
      | _ =>
          ((.lam type bodyResult, bodyStable),
            bodySteps.map ((Frame.lamBody type).lift declarations))
  | .typeApp function type =>
      let ((functionResult, functionStable), functionSteps) := elaboratePass function
      match functionResult with
      | .typeLam body =>
          ((Tm.typeInstantiate type body, false),
            functionSteps.map ((Frame.typeAppFunction type).lift declarations) ++
              [typeBetaStep declarations body type])
      | _ =>
          ((.typeApp functionResult type, functionStable),
            functionSteps.map ((Frame.typeAppFunction type).lift declarations))
  | .typeLam body =>
      let ((bodyResult, bodyStable), bodySteps) := elaboratePass body
      match bodyResult with
      | .typeApp function (.var 0) =>
          match Tm.typeDropAt? 0 function with
          | some contracted =>
              ((contracted, false),
                bodySteps.map (Frame.typeLamBody.lift declarations) ++
                  [typeEtaStep declarations function contracted])
          | none =>
              ((.typeLam bodyResult, bodyStable),
                bodySteps.map (Frame.typeLamBody.lift declarations))
      | _ =>
          ((.typeLam bodyResult, bodyStable),
            bodySteps.map (Frame.typeLamBody.lift declarations))
  | .imp domain codomain =>
      let ((domainResult, domainStable), domainSteps) := elaboratePass domain
      let ((codomainResult, codomainStable), codomainSteps) := elaboratePass codomain
      ((.imp domainResult codomainResult, domainStable && codomainStable),
        domainSteps.map ((Frame.impDomain codomain).lift declarations) ++
          codomainSteps.map ((Frame.impCodomain domainResult).lift declarations))
  | .all type body =>
      let ((bodyResult, bodyStable), bodySteps) := elaboratePass body
      ((.all type bodyResult, bodyStable), bodySteps.map ((Frame.allBody type).lift declarations))
  | .typeAll body =>
      let ((bodyResult, bodyStable), bodySteps) := elaboratePass body
      ((.typeAll bodyResult, bodyStable), bodySteps.map (Frame.typeAllBody.lift declarations))
  | term => ((term, true), [])

/-- **A pass writes its own article.** The instrumented pass returns what `Tm.normalizeOne`
returns, and its steps lead from the input to the output, each accepted by the calculus. -/
theorem elaboratePass_spec (term : Tm) :
    (elaboratePass declarations term).1 = Tm.normalizeOne term ∧
      Chain term (elaboratePass declarations term).2 (elaboratePass declarations term).1.1 ∧
        ∀ step ∈ (elaboratePass declarations term).2, step.Valid declarations := by
  induction term with
  | db index => exact ⟨rfl, rfl, by simp [elaboratePass]⟩
  | named name => exact ⟨rfl, rfl, by simp [elaboratePass]⟩
  | prim index => exact ⟨rfl, rfl, by simp [elaboratePass]⟩
  | app function argument functionIH argumentIH =>
      rcases functionOut : elaboratePass declarations function with
        ⟨⟨functionResult, functionStable⟩, functionSteps⟩
      rcases argumentOut : elaboratePass declarations argument with
        ⟨⟨argumentResult, argumentStable⟩, argumentSteps⟩
      rw [functionOut] at functionIH
      rw [argumentOut] at argumentIH
      obtain ⟨functionEq, functionChain, functionValid⟩ := functionIH
      obtain ⟨argumentEq, argumentChain, argumentValid⟩ := argumentIH
      dsimp only at functionEq functionChain functionValid argumentEq argumentChain argumentValid
      have congruenceChain := Chain.append
        (Frame.chain_lift declarations (.appFunction argument) functionChain)
        (Frame.chain_lift declarations (.appArgument functionResult) argumentChain)
      have congruenceValid := valid_append declarations
        (Frame.valid_lift declarations (.appFunction argument) functionValid)
        (Frame.valid_lift declarations (.appArgument functionResult) argumentValid)
      simp only [elaboratePass, functionOut, argumentOut]
      cases functionResult
      case lam type body =>
        refine ⟨?_, Chain.append congruenceChain
          ⟨rfl, betaStep_target declarations type body argumentResult⟩,
          valid_append declarations congruenceValid
            (valid_singleton declarations (betaStep_valid declarations type body argumentResult))⟩
        simp only [Tm.normalizeOne, ← functionEq, ← argumentEq]
      all_goals
        refine ⟨?_, congruenceChain, congruenceValid⟩
        simp only [Tm.normalizeOne, ← functionEq, ← argumentEq]
  | lam type body bodyIH =>
      rcases bodyOut : elaboratePass declarations body with ⟨⟨bodyResult, bodyStable⟩, bodySteps⟩
      rw [bodyOut] at bodyIH
      obtain ⟨bodyEq, bodyChain, bodyValid⟩ := bodyIH
      dsimp only at bodyEq bodyChain bodyValid
      have congruenceChain := Frame.chain_lift declarations (.lamBody type) bodyChain
      have congruenceValid := Frame.valid_lift declarations (.lamBody type) bodyValid
      simp only [elaboratePass, bodyOut]
      split
      · rename_i function
        split
        · rename_i contracted drop
          refine ⟨?_, Chain.append congruenceChain ⟨rfl, rfl⟩,
            valid_append declarations congruenceValid
              (valid_singleton declarations (etaStep_valid declarations drop))⟩
          simp only [Tm.normalizeOne, ← bodyEq, drop]
        · rename_i drop
          refine ⟨?_, congruenceChain, congruenceValid⟩
          simp only [Tm.normalizeOne, ← bodyEq, drop]
      · refine ⟨?_, congruenceChain, congruenceValid⟩
        simp only [Tm.normalizeOne, ← bodyEq]
  | typeApp function type functionIH =>
      rcases functionOut : elaboratePass declarations function with
        ⟨⟨functionResult, functionStable⟩, functionSteps⟩
      rw [functionOut] at functionIH
      obtain ⟨functionEq, functionChain, functionValid⟩ := functionIH
      dsimp only at functionEq functionChain functionValid
      have congruenceChain := Frame.chain_lift declarations (.typeAppFunction type) functionChain
      have congruenceValid := Frame.valid_lift declarations (.typeAppFunction type) functionValid
      simp only [elaboratePass, functionOut]
      cases functionResult
      case typeLam body =>
        refine ⟨?_, Chain.append congruenceChain
          ⟨rfl, typeBetaStep_target declarations body type⟩,
          valid_append declarations congruenceValid
            (valid_singleton declarations (typeBetaStep_valid declarations body type))⟩
        simp only [Tm.normalizeOne, ← functionEq]
      all_goals
        refine ⟨?_, congruenceChain, congruenceValid⟩
        simp only [Tm.normalizeOne, ← functionEq]
  | typeLam body bodyIH =>
      rcases bodyOut : elaboratePass declarations body with ⟨⟨bodyResult, bodyStable⟩, bodySteps⟩
      rw [bodyOut] at bodyIH
      obtain ⟨bodyEq, bodyChain, bodyValid⟩ := bodyIH
      dsimp only at bodyEq bodyChain bodyValid
      have congruenceChain := Frame.chain_lift declarations .typeLamBody bodyChain
      have congruenceValid := Frame.valid_lift declarations .typeLamBody bodyValid
      simp only [elaboratePass, bodyOut]
      split
      · rename_i function
        split
        · rename_i contracted drop
          refine ⟨?_, Chain.append congruenceChain ⟨rfl, rfl⟩,
            valid_append declarations congruenceValid
              (valid_singleton declarations (typeEtaStep_valid declarations drop))⟩
          simp only [Tm.normalizeOne, ← bodyEq, drop]
        · rename_i drop
          refine ⟨?_, congruenceChain, congruenceValid⟩
          simp only [Tm.normalizeOne, ← bodyEq, drop]
      · refine ⟨?_, congruenceChain, congruenceValid⟩
        simp only [Tm.normalizeOne, ← bodyEq]
  | imp domain codomain domainIH codomainIH =>
      rcases domainOut : elaboratePass declarations domain with
        ⟨⟨domainResult, domainStable⟩, domainSteps⟩
      rcases codomainOut : elaboratePass declarations codomain with
        ⟨⟨codomainResult, codomainStable⟩, codomainSteps⟩
      rw [domainOut] at domainIH
      rw [codomainOut] at codomainIH
      obtain ⟨domainEq, domainChain, domainValid⟩ := domainIH
      obtain ⟨codomainEq, codomainChain, codomainValid⟩ := codomainIH
      dsimp only at domainEq domainChain domainValid codomainEq codomainChain codomainValid
      simp only [elaboratePass, domainOut, codomainOut]
      refine ⟨?_, Chain.append
          (Frame.chain_lift declarations (.impDomain codomain) domainChain)
          (Frame.chain_lift declarations (.impCodomain domainResult) codomainChain),
        valid_append declarations
          (Frame.valid_lift declarations (.impDomain codomain) domainValid)
          (Frame.valid_lift declarations (.impCodomain domainResult) codomainValid)⟩
      simp only [Tm.normalizeOne, ← domainEq, ← codomainEq]
  | all type body bodyIH =>
      rcases bodyOut : elaboratePass declarations body with ⟨⟨bodyResult, bodyStable⟩, bodySteps⟩
      rw [bodyOut] at bodyIH
      obtain ⟨bodyEq, bodyChain, bodyValid⟩ := bodyIH
      dsimp only at bodyEq bodyChain bodyValid
      simp only [elaboratePass, bodyOut]
      refine ⟨?_, Frame.chain_lift declarations (.allBody type) bodyChain,
        Frame.valid_lift declarations (.allBody type) bodyValid⟩
      simp only [Tm.normalizeOne, ← bodyEq]
  | typeAll body bodyIH =>
      rcases bodyOut : elaboratePass declarations body with ⟨⟨bodyResult, bodyStable⟩, bodySteps⟩
      rw [bodyOut] at bodyIH
      obtain ⟨bodyEq, bodyChain, bodyValid⟩ := bodyIH
      dsimp only at bodyEq bodyChain bodyValid
      simp only [elaboratePass, bodyOut]
      refine ⟨?_, Frame.chain_lift declarations .typeAllBody bodyChain,
        Frame.valid_lift declarations .typeAllBody bodyValid⟩
      simp only [Tm.normalizeOne, ← bodyEq]

theorem elaboratePass_fst (term : Tm) :
    (elaboratePass declarations term).1 = Tm.normalizeOne term :=
  (elaboratePass_spec declarations term).1

end Pass




/-! ## Unfolding definitions -/

section Delta

variable (environment : Environment)

/-- `deltaNormalize`, writing its steps. -/
def elaborateDelta : Nat → Tm → Option (Tm × List Step)
  | 0, .named name =>
      match environment.lookupTerm? name with
      | some ⟨_, _, some _⟩ => none
      | _ => some (.named name, [])
  | fuel + 1, .named name =>
      match environment.lookupTerm? name with
      | some ⟨_, type, some body⟩ =>
          match elaborateDelta fuel body with
          | some (result, steps) => some (result, deltaStep environment.terms name type body :: steps)
          | none => none
      | _ => some (.named name, [])
  | fuel, .app function argument =>
      match elaborateDelta fuel function, elaborateDelta fuel argument with
      | some (functionResult, functionSteps), some (argumentResult, argumentSteps) =>
          some (.app functionResult argumentResult,
            functionSteps.map ((Frame.appFunction argument).lift environment.terms) ++
              argumentSteps.map ((Frame.appArgument functionResult).lift environment.terms))
      | _, _ => none
  | fuel, .lam type body =>
      match elaborateDelta fuel body with
      | some (bodyResult, bodySteps) =>
          some (.lam type bodyResult, bodySteps.map ((Frame.lamBody type).lift environment.terms))
      | none => none
  | fuel, .imp domain codomain =>
      match elaborateDelta fuel domain, elaborateDelta fuel codomain with
      | some (domainResult, domainSteps), some (codomainResult, codomainSteps) =>
          some (.imp domainResult codomainResult,
            domainSteps.map ((Frame.impDomain codomain).lift environment.terms) ++
              codomainSteps.map ((Frame.impCodomain domainResult).lift environment.terms))
      | _, _ => none
  | fuel, .all type body =>
      match elaborateDelta fuel body with
      | some (bodyResult, bodySteps) =>
          some (.all type bodyResult, bodySteps.map ((Frame.allBody type).lift environment.terms))
      | none => none
  | fuel, .typeApp function type =>
      match elaborateDelta fuel function with
      | some (functionResult, functionSteps) =>
          some (.typeApp functionResult type,
            functionSteps.map ((Frame.typeAppFunction type).lift environment.terms))
      | none => none
  | fuel, .typeLam body =>
      match elaborateDelta fuel body with
      | some (bodyResult, bodySteps) =>
          some (.typeLam bodyResult, bodySteps.map (Frame.typeLamBody.lift environment.terms))
      | none => none
  | fuel, .typeAll body =>
      match elaborateDelta fuel body with
      | some (bodyResult, bodySteps) =>
          some (.typeAll bodyResult, bodySteps.map (Frame.typeAllBody.lift environment.terms))
      | none => none
  | _, .db index => some (.db index, [])
  | _, .prim index => some (.prim index, [])

/-- **Unfolding writes its own article.** -/
theorem elaborateDelta_spec : ∀ (fuel : Nat) (term : Tm) {result : Tm} {steps : List Step},
    elaborateDelta environment fuel term = some (result, steps) →
      deltaNormalize environment fuel term = some result ∧ Chain term steps result ∧
        ∀ step ∈ steps, step.Valid environment.terms
  | 0, .named name, result, steps, elaborated => by
      simp only [elaborateDelta] at elaborated
      split at elaborated
      · simp at elaborated
      · rename_i notDefinition
        simp only [Option.some.injEq, Prod.mk.injEq] at elaborated
        obtain ⟨rfl, rfl⟩ := elaborated
        refine ⟨?_, rfl, by simp⟩
        simp only [deltaNormalize]
  | fuel + 1, .named name, result, steps, elaborated => by
      simp only [elaborateDelta] at elaborated
      split at elaborated
      · rename_i found type body lookup
        cases bodyElaborated : elaborateDelta environment fuel body with
        | none => simp [bodyElaborated] at elaborated
        | some bodyOutput =>
          obtain ⟨bodyResult, bodySteps⟩ := bodyOutput
          simp only [bodyElaborated, Option.some.injEq, Prod.mk.injEq] at elaborated
          obtain ⟨rfl, rfl⟩ := elaborated
          obtain ⟨bodyNormal, bodyChain, bodyValid⟩ :=
            elaborateDelta_spec fuel body bodyElaborated
          refine ⟨?_, ⟨rfl, bodyChain⟩, ?_⟩
          · simp only [deltaNormalize, lookup]
            exact bodyNormal
          · intro step member
            rcases List.mem_cons.mp member with rfl | member
            · exact deltaStep_valid environment.terms lookup
            · exact bodyValid step member
      · rename_i notDefinition
        simp only [Option.some.injEq, Prod.mk.injEq] at elaborated
        obtain ⟨rfl, rfl⟩ := elaborated
        refine ⟨?_, rfl, by simp⟩
        simp only [deltaNormalize]
  | fuel, .app function argument, result, steps, elaborated => by
      cases functionElaborated : elaborateDelta environment fuel function with
      | none => simp [elaborateDelta, functionElaborated] at elaborated
      | some functionOutput =>
        obtain ⟨functionResult, functionSteps⟩ := functionOutput
        cases argumentElaborated : elaborateDelta environment fuel argument with
        | none => simp [elaborateDelta, functionElaborated, argumentElaborated] at elaborated
        | some argumentOutput =>
          obtain ⟨argumentResult, argumentSteps⟩ := argumentOutput
          obtain ⟨functionNormal, functionChain, functionValid⟩ :=
            elaborateDelta_spec fuel function functionElaborated
          obtain ⟨argumentNormal, argumentChain, argumentValid⟩ :=
            elaborateDelta_spec fuel argument argumentElaborated
          simp only [elaborateDelta, functionElaborated, argumentElaborated, Option.some.injEq,
            Prod.mk.injEq] at elaborated
          obtain ⟨rfl, rfl⟩ := elaborated
          refine ⟨?_, Chain.append
              (Frame.chain_lift environment.terms (.appFunction argument) functionChain)
              (Frame.chain_lift environment.terms (.appArgument functionResult) argumentChain),
            valid_append environment.terms
              (Frame.valid_lift environment.terms (.appFunction argument) functionValid)
              (Frame.valid_lift environment.terms (.appArgument functionResult) argumentValid)⟩
          simp [deltaNormalize, functionNormal, argumentNormal]
  | fuel, .lam type body, result, steps, elaborated => by
      cases bodyElaborated : elaborateDelta environment fuel body with
      | none => simp [elaborateDelta, bodyElaborated] at elaborated
      | some bodyOutput =>
        obtain ⟨bodyResult, bodySteps⟩ := bodyOutput
        obtain ⟨bodyNormal, bodyChain, bodyValid⟩ := elaborateDelta_spec fuel body bodyElaborated
        simp only [elaborateDelta, bodyElaborated, Option.some.injEq, Prod.mk.injEq] at elaborated
        obtain ⟨rfl, rfl⟩ := elaborated
        refine ⟨?_, Frame.chain_lift environment.terms (.lamBody type) bodyChain,
          Frame.valid_lift environment.terms (.lamBody type) bodyValid⟩
        simp [deltaNormalize, bodyNormal]
  | fuel, .imp domain codomain, result, steps, elaborated => by
      cases domainElaborated : elaborateDelta environment fuel domain with
      | none => simp [elaborateDelta, domainElaborated] at elaborated
      | some domainOutput =>
        obtain ⟨domainResult, domainSteps⟩ := domainOutput
        cases codomainElaborated : elaborateDelta environment fuel codomain with
        | none => simp [elaborateDelta, domainElaborated, codomainElaborated] at elaborated
        | some codomainOutput =>
          obtain ⟨codomainResult, codomainSteps⟩ := codomainOutput
          obtain ⟨domainNormal, domainChain, domainValid⟩ :=
            elaborateDelta_spec fuel domain domainElaborated
          obtain ⟨codomainNormal, codomainChain, codomainValid⟩ :=
            elaborateDelta_spec fuel codomain codomainElaborated
          simp only [elaborateDelta, domainElaborated, codomainElaborated, Option.some.injEq,
            Prod.mk.injEq] at elaborated
          obtain ⟨rfl, rfl⟩ := elaborated
          refine ⟨?_, Chain.append
              (Frame.chain_lift environment.terms (.impDomain codomain) domainChain)
              (Frame.chain_lift environment.terms (.impCodomain domainResult) codomainChain),
            valid_append environment.terms
              (Frame.valid_lift environment.terms (.impDomain codomain) domainValid)
              (Frame.valid_lift environment.terms (.impCodomain domainResult) codomainValid)⟩
          simp [deltaNormalize, domainNormal, codomainNormal]
  | fuel, .all type body, result, steps, elaborated => by
      cases bodyElaborated : elaborateDelta environment fuel body with
      | none => simp [elaborateDelta, bodyElaborated] at elaborated
      | some bodyOutput =>
        obtain ⟨bodyResult, bodySteps⟩ := bodyOutput
        obtain ⟨bodyNormal, bodyChain, bodyValid⟩ := elaborateDelta_spec fuel body bodyElaborated
        simp only [elaborateDelta, bodyElaborated, Option.some.injEq, Prod.mk.injEq] at elaborated
        obtain ⟨rfl, rfl⟩ := elaborated
        refine ⟨?_, Frame.chain_lift environment.terms (.allBody type) bodyChain,
          Frame.valid_lift environment.terms (.allBody type) bodyValid⟩
        simp [deltaNormalize, bodyNormal]
  | fuel, .typeApp function type, result, steps, elaborated => by
      cases functionElaborated : elaborateDelta environment fuel function with
      | none => simp [elaborateDelta, functionElaborated] at elaborated
      | some functionOutput =>
        obtain ⟨functionResult, functionSteps⟩ := functionOutput
        obtain ⟨functionNormal, functionChain, functionValid⟩ :=
          elaborateDelta_spec fuel function functionElaborated
        simp only [elaborateDelta, functionElaborated, Option.some.injEq,
          Prod.mk.injEq] at elaborated
        obtain ⟨rfl, rfl⟩ := elaborated
        refine ⟨?_, Frame.chain_lift environment.terms (.typeAppFunction type) functionChain,
          Frame.valid_lift environment.terms (.typeAppFunction type) functionValid⟩
        simp [deltaNormalize, functionNormal]
  | fuel, .typeLam body, result, steps, elaborated => by
      cases bodyElaborated : elaborateDelta environment fuel body with
      | none => simp [elaborateDelta, bodyElaborated] at elaborated
      | some bodyOutput =>
        obtain ⟨bodyResult, bodySteps⟩ := bodyOutput
        obtain ⟨bodyNormal, bodyChain, bodyValid⟩ := elaborateDelta_spec fuel body bodyElaborated
        simp only [elaborateDelta, bodyElaborated, Option.some.injEq, Prod.mk.injEq] at elaborated
        obtain ⟨rfl, rfl⟩ := elaborated
        refine ⟨?_, Frame.chain_lift environment.terms .typeLamBody bodyChain,
          Frame.valid_lift environment.terms .typeLamBody bodyValid⟩
        simp [deltaNormalize, bodyNormal]
  | fuel, .typeAll body, result, steps, elaborated => by
      cases bodyElaborated : elaborateDelta environment fuel body with
      | none => simp [elaborateDelta, bodyElaborated] at elaborated
      | some bodyOutput =>
        obtain ⟨bodyResult, bodySteps⟩ := bodyOutput
        obtain ⟨bodyNormal, bodyChain, bodyValid⟩ := elaborateDelta_spec fuel body bodyElaborated
        simp only [elaborateDelta, bodyElaborated, Option.some.injEq, Prod.mk.injEq] at elaborated
        obtain ⟨rfl, rfl⟩ := elaborated
        refine ⟨?_, Frame.chain_lift environment.terms .typeAllBody bodyChain,
          Frame.valid_lift environment.terms .typeAllBody bodyValid⟩
        simp [deltaNormalize, bodyNormal]
  | fuel, .db index, result, steps, elaborated => by
      simp only [elaborateDelta, Option.some.injEq, Prod.mk.injEq] at elaborated
      obtain ⟨rfl, rfl⟩ := elaborated
      refine ⟨?_, rfl, by simp⟩
      cases fuel <;> simp [deltaNormalize]
  | fuel, .prim index, result, steps, elaborated => by
      simp only [elaborateDelta, Option.some.injEq, Prod.mk.injEq] at elaborated
      obtain ⟨rfl, rfl⟩ := elaborated
      refine ⟨?_, rfl, by simp⟩
      cases fuel <;> simp [deltaNormalize]
termination_by fuel term => (fuel, sizeOf term)

end Delta


section DeltaComplete

variable (environment : Environment)

/-- **Unfolding always elaborates.** -/
theorem elaborateDelta_complete : ∀ (fuel : Nat) (term : Tm) {result : Tm},
    deltaNormalize environment fuel term = some result →
      ∃ steps, elaborateDelta environment fuel term = some (result, steps)
  | 0, .named name, result, normal => by
      simp only [deltaNormalize] at normal
      simp only [elaborateDelta]
      split at normal
      · simp at normal
      · rename_i notDefinition
        simp only [Option.some.injEq] at normal
        subst normal
        split
        · rename_i found type body lookup
          exact absurd lookup (notDefinition found type body)
        · exact ⟨_, rfl⟩
  | fuel + 1, .named name, result, normal => by
      simp only [deltaNormalize] at normal
      simp only [elaborateDelta]
      split at normal
      · rename_i found type body lookup
        obtain ⟨steps, bodyElaborated⟩ := elaborateDelta_complete fuel body normal
        simp only [lookup, bodyElaborated]
        exact ⟨_, rfl⟩
      · rename_i notDefinition
        simp only [Option.some.injEq] at normal
        subst normal
        split
        · rename_i found type body lookup
          exact absurd lookup (notDefinition found type body)
        · exact ⟨_, rfl⟩
  | fuel, .app function argument, result, normal => by
      simp only [deltaNormalize, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at normal
      obtain ⟨functionResult, functionNormal, argumentResult, argumentNormal, rfl⟩ := normal
      obtain ⟨functionSteps, functionElaborated⟩ :=
        elaborateDelta_complete fuel function functionNormal
      obtain ⟨argumentSteps, argumentElaborated⟩ :=
        elaborateDelta_complete fuel argument argumentNormal
      simp only [elaborateDelta, functionElaborated, argumentElaborated]
      exact ⟨_, rfl⟩
  | fuel, .lam type body, result, normal => by
      simp only [deltaNormalize, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at normal
      obtain ⟨bodyResult, bodyNormal, rfl⟩ := normal
      obtain ⟨bodySteps, bodyElaborated⟩ := elaborateDelta_complete fuel body bodyNormal
      simp only [elaborateDelta, bodyElaborated]
      exact ⟨_, rfl⟩
  | fuel, .imp domain codomain, result, normal => by
      simp only [deltaNormalize, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at normal
      obtain ⟨domainResult, domainNormal, codomainResult, codomainNormal, rfl⟩ := normal
      obtain ⟨domainSteps, domainElaborated⟩ := elaborateDelta_complete fuel domain domainNormal
      obtain ⟨codomainSteps, codomainElaborated⟩ :=
        elaborateDelta_complete fuel codomain codomainNormal
      simp only [elaborateDelta, domainElaborated, codomainElaborated]
      exact ⟨_, rfl⟩
  | fuel, .all type body, result, normal => by
      simp only [deltaNormalize, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at normal
      obtain ⟨bodyResult, bodyNormal, rfl⟩ := normal
      obtain ⟨bodySteps, bodyElaborated⟩ := elaborateDelta_complete fuel body bodyNormal
      simp only [elaborateDelta, bodyElaborated]
      exact ⟨_, rfl⟩
  | fuel, .typeApp function type, result, normal => by
      simp only [deltaNormalize, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at normal
      obtain ⟨functionResult, functionNormal, rfl⟩ := normal
      obtain ⟨functionSteps, functionElaborated⟩ :=
        elaborateDelta_complete fuel function functionNormal
      simp only [elaborateDelta, functionElaborated]
      exact ⟨_, rfl⟩
  | fuel, .typeLam body, result, normal => by
      simp only [deltaNormalize, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at normal
      obtain ⟨bodyResult, bodyNormal, rfl⟩ := normal
      obtain ⟨bodySteps, bodyElaborated⟩ := elaborateDelta_complete fuel body bodyNormal
      simp only [elaborateDelta, bodyElaborated]
      exact ⟨_, rfl⟩
  | fuel, .typeAll body, result, normal => by
      simp only [deltaNormalize, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at normal
      obtain ⟨bodyResult, bodyNormal, rfl⟩ := normal
      obtain ⟨bodySteps, bodyElaborated⟩ := elaborateDelta_complete fuel body bodyNormal
      simp only [elaborateDelta, bodyElaborated]
      exact ⟨_, rfl⟩
  | fuel, .db index, result, normal => by
      have same : result = .db index := by
        cases fuel <;> simpa [deltaNormalize, eq_comm] using normal
      subst same
      exact ⟨[], by simp [elaborateDelta]⟩
  | fuel, .prim index, result, normal => by
      have same : result = .prim index := by
        cases fuel <;> simpa [deltaNormalize, eq_comm] using normal
      subst same
      exact ⟨[], by simp [elaborateDelta]⟩
termination_by fuel term => (fuel, sizeOf term)

end DeltaComplete

/-! ## Runs -/

section Runs

variable (declarations : List TermDecl)

/-- `Tm.normalize`, writing its steps. -/
def elaborateRun : Nat → Tm → Option (Tm × List Step)
  | 0, term =>
      let ((result, stable), steps) := elaboratePass declarations term
      if stable then some (result, steps) else none
  | fuel + 1, term =>
      let ((result, stable), steps) := elaboratePass declarations term
      if stable then some (result, steps)
      else
        match elaborateRun fuel result with
        | some (final, rest) => some (final, steps ++ rest)
        | none => none

/-- **A run writes its own article.** -/
theorem elaborateRun_spec (fuel : Nat) (term : Tm) {result : Tm} {steps : List Step}
    (elaborated : elaborateRun declarations fuel term = some (result, steps)) :
    Tm.normalize fuel term = some result ∧ Chain term steps result ∧
      ∀ step ∈ steps, step.Valid declarations := by
  induction fuel generalizing term result steps with
  | zero =>
      have spec := elaboratePass_spec declarations term
      rcases passOut : elaboratePass declarations term with ⟨⟨passResult, stable⟩, passSteps⟩
      rw [passOut] at spec
      obtain ⟨passEq, passChain, passValid⟩ := spec
      dsimp only at passEq passChain passValid
      simp only [elaborateRun, passOut] at elaborated
      cases stable
      · simp at elaborated
      · simp only [if_true, Option.some.injEq, Prod.mk.injEq] at elaborated
        obtain ⟨rfl, rfl⟩ := elaborated
        refine ⟨?_, passChain, passValid⟩
        simp [Tm.normalize, ← passEq]
  | succ fuel fuelIH =>
      have spec := elaboratePass_spec declarations term
      rcases passOut : elaboratePass declarations term with ⟨⟨passResult, stable⟩, passSteps⟩
      rw [passOut] at spec
      obtain ⟨passEq, passChain, passValid⟩ := spec
      dsimp only at passEq passChain passValid
      simp only [elaborateRun, passOut] at elaborated
      cases stable
      · cases restElaborated : elaborateRun declarations fuel passResult with
        | none => simp [restElaborated] at elaborated
        | some restOutput =>
          obtain ⟨final, rest⟩ := restOutput
          simp only [Bool.false_eq_true, if_false, restElaborated, Option.some.injEq,
            Prod.mk.injEq] at elaborated
          obtain ⟨rfl, rfl⟩ := elaborated
          obtain ⟨restNormal, restChain, restValid⟩ := fuelIH passResult restElaborated
          refine ⟨?_, Chain.append passChain restChain, valid_append declarations passValid restValid⟩
          simp [Tm.normalize, ← passEq, restNormal]
      · simp only [if_true, Option.some.injEq, Prod.mk.injEq] at elaborated
        obtain ⟨rfl, rfl⟩ := elaborated
        refine ⟨?_, passChain, passValid⟩
        simp [Tm.normalize, ← passEq]

/-- **Every run of the normalizer elaborates.** -/
theorem elaborateRun_complete (fuel : Nat) (term : Tm) {result : Tm}
    (normal : Tm.normalize fuel term = some result) :
    ∃ steps, elaborateRun declarations fuel term = some (result, steps) := by
  induction fuel generalizing term with
  | zero =>
      have passEq := elaboratePass_fst declarations term
      rcases passOut : elaboratePass declarations term with ⟨⟨passResult, stable⟩, passSteps⟩
      rw [passOut] at passEq
      dsimp only at passEq
      simp only [Tm.normalize, ← passEq] at normal
      simp only [elaborateRun, passOut]
      cases stable
      · simp at normal
      · simp only [if_true, Option.some.injEq] at normal ⊢
        subst normal
        exact ⟨_, rfl⟩
  | succ fuel fuelIH =>
      have passEq := elaboratePass_fst declarations term
      rcases passOut : elaboratePass declarations term with ⟨⟨passResult, stable⟩, passSteps⟩
      rw [passOut] at passEq
      dsimp only at passEq
      simp only [Tm.normalize, ← passEq] at normal
      simp only [elaborateRun, passOut]
      cases stable
      · simp only [Bool.false_eq_true, if_false] at normal ⊢
        obtain ⟨rest, restElaborated⟩ := fuelIH passResult normal
        simp only [restElaborated]
        exact ⟨_, rfl⟩
      · simp only [if_true, Option.some.injEq] at normal ⊢
        subst normal
        exact ⟨_, rfl⟩

end Runs


/-! ## Normalization and conversion -/

section Conversion

variable (environment : Environment)

/-- Megalodon's normalization, writing its steps: unfolding, then the run of passes. -/
def elaborateNormalize (fuel : Nat) (term : Tm) : Option (Tm × List Step) :=
  match elaborateDelta environment fuel term with
  | some (unfolded, deltaSteps) =>
      match elaborateRun environment.terms fuel unfolded with
      | some (normal, runSteps) => some (normal, deltaSteps ++ runSteps)
      | none => none
  | none => none

/-- **Normalization writes its own article.** -/
theorem elaborateNormalize_spec {fuel : Nat} {term normal : Tm} {steps : List Step}
    (elaborated : elaborateNormalize environment fuel term = some (normal, steps)) :
    normalize environment fuel term = some normal ∧ Chain term steps normal ∧
      ∀ step ∈ steps, step.Valid environment.terms := by
  unfold elaborateNormalize at elaborated
  cases deltaElaborated : elaborateDelta environment fuel term with
  | none => simp [deltaElaborated] at elaborated
  | some deltaOutput =>
    obtain ⟨unfolded, deltaSteps⟩ := deltaOutput
    cases runElaborated : elaborateRun environment.terms fuel unfolded with
    | none => simp [deltaElaborated, runElaborated] at elaborated
    | some runOutput =>
      obtain ⟨final, runSteps⟩ := runOutput
      simp only [deltaElaborated, runElaborated, Option.some.injEq, Prod.mk.injEq] at elaborated
      obtain ⟨rfl, rfl⟩ := elaborated
      obtain ⟨deltaNormal, deltaChain, deltaValid⟩ :=
        elaborateDelta_spec environment fuel term deltaElaborated
      obtain ⟨runNormal, runChain, runValid⟩ :=
        elaborateRun_spec environment.terms fuel unfolded runElaborated
      refine ⟨?_, Chain.append deltaChain runChain,
        valid_append environment.terms deltaValid runValid⟩
      simp [normalize, deltaNormal, runNormal]

/-- **Every normalization elaborates.** -/
theorem elaborateNormalize_complete {fuel : Nat} {term normal : Tm}
    (normalized : normalize environment fuel term = some normal) :
    ∃ steps, elaborateNormalize environment fuel term = some (normal, steps) := by
  simp only [normalize, Option.bind_eq_bind, Option.bind_eq_some_iff] at normalized
  obtain ⟨unfolded, deltaNormal, runNormal⟩ := normalized
  obtain ⟨deltaSteps, deltaElaborated⟩ :=
    elaborateDelta_complete environment fuel term deltaNormal
  obtain ⟨runSteps, runElaborated⟩ :=
    elaborateRun_complete environment.terms fuel unfolded runNormal
  exact ⟨deltaSteps ++ runSteps, by simp [elaborateNormalize, deltaElaborated, runElaborated]⟩

/-- The conversion article for two terms: their normalization paths to a common normal form. -/
def conversionArticle (fuel : Nat) (left right : Tm) : Option RawProof :=
  match elaborateNormalize environment fuel left, elaborateNormalize environment fuel right with
  | some (leftNormal, leftSteps), some (rightNormal, rightSteps) =>
      if leftNormal = rightNormal then
        some (node "megalodon-def-conversion-common"
          [encoded environment.terms, ETm left, ETm right, ETm leftNormal]
          [pathArticle environment.terms leftNormal leftSteps,
            pathArticle environment.terms leftNormal rightSteps])
      else none
  | _, _ => none

/-- **A conversion article is accepted by the explicit calculus.** -/
theorem conversionArticle_checked {fuel : Nat} {left right : Tm} {article : RawProof}
    (built : conversionArticle environment fuel left right = some article) :
    checkRaw validated (converts (encoded environment.terms) (ETm left) (ETm right)) article =
      true := by
  unfold conversionArticle at built
  cases leftElaborated : elaborateNormalize environment fuel left with
  | none => simp [leftElaborated] at built
  | some leftOutput =>
    obtain ⟨leftNormal, leftSteps⟩ := leftOutput
    cases rightElaborated : elaborateNormalize environment fuel right with
    | none => simp [leftElaborated, rightElaborated] at built
    | some rightOutput =>
      obtain ⟨rightNormal, rightSteps⟩ := rightOutput
      simp only [leftElaborated, rightElaborated] at built
      split at built
      · rename_i same
        subst same
        simp only [Option.some.injEq] at built
        subst built
        obtain ⟨-, leftChain, leftValid⟩ := elaborateNormalize_spec environment leftElaborated
        obtain ⟨-, rightChain, rightValid⟩ := elaborateNormalize_spec environment rightElaborated
        rw [node, checkRaw_node _ (instantiate_conversionCommon environment.terms left right leftNormal),
          checkRawChildren_two, Bool.and_eq_true]
        exact ⟨pathArticle_checked environment.terms leftChain leftValid,
          pathArticle_checked environment.terms rightChain rightValid⟩
      · simp at built

/-- Megalodon's conversion test: both sides normalize within the budget, to the same term. -/
def nativeConverts (fuel : Nat) (left right : Tm) : Bool :=
  match normalize environment fuel left, normalize environment fuel right with
  | some leftNormal, some rightNormal => decide (leftNormal = rightNormal)
  | _, _ => false

theorem conversionArticle_complete {fuel : Nat} {left right : Tm}
    (converted : nativeConverts environment fuel left right = true) :
    ∃ article, conversionArticle environment fuel left right = some article := by
  unfold nativeConverts at converted
  cases leftNormalized : normalize environment fuel left with
  | none => simp [leftNormalized] at converted
  | some leftNormal =>
    cases rightNormalized : normalize environment fuel right with
    | none => simp [leftNormalized, rightNormalized] at converted
    | some rightNormal =>
      simp only [leftNormalized, rightNormalized, decide_eq_true_eq] at converted
      subst converted
      obtain ⟨leftSteps, leftElaborated⟩ :=
        elaborateNormalize_complete environment leftNormalized
      obtain ⟨rightSteps, rightElaborated⟩ :=
        elaborateNormalize_complete environment rightNormalized
      exact ⟨node "megalodon-def-conversion-common"
          [encoded environment.terms, ETm left, ETm right, ETm leftNormal]
          [pathArticle environment.terms leftNormal leftSteps,
            pathArticle environment.terms leftNormal rightSteps],
        by simp [conversionArticle, leftElaborated, rightElaborated]⟩

/-! ## The native test elaborates into the explicit calculus -/

/-- Megalodon's conversion test. The budget is the certificate. -/
def nativeChecker : Checker (ConversionClaim Tm) ℕ where
  check claim fuel := nativeConverts environment fuel claim.source claim.target

/-- The explicit calculus's conversion judgment. -/
def explicitChecker : Checker (ConversionClaim Tm) RawProof where
  check claim article :=
    checkRaw validated
      (converts (encoded environment.terms) (ETm claim.source) (ETm claim.target)) article

/-- **The modeled native conversion elaborates exactly into its explicit calculus.** The
elaborator is the normalizer, instrumented to write each step it takes. -/
def conversionElaboration : Elaboration (nativeChecker environment) (explicitChecker environment) where
  elaborate claim fuel :=
    if (nativeChecker environment).check claim fuel then
      conversionArticle environment fuel claim.source claim.target
    else none
  exact claim fuel := by
    constructor
    · intro accepted
      obtain ⟨article, built⟩ := conversionArticle_complete environment accepted
      exact ⟨article, by simp [accepted, built], conversionArticle_checked environment built⟩
    · rintro ⟨article, produced, -⟩
      by_contra rejected
      simp [rejected] at produced

/-- **Trust reduction for the modeled conversion.** Whatever the explicit calculus is sound
for, the native test is sound for, with no trust in the normalizer. -/
theorem nativeChecker_sound {Meaning : ConversionClaim Tm → Prop}
    (explicitSound : (explicitChecker environment).Sound Meaning) :
    (nativeChecker environment).Sound Meaning :=
  (conversionElaboration environment).sound explicitSound

end Conversion


/-! ## The load of a pass -/

section Load

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.TierLattice

variable (declarations : List TermDecl)

/-- Megalodon's reduction as a rewriting system: one step is a reduction that the explicit
calculus accepts. -/
def reductionGSLT : GSLT.{0} :=
  equalityGSLT Tm fun source target =>
    ∃ article, checkRaw validated
      (reduces (encoded declarations) (ETm source) (ETm target)) article = true

theorem chain_stepsIn {start finish : Tm} {steps : List Step}
    (chain : Chain start steps finish) (valid : ∀ step ∈ steps, step.Valid declarations) :
    StepsIn (reductionGSLT declarations) steps.length start finish := by
  induction steps generalizing start with
  | nil =>
      simp only [Chain] at chain
      subst chain
      exact .zero _
  | cons step steps ih =>
      obtain ⟨same, rest⟩ := chain
      subst same
      exact .succ ⟨step.article, valid step (by simp)⟩
        (ih rest (fun other member => valid other (by simp [member])))

theorem multiStep_of_stepsIn {theory : GSLT.{0}} {n : ℕ} {source target : theory.Term}
    (steps : StepsIn theory n source target) : theory.MultiStep source target := by
  induction steps with
  | zero => exact .refl _
  | succ step _ ih => exact .step step ih

theorem chain_nonempty {start finish : Tm} {steps : List Step}
    (chain : Chain start steps finish) (changed : finish ≠ start) : 0 < steps.length := by
  cases steps with
  | nil =>
      simp only [Chain] at chain
      exact absurd chain.symm changed
  | cons _ _ => simp

/-- **A pass of the normalizer is a coarse step of the reduction system.** A pass that
changes its term performs a nonempty path of explicit reductions, so it is one step of the
coarsening, and its load is the number of contractions it writes. -/
theorem elaboratePass_coarse {term : Tm} (changed : (Tm.normalizeOne term).1 ≠ term) :
    (coarsen (reductionGSLT declarations)).Step term (Tm.normalizeOne term).1 ∧
      StepsIn (reductionGSLT declarations) (elaboratePass declarations term).2.length term
        (Tm.normalizeOne term).1 := by
  obtain ⟨passEq, chain, valid⟩ := elaboratePass_spec declarations term
  rw [passEq] at chain
  have load := chain_stepsIn declarations chain valid
  exact ⟨coarse_step_of_stepsIn _ load (chain_nonempty chain changed), load⟩

/-- **A run reaches its normal form in the reduction system**, in as many steps as it
writes. -/
theorem elaborateRun_reaches {fuel : Nat} {term normal : Tm} {steps : List Step}
    (elaborated : elaborateRun declarations fuel term = some (normal, steps)) :
    StepsIn (reductionGSLT declarations) steps.length term normal ∧
      (coarsen (reductionGSLT declarations)).MultiStep term normal := by
  obtain ⟨-, chain, valid⟩ := elaborateRun_spec declarations fuel term elaborated
  have load := chain_stepsIn declarations chain valid
  exact ⟨load, (coarsen_multiStep_iff (reductionGSLT declarations) term normal).mpr
    (multiStep_of_stepsIn load)⟩

end Load

/-! ## On to MM0 -/

section MM0

open Mettapedia.Languages.MM0.Translation
open CalculusSimulation (FirstOrder FirstOrderList FirstOrderCalculus FirstOrderClaim)

/-- Megalodon's explicit calculus is first-order: its metavariables have arity zero, its
schemas are built from constructors and metavariables, it has no side conditions, and its
rule names are distinct. -/
theorem calculus_firstOrder : FirstOrderCalculus DefinitionConversionKernel.definition :=
  CalculusSimulation.firstOrderCheck_sound (by decide +kernel)

theorem firstOrder_encodeNat : ∀ value : Nat, FirstOrder (ENat value)
  | 0 => .apply .nil
  | value + 1 => .apply (.cons (firstOrder_encodeNat value) .nil)

theorem firstOrder_encodeTp : ∀ type : Tp, FirstOrder (ETp type)
  | .var index => .apply (.cons (firstOrder_encodeNat index) .nil)
  | .prop => .apply .nil
  | .base index => .apply (.cons (firstOrder_encodeNat index) .nil)
  | .arr domain codomain =>
      .apply (.cons (firstOrder_encodeTp domain) (.cons (firstOrder_encodeTp codomain) .nil))
  | .all body => .apply (.cons (firstOrder_encodeTp body) .nil)

theorem firstOrder_encodeTm : ∀ term : Tm, FirstOrder (ETm term)
  | .db index => .apply (.cons (firstOrder_encodeNat index) .nil)
  | .named _ => .apply (.cons (.apply .nil) .nil)
  | .prim index => .apply (.cons (firstOrder_encodeNat index) .nil)
  | .app function argument =>
      .apply (.cons (firstOrder_encodeTm function) (.cons (firstOrder_encodeTm argument) .nil))
  | .lam type body =>
      .apply (.cons (firstOrder_encodeTp type) (.cons (firstOrder_encodeTm body) .nil))
  | .imp domain codomain =>
      .apply (.cons (firstOrder_encodeTm domain) (.cons (firstOrder_encodeTm codomain) .nil))
  | .all type body =>
      .apply (.cons (firstOrder_encodeTp type) (.cons (firstOrder_encodeTm body) .nil))
  | .typeApp function type =>
      .apply (.cons (firstOrder_encodeTm function) (.cons (firstOrder_encodeTp type) .nil))
  | .typeLam body => .apply (.cons (firstOrder_encodeTm body) .nil)
  | .typeAll body => .apply (.cons (firstOrder_encodeTm body) .nil)

theorem firstOrder_encoded : ∀ declarations : List TermDecl, FirstOrder (encoded declarations)
  | [] => .apply .nil
  | ⟨_, type, none⟩ :: rest =>
      .apply (.cons (.apply .nil) (.cons (firstOrder_encodeTp type)
        (.cons (firstOrder_encoded rest) .nil)))
  | ⟨_, type, some body⟩ :: rest =>
      .apply (.cons (.apply .nil) (.cons (firstOrder_encodeTp type)
        (.cons (firstOrder_encodeTm body) (.cons (firstOrder_encoded rest) .nil))))

/-- A conversion of Megalodon terms, as a claim of the explicit calculus. -/
def conversionClaim (environment : Environment) (claim : ConversionClaim Tm) : FirstOrderClaim :=
  ⟨converts (encoded environment.terms) (ETm claim.source) (ETm claim.target),
    .apply (.cons (.apply (.cons (firstOrder_encoded environment.terms)
        (.cons (firstOrder_encodeTm claim.source) .nil)))
      (.cons (.apply (.cons (firstOrder_encoded environment.terms)
        (.cons (firstOrder_encodeTm claim.target) .nil))) .nil))⟩

/-- **MM0 and Megalodon's explicit calculus p-simulate each other.** -/
def mm0Equivalent :
    PSimulation (CalculusSimulation.mm0Checker (definition := validated) calculus_firstOrder)
        (CalculusSimulation.calculusChecker (definition := validated) calculus_firstOrder) ×
      PSimulation (CalculusSimulation.calculusChecker (definition := validated) calculus_firstOrder)
        (CalculusSimulation.mm0Checker (definition := validated) calculus_firstOrder) :=
  CalculusSimulation.pEquivalent calculus_firstOrder

/-- **Megalodon's conversion reaches MM0.** A conversion the native test accepts elaborates
into an article of the explicit calculus, and the article translates into an MM0 witness
that the MM0 kernel accepts for the rendered claim. -/
theorem native_mm0 (environment : Environment) (claim : ConversionClaim Tm) (fuel : ℕ)
    (accepted : (nativeChecker environment).check claim fuel = true) :
    ∃ article witness,
      (conversionElaboration environment).elaborate claim fuel = some article ∧
        (mm0Equivalent.1).translate (conversionClaim environment claim) article = witness ∧
          (CalculusSimulation.mm0Checker (definition := validated) calculus_firstOrder).check
            (conversionClaim environment claim) witness = true := by
  obtain ⟨article, produced, explicitAccepted⟩ :=
    ((conversionElaboration environment).exact claim fuel).mp accepted
  exact ⟨article, _, produced, rfl, mm0Equivalent.1.preserves _ article explicitAccepted⟩

end MM0


/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.MM0.Translation

/-- `idp` is the identity on propositions and `p` a proposition, as in the Megalodon document
proving `idp p → p`. -/
abbrev environment : Environment := MathdataKernel.definitionConversionEnvironment

/-- Delta then beta: `idp p` converts to `p`. -/
def unfolds : ConversionClaim Tm := ⟨.app (.named "idp") (.named "p"), .named "p"⟩

theorem unfolds_native : (nativeChecker environment).check unfolds 16 = true := by
  simp [nativeChecker, nativeConverts, unfolds, MathdataKernel.definitionConversionEnvironment,
    normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Environment.lookupTerm?,
    lookupTermList?, Tm.instantiate, Tm.instantiateAt, Tm.shift]

/-- Its article is accepted by the explicit calculus, and its MM0 witness by the MM0 kernel. -/
example : ∃ article witness,
    (conversionElaboration environment).elaborate unfolds 16 = some article ∧
      (mm0Equivalent.1).translate (conversionClaim environment unfolds) article = witness ∧
        (CalculusSimulation.mm0Checker (definition := validated) calculus_firstOrder).check
          (conversionClaim environment unfolds) witness = true :=
  native_mm0 environment unfolds 16 unfolds_native

/-- `idp` and `p` have different normal forms: the test fails and nothing is elaborated. -/
def different : ConversionClaim Tm := ⟨.named "idp", .named "p"⟩

theorem different_rejected : (nativeChecker environment).check different 16 = false := by
  simp [nativeChecker, nativeConverts, different, MathdataKernel.definitionConversionEnvironment,
    normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Environment.lookupTerm?,
    lookupTermList?]

example : (conversionElaboration environment).elaborate different 16 = none := by
  simp [conversionElaboration, different_rejected]

/-- With a budget of zero, the unfolding of `idp` fails: Megalodon rejects for want of
resources, and nothing is elaborated. -/
theorem unfolds_budget_zero : (nativeChecker environment).check unfolds 0 = false := by
  simp [nativeChecker, nativeConverts, unfolds, MathdataKernel.definitionConversionEnvironment,
    normalize, deltaNormalize, Environment.lookupTerm?, lookupTermList?]

/-- A parameter `f` from propositions to propositions. -/
def etaEnvironment : Environment := { terms := [{ name := "f", type := .arr .prop .prop }] }

/-- Eta: `fun x => f x` converts to `f`. -/
def etaClaim : ConversionClaim Tm := ⟨.lam .prop (.app (.named "f") (.db 0)), .named "f"⟩

theorem eta_native : (nativeChecker etaEnvironment).check etaClaim 4 = true := by
  simp [nativeChecker, nativeConverts, etaClaim, etaEnvironment, normalize, deltaNormalize,
    Tm.normalize, Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?, Tm.dropAt?]

/-- Eta does not contract when the function uses the bound variable. -/
theorem eta_bound_rejected :
    (nativeChecker etaEnvironment).check
      ⟨.lam .prop (.app (.app (.named "f") (.db 0)) (.db 0)), .app (.named "f") (.db 0)⟩ 4 =
        false := by
  simp [nativeChecker, nativeConverts, etaEnvironment, normalize, deltaNormalize, Tm.normalize,
    Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?, Tm.dropAt?]

/-- Type-level beta: the polymorphic identity at `prop` converts to the identity on `prop`. -/
def typeBetaClaim : ConversionClaim Tm :=
  ⟨.typeApp (.typeLam (.lam (.var 0) (.db 0))) .prop, .lam .prop (.db 0)⟩

theorem typeBeta_native : (nativeChecker environment).check typeBetaClaim 4 = true := by
  simp [nativeChecker, nativeConverts, typeBetaClaim, MathdataKernel.definitionConversionEnvironment,
    normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.typeInstantiate,
    Tm.typeInstantiateAt, Tp.instantiateAt, Tp.shift]

/-- A polymorphic constant `c`. -/
def typeEtaEnvironment : Environment :=
  { terms := [{ name := "c", type := .all (.arr (.var 0) .prop) }] }

/-- Type-level eta: `fun A => c A` converts to `c`. -/
def typeEtaClaim : ConversionClaim Tm := ⟨.typeLam (.typeApp (.named "c") (.var 0)), .named "c"⟩

theorem typeEta_native : (nativeChecker typeEtaEnvironment).check typeEtaClaim 4 = true := by
  simp [nativeChecker, nativeConverts, typeEtaClaim, typeEtaEnvironment, normalize,
    deltaNormalize, Tm.normalize, Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?,
    Tm.typeDropAt?]

/-- Its article is accepted by the explicit calculus, and its MM0 witness by the MM0 kernel. -/
example : ∃ article witness,
    (conversionElaboration typeEtaEnvironment).elaborate typeEtaClaim 4 = some article ∧
      (mm0Equivalent.1).translate (conversionClaim typeEtaEnvironment typeEtaClaim) article =
        witness ∧
        (CalculusSimulation.mm0Checker (definition := validated) calculus_firstOrder).check
          (conversionClaim typeEtaEnvironment typeEtaClaim) witness = true :=
  native_mm0 typeEtaEnvironment typeEtaClaim 4 typeEta_native

/-- Type-level eta does not contract when the function uses the bound type variable. -/
theorem typeEta_bound_rejected :
    (nativeChecker typeEtaEnvironment).check
      ⟨.typeLam (.typeApp (.typeApp (.named "c") (.var 0)) (.var 0)),
        .typeApp (.named "c") (.var 0)⟩ 4 = false := by
  simp [nativeChecker, nativeConverts, typeEtaEnvironment, normalize, deltaNormalize,
    Tm.normalize, Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?, Tm.typeDropAt?,
    Tp.dropAt?]

end Controls

end Mettapedia.Languages.Megalodon.ConversionElaboration
