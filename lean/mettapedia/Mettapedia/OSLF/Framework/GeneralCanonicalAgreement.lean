import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderRootComparison
import Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalCertificate

/-!
# The general typed semantics agrees with the canonical one at the root

Two semantics give meaning to a MeTTaIL language. The canonical one,
`TypeSynthesis.langGSLTUsing`, is the relation used by `langOSLF` and the IR
passes. The general one, `GeneralOccurrenceSemantics.gslt`, runs admitted plans
over typed sites; the compiled MeTTa execution and the native types use it.

This module proves that they relate the same terms for every language whose
rules are unconditional first-order rows applied at the root, without
equations, on every well-sorted source. The hypotheses form one decidable
check, `checkRootProfile`, so a concrete language discharges them by
computation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.Match MeTTaIL.MatchSpec MeTTaIL.RuleBinding
open MeTTaIL.GeneralExecutionAdmission MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open MeTTaIL.GeneralTypedSites
open MeTTaIL.NonrecursiveReduction (rootReducts step_iff_mem_rootReducts isUnconditionalAligned)

variable (language : LanguageDef) (type : TypeExpr)

/-- The plan that runs every authored rule at the root, with no free names, over
a provider snapshot (empty unless given). -/
def rootPlan (provider : GeneralPremise.ProviderSnapshot := { signatures := [], rows := [] }) : Plan :=
  compile ⟨language, [], provider⟩ {sites := .rootOnly}

/-- The environment in which that plan executes. -/
def environment (provider : GeneralPremise.ProviderSnapshot := { signatures := [], rows := [] }) : GeneralPremise.Environment :=
  GeneralPlanEnvironment.environment (rootPlan language provider)

/-- A rule's two sides, the only parts of a rule that root reduction reads. -/
def sides (rule : RewriteRule) : Pattern × Pattern := (rule.left, rule.right)

/-- One executed row: the plan records the inferred binding specification, the
row is admitted and first-order, and both sides have the sort. -/
def checkRow (entry : RewriteRule × Nat) : Bool :=
  GeneralPremise.specification? (environment language) entry.2 ==
      some (GeneralRuleBindingInference.inferredSpec entry.1) &&
    admittedFor entry.1 (GeneralRuleBindingInference.inferredSpec entry.1) &&
    checkRuleShape entry.1 &&
    checkHasType (environment language).language (FreeTypeContext.ofList entry.1.typeContext) []
      entry.1.left type &&
    checkHasType (environment language).language (FreeTypeContext.ofList entry.1.typeContext) []
      entry.1.right type

/-- The root profile: the executed language is valid, the authored rules are
unconditional, there are no equations, the plan executes every authored rule
with its sides unchanged, and every executed row passes `checkRow`. -/
def checkRootProfile : Bool :=
  (environment language).language.validate.isEmpty &&
    isUnconditionalAligned language &&
    language.isEquationFree &&
    (rootPlan language).equations.isEmpty &&
    ((environment language).language.rewrites.map sides == language.rewrites.map sides) &&
    (environment language).language.rewrites.zipIdx.all (checkRow language type)

section Profile

variable {language type}

structure RootProfile (language : LanguageDef) (type : TypeExpr) : Prop where
  valid : (environment language).language.validate = []
  unconditional : isUnconditionalAligned language = true
  equationFree : language.isEquationFree = true
  equations : (rootPlan language).equations = []
  sides : (environment language).language.rewrites.map sides = language.rewrites.map sides
  rows : (environment language).language.rewrites.zipIdx.all (checkRow language type) = true

theorem RootProfile.of_check (checked : checkRootProfile language type = true) :
    RootProfile language type := by
  simp only [checkRootProfile, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at checked
  obtain ⟨⟨⟨⟨⟨valid, unconditional⟩, equationFree⟩, equations⟩, sides⟩, rows⟩ := checked
  exact ⟨valid, unconditional, equationFree, equations, sides, rows⟩

theorem RootProfile.row (profile : RootProfile language type) {index : Nat} {rule : RewriteRule}
    (declared : (environment language).language.rewrites[index]? = some rule) :
    GeneralPremise.specification? (environment language) index =
        some (GeneralRuleBindingInference.inferredSpec rule) ∧
      admittedFor rule (GeneralRuleBindingInference.inferredSpec rule) = true ∧
      checkRuleShape rule = true ∧
      HasType (environment language).language (FreeTypeContext.ofList rule.typeContext) [] rule.left type ∧
      HasType (environment language).language (FreeTypeContext.ofList rule.typeContext) [] rule.right type := by
  have checked := List.all_eq_true.mp profile.rows (rule, index)
    (List.mk_mem_zipIdx_iff_getElem?.mpr declared)
  simp only [checkRow, Bool.and_eq_true, beq_iff_eq] at checked
  exact ⟨checked.1.1.1.1, checked.1.1.1.2, checked.1.1.2,
    checkHasType_sound checked.1.2, checkHasType_sound checked.2⟩

/-- Root reduction reads only rule sides. -/
theorem rootReducts_eq_of_sides {first second : LanguageDef}
    (same : first.rewrites.map sides = second.rewrites.map sides) (source : Pattern) :
    rootReducts first source = rootReducts second source := by
  have expand : ∀ language : LanguageDef, rootReducts language source =
      (language.rewrites.map sides).flatMap fun pair =>
        (matchPattern pair.1 source).map fun bindings => applyBindings bindings pair.2 := by
    intro language
    simp only [rootReducts, List.flatMap_map, sides]
  rw [expand first, expand second, same]

theorem RootProfile.root_reducts (profile : RootProfile language type) (source : Pattern) :
    rootReducts (environment language).language source = rootReducts language source :=
  rootReducts_eq_of_sides profile.sides source

theorem rootOnly_site {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed language free .rootOnly bound type source site) :
    site = SiteData.here bound type source := by
  cases licensed <;> simp_all [OperationalPermissions.rootOnly]

theorem RootProfile.primitive_to_original (profile : RootProfile language type)
    (bound : List TypeExpr) {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid (rootPlan language) bound type source) :
    receipt.target ∈ rootReducts language source := by
  have site := rootOnly_site valid.1.2
  have declared : (environment language).language.rewrites[receipt.job.ordinal]? =
      some receipt.job.declaration.rule :=
    GeneralRuleJobs.Job.selected_rule valid.1
  obtain ⟨specified, _, shape, _, _⟩ := profile.row declared
  have firing : GeneralPremise.RootFiring (environment language) bound type source
      receipt.job.ordinal receipt.matcherTrace receipt.captured receipt.completed
      receipt.premiseHistory receipt.localTarget := by
    simpa only [site, SiteData.here, environment, GeneralPlanEnvironment.environmentWith_empty] using valid.2.1
  obtain ⟨bindings, matched, endpoint⟩ := rootFiring_readout declared specified shape firing
  have same : receipt.target = receipt.localTarget := by
    simpa only [site, SiteData.here, DerivedContexts.OneHoleContext.fill] using valid.2.2.2.1
  rw [same, ← profile.root_reducts source]
  exact List.mem_flatMap.mpr ⟨receipt.job.declaration.rule, List.mem_of_getElem? declared,
    List.mem_map.mpr ⟨bindings, matchRel_complete matched, endpoint⟩⟩

theorem RootProfile.original_to_primitive (profile : RootProfile language type)
    (bound : List TypeExpr) {source target : Pattern}
    (typed : OpenPatternWellSorted (rootPlan language).snapshot.language
      (rootPlan language).snapshot.free bound type source)
    (member : target ∈ rootReducts language source) :
    ∃ receipt : GeneralRuleJobs.Receipt,
      receipt.Valid (rootPlan language) bound type source ∧ receipt.target = target := by
  rw [← profile.root_reducts source] at member
  obtain ⟨rule, declaredMember, reductMember⟩ := List.mem_flatMap.mp member
  obtain ⟨bindings, matching, endpoint⟩ := List.mem_map.mp reductMember
  obtain ⟨index, declared⟩ := List.mem_iff_getElem?.mp declaredMember
  have selected : ∃ declaration, (rootPlan language).rules[index]? = some declaration ∧
      declaration.rule = rule := by
    have row : ((rootPlan language).rules.map RulePlan.rule)[index]? = some rule := declared
    simp only [List.getElem?_map, Option.map_eq_some_iff] at row
    exact row
  obtain ⟨declaration, selected, _⟩ := selected
  obtain ⟨specified, admitted, shape, leftTyped, rightTyped⟩ := profile.row declared
  have sourceTyped : OpenPatternWellSorted (environment language).language
      (environment language).free bound type source :=
    (GeneralPlanEnvironment.typing_iff (rootPlan language) bound type source).mpr typed
  obtain ⟨trace, captured, firing⟩ := rootFiring_construct profile.valid declared specified admitted
    shape leftTyped rightTyped sourceTyped (matchPattern_sound matching) endpoint
  let job : GeneralRuleJobs.Job := ⟨index, declaration, SiteData.here bound type source⟩
  have jobValid : job.Valid (rootPlan language) bound type source :=
    ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, .here rfl sourceTyped.2.2.1 sourceTyped.1⟩
  let receipt : GeneralRuleJobs.Receipt := ⟨job, trace, captured, captured, [], target, target⟩
  refine ⟨receipt, ⟨jobValid, firing, rfl, rfl, ?_⟩, rfl⟩
  cases firing with
  | fire _ _ _ _ _ _ _ _ sorted => exact sorted

theorem RootProfile.equivalence_is_equality (profile : RootProfile language type)
    (bound : List TypeExpr) {first second : Pattern}
    (equivalent : (GeneralOccurrenceSemantics.gslt (rootPlan language) bound type).Equiv first second) :
    first = second :=
  GeneralOccurrenceFrontier.LocalEquationFree.equation_equivalence_is_equality
    (request := ⟨rootPlan language, bound, type, first⟩) profile.equations equivalent

/-- The general step from a well-sorted source is root reduction. -/
theorem RootProfile.general_step_iff_rootReducts (profile : RootProfile language type)
    (bound : List TypeExpr) {source target : Pattern}
    (typed : OpenPatternWellSorted (rootPlan language).snapshot.language
      (rootPlan language).snapshot.free bound type source) :
    (GeneralOccurrenceSemantics.gslt (rootPlan language) bound type).Step source target ↔
      target ∈ rootReducts language source := by
  constructor
  · rintro ⟨representative, receipt, before, fired, after⟩
    have sourceSame := profile.equivalence_is_equality bound before
    have targetSame := profile.equivalence_is_equality bound after
    subst representative
    rw [← targetSame]
    exact profile.primitive_to_original bound fired
  · intro original
    obtain ⟨receipt, fired, endpoint⟩ := profile.original_to_primitive bound typed original
    exact ⟨source, receipt, .refl source, fired, endpoint ▸ Relation.EqvGen.refl receipt.target⟩

/-- **Agreement.** For a language with the root profile, the general step from a
well-sorted source is the canonical step, in every relation environment. -/
theorem RootProfile.general_step_iff_canonical (profile : RootProfile language type)
    (relEnv : Engine.RelationEnv) (bound : List TypeExpr) {source target : Pattern}
    (typed : OpenPatternWellSorted (rootPlan language).snapshot.language
      (rootPlan language).snapshot.free bound type source) :
    (GeneralOccurrenceSemantics.gslt (rootPlan language) bound type).Step source target ↔
      (TypeSynthesis.langGSLTUsing relEnv language).Step source target :=
  (profile.general_step_iff_rootReducts bound typed).trans
    ((step_iff_mem_rootReducts (ContextualStep.engineBasePremises relEnv) language
        profile.unconditional source target).symm.trans
      (TypeSynthesis.langSemanticReducesUsing_iff_langReducesUsing_of_equation_free relEnv
        profile.equationFree source target).symm)

end Profile

end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
