import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderRootComparison
import Mettapedia.Languages.PartrecMachine.Adequacy

open Mettapedia.OSLF.Framework

/-!
# Original Partrec reduction and the generated typed native engine

The comparison retains the original nineteen authored declarations. Scoped
metadata is inferred from those rows and read back through independently
proved first-order matching laws. The theorem concerns every admitted open
configuration, rather than a selected list of runtime examples.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Partrec.Comparison

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.Match MeTTaIL.MatchSpec MeTTaIL.RuleBinding
open MeTTaIL.GeneralExecutionAdmission MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend

 def environment : GeneralPremise.Environment := GeneralPlanEnvironment.environment plan

 theorem environment_valid : environment.language.validate = [] := by
  cbv

 def annotate (rule : RewriteRule) : RewriteRule :=
  {rule with bindings := some (GeneralRuleBindingInference.inferredSpec rule)}

 theorem environment_authored_rows :
    environment.language.rewrites = Mettapedia.Languages.PartrecMachine.partrecMachine.rewrites.map annotate := by
  cbv

 theorem checked_rows : environment.language.rewrites.zipIdx.all (fun entry =>
    GeneralPremise.specification? environment entry.2 ==
      some (GeneralRuleBindingInference.inferredSpec entry.1) &&
    admittedFor entry.1 (GeneralRuleBindingInference.inferredSpec entry.1) &&
    checkRuleShape entry.1 &&
    checkHasType environment.language (FreeTypeContext.ofList entry.1.typeContext) [] entry.1.left (.base "Cfg") &&
    checkHasType environment.language (FreeTypeContext.ofList entry.1.typeContext) [] entry.1.right (.base "Cfg")) = true := by
  cbv

 theorem row_properties {index : Nat} {rule : RewriteRule}
    (declared : environment.language.rewrites[index]? = some rule) :
    GeneralPremise.specification? environment index = some (GeneralRuleBindingInference.inferredSpec rule) ∧
    admittedFor rule (GeneralRuleBindingInference.inferredSpec rule) = true ∧
    checkRuleShape rule = true ∧
    HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.left (.base "Cfg") ∧
    HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.right (.base "Cfg") := by
  have checked := List.all_eq_true.mp checked_rows (rule, index)
    (List.mk_mem_zipIdx_iff_getElem?.mpr declared)
  simp only [Bool.and_eq_true, beq_iff_eq] at checked
  exact ⟨checked.1.1.1.1, checked.1.1.1.2, checked.1.1.2,
    checkHasType_sound checked.1.2, checkHasType_sound checked.2⟩

 theorem rootOnly_site {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed language free .rootOnly bound type source site) :
    site = SiteData.here bound type source := by
  cases licensed <;> simp_all [OperationalPermissions.rootOnly]

 theorem original_root_reducts (source : Pattern) :
    NonrecursiveReduction.rootReducts environment.language source =
      NonrecursiveReduction.rootReducts Mettapedia.Languages.PartrecMachine.partrecMachine source := by
  simp only [NonrecursiveReduction.rootReducts, environment_authored_rows, List.flatMap_map,
    annotate]

 theorem primitive_to_original (bound : List TypeExpr) {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan bound (.base "Cfg") source) :
    receipt.target ∈ NonrecursiveReduction.rootReducts Mettapedia.Languages.PartrecMachine.partrecMachine source := by
  have site := rootOnly_site valid.1.2
  have declared : environment.language.rewrites[receipt.job.ordinal]? = some receipt.job.declaration.rule :=
    GeneralRuleJobs.Job.selected_rule valid.1
  obtain ⟨specified, _, shape, _, _⟩ := row_properties declared
  have firing : GeneralPremise.RootFiring environment bound (.base "Cfg") source receipt.job.ordinal
      receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget := by
    simpa only [site, SiteData.here, environment, GeneralPlanEnvironment.environmentWith_empty] using valid.2.1
  obtain ⟨bindings, matched, endpoint⟩ := rootFiring_readout declared specified shape firing
  have same : receipt.target = receipt.localTarget := by
    simpa only [site, SiteData.here, DerivedContexts.OneHoleContext.fill] using valid.2.2.2.1
  rw [same, ← original_root_reducts source]
  exact List.mem_flatMap.mpr ⟨receipt.job.declaration.rule, List.mem_of_getElem? declared,
    List.mem_map.mpr ⟨bindings, matchRel_complete matched, endpoint⟩⟩

 theorem original_to_primitive (bound : List TypeExpr) {source target : Pattern}
    (typed : Source bound source)
    (member : target ∈ NonrecursiveReduction.rootReducts
      Mettapedia.Languages.PartrecMachine.partrecMachine source) :
    ∃ receipt : GeneralRuleJobs.Receipt,
      receipt.Valid plan bound (.base "Cfg") source ∧ receipt.target = target := by
  rw [← original_root_reducts source] at member
  obtain ⟨rule, declaredMember, reductMember⟩ := List.mem_flatMap.mp member
  obtain ⟨bindings, matching, endpoint⟩ := List.mem_map.mp reductMember
  obtain ⟨index, declared⟩ := List.mem_iff_getElem?.mp declaredMember
  have selected : ∃ declaration, plan.rules[index]? = some declaration ∧ declaration.rule = rule := by
    have row : (plan.rules.map RulePlan.rule)[index]? = some rule := declared
    simp only [List.getElem?_map, Option.map_eq_some_iff] at row
    exact row
  obtain ⟨declaration, selected, ruleSame⟩ := selected
  obtain ⟨specified, admitted, shape, leftTyped, rightTyped⟩ := row_properties declared
  have sourceTyped : OpenPatternWellSorted environment.language environment.free bound (.base "Cfg") source :=
    (GeneralPlanEnvironment.typing_iff plan bound (.base "Cfg") source).mpr typed
  obtain ⟨trace, captured, firing⟩ := rootFiring_construct environment_valid declared specified admitted shape
    leftTyped rightTyped sourceTyped (matchPattern_sound matching) endpoint
  let job : GeneralRuleJobs.Job := ⟨index, declaration, SiteData.here bound (.base "Cfg") source⟩
  have jobValid : job.Valid plan bound (.base "Cfg") source := by
    exact ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, .here rfl sourceTyped.2.2.1 sourceTyped.1⟩
  let receipt : GeneralRuleJobs.Receipt := ⟨job, trace, captured, captured, [], target, target⟩
  refine ⟨receipt, ?_, rfl⟩
  refine ⟨jobValid, ?_, ?_, rfl, ?_⟩
  · exact firing
  · rfl
  · have sorted : OpenPatternWellSorted environment.language environment.free bound (.base "Cfg") target := by
      cases firing with
      | fire _ _ _ _ _ _ _ _ sorted => exact sorted
    exact sorted

 theorem generated_equivalence_is_equality (bound : List TypeExpr) {first second : Pattern}
    (equivalent : (theory bound).Equiv first second) : first = second :=
  GeneralOccurrenceFrontier.LocalEquationFree.equation_equivalence_is_equality
    (request := request bound first) plan_equations equivalent

 theorem generated_step_iff_original (bound : List TypeExpr) {source target : Pattern}
    (typed : Source bound source) :
    (theory bound).Step source target ↔ Mettapedia.Languages.PartrecMachine.Reduces source target := by
  rw [Mettapedia.Languages.PartrecMachine.reduces_iff_mem_rootReducts]
  constructor
  · rintro ⟨representative, receipt, before, fired, after⟩
    have sourceSame := generated_equivalence_is_equality bound before
    have targetSame := generated_equivalence_is_equality bound after
    subst representative
    rw [← targetSame]
    exact primitive_to_original bound fired
  · intro original
    obtain ⟨receipt, fired, endpoint⟩ := original_to_primitive bound typed original
    exact ⟨source, receipt, .refl source, fired, endpoint ▸ Relation.EqvGen.refl receipt.target⟩

 theorem generated_step_iff_original_gslt (bound : List TypeExpr) {source target : Pattern}
    (typed : Source bound source) :
    (theory bound).Step source target ↔
      (TypeSynthesis.langGSLT Mettapedia.Languages.PartrecMachine.partrecMachine).Step source target :=
  (generated_step_iff_original bound typed).trans
    (Mettapedia.Languages.PartrecMachine.reduces_iff_generatedStep source target)

 theorem original_target_admitted (bound : List TypeExpr) {source target : Pattern}
    (typed : Source bound source) (step : Mettapedia.Languages.PartrecMachine.Reduces source target) :
    Source bound target := by
  obtain ⟨receipt, valid, same⟩ := original_to_primitive bound typed
    (Mettapedia.Languages.PartrecMachine.reduces_iff_mem_rootReducts.mp step)
  rw [← same]
  exact (GeneralPlanEnvironment.typing_iff plan bound (.base "Cfg") receipt.target).mp valid.2.2.2.2

 theorem frontier_targets_exactly_original (bound : List TypeExpr) (source : Pattern)
    (typed : Source bound source) (target : Pattern) :
    (∃ receipt ∈ (backend bound).frontier ((backend bound).completionBudget source) source,
      (backend bound).target source receipt = target) ↔
      Mettapedia.Languages.PartrecMachine.Reduces source target := by
  constructor
  · rintro ⟨receipt, listed, endpoint⟩
    rw [← endpoint]
    exact (generated_step_iff_original bound typed).mp ((backend bound).sound _ _ receipt listed)
  · intro original
    obtain ⟨receipt, listed, equivalent⟩ := whole_profile_successor_coverage bound _ source
      (whole_profile_complete bound source typed) target ((generated_step_iff_original bound typed).mpr original)
    exact ⟨receipt, listed, (generated_equivalence_is_equality bound equivalent).symm⟩

end Mettapedia.OSLF.NativeTypes.Instances.Partrec.Comparison
