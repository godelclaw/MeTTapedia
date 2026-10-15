import Mettapedia.OSLF.MeTTaIL.StructuralDescentAuthoredPlans
import Mettapedia.OSLF.MeTTaIL.StructuralDescentAuthoredOrigins
import Mettapedia.OSLF.MeTTaIL.StructuralDescentBindingMetadata

/-!
# Complete receipt comparison with original scoped source declarations

Authored binding profiles retain their original environments. For declarations
with omitted root binding annotations, the premise-free comparison uses the
original source schemas, grammar, typed captures and exact RHS instance.
It does not equate the annotated runtime language with the original source.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.SourceReadout

open Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise GeneralExecutionAdmission ScopedRuleMatching RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Independent original-source firing. Premise-free declarations retain the
matched assignment unchanged and have no premise events. -/
inductive PremiseFreeFiring (snapshot : Snapshot) (reflection : Reflection.ReflectionProfile)
    (spec : RuleBindingSpec) : List TypeExpr → TypeExpr → Pattern → Nat →
      List GeneralScopedMatchMachine.BagChoice → Assignment → Pattern → Prop where
  | fire {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
      {rule : RewriteRule} {trace : List GeneralScopedMatchMachine.BagChoice} {captured : Assignment} :
      snapshot.language.rewrites[index]? = some rule →
      rule.premises = [] →
      admittedFor rule spec = true →
      OpenPatternWellSorted snapshot.language snapshot.free bound type source →
      GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 []
        rule.left source trace captured →
      ConditionalEquationExecution.AssignmentTyped snapshot.language snapshot.free bound rule spec captured →
      ConditionalEquationExecution.AssignmentObjects captured →
      reductWith? (ScopedReflectiveExecution.binderOperation reflection rule)
        rule spec bound.length captured = some target →
      OpenPatternWellSorted snapshot.language snapshot.free bound type target →
      PremiseFreeFiring snapshot reflection spec bound type source index trace captured target

private theorem typed_assignment (plan : GeneralExecutionAdmission.Plan) (declaration : RulePlan)
    (implicitTypes : declaration.binding.implicitTypes = []) (bound : List TypeExpr)
    (assignment : Assignment) :
    ConditionalEquationExecution.AssignmentTyped (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free bound declaration.rule declaration.binding.spec assignment ↔
    ConditionalEquationExecution.AssignmentTyped plan.snapshot.language plan.snapshot.free bound
      declaration.authored declaration.binding.spec assignment := by
  have context : declaration.rule.typeContext = declaration.authored.typeContext := by
    simp only [RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate, implicitTypes, List.append_nil]
  constructor
  · intro typed name value present
    obtain ⟨dependencies, expected, specified, declared, dependencyEq, ambientEq, sorted⟩ := typed name value present
    exact ⟨dependencies, expected, specified, context ▸ declared, dependencyEq, ambientEq,
      GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar plan) sorted⟩
  · intro typed name value present
    obtain ⟨dependencies, expected, specified, declared, dependencyEq, ambientEq, sorted⟩ := typed name value present
    exact ⟨dependencies, expected, specified, context.symm ▸ declared, dependencyEq, ambientEq,
      GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar plan).symm sorted⟩

/-- Both directions compare complete occurrences at the selected declaration,
including trace, original index, captured assignment, exact target and the
absence of fabricated premise events. -/
theorem premise_free_root_iff (snapshot : Snapshot) (permissions : Permissions)
    (ordinal : Nat) (declaration : RulePlan)
    (position : (Plan.compile snapshot permissions).rules[ordinal]? = some declaration)
    (implicitTypes : declaration.binding.implicitTypes = [])
    (noPremises : declaration.authored.premises = [])
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List Event) (target : Pattern) :
    RootFiring (GeneralPlanEnvironment.environment (Plan.compile snapshot permissions))
      bound type source ordinal trace captured completed history target ↔
    PremiseFreeFiring snapshot permissions.reflection declaration.binding.spec
      bound type source declaration.declarationIndex trace captured target ∧
      completed = captured ∧ history = [] := by
  let plan := Plan.compile snapshot permissions
  have saved : plan.snapshot = snapshot := by
    exact Plan.snapshot_preserved (GeneralExecutionAdmission.compile snapshot permissions)
  have permissionsSaved : plan.permissions = permissions := by
    exact Plan.permissions_preserved (GeneralExecutionAdmission.compile snapshot permissions)
  have elaborated : declaration.rule = BindingMetadata.annotate declaration.authored (some declaration.binding.spec) := by
    simp only [RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate,
      BindingMetadata.annotate, implicitTypes, List.append_nil]
  have rawMember : declaration ∈ (GeneralExecutionAdmission.compile snapshot permissions).rules := by
    simpa only [Plan.compile, Plan.rules_preserved] using List.mem_of_getElem? position
  obtain ⟨authored, index, sourcePosition, _, compiled⟩ := compiled_rule_origin rawMember
  have info := rulePlan_readout compiled
  have originalPosition : snapshot.language.rewrites[declaration.declarationIndex]? = some declaration.authored := by
    simpa only [info.1, info.2.1] using List.mk_mem_zipIdx_iff_getElem?.mp sourcePosition
  have declared := GeneralPlanEnvironment.selected_rule plan position
  have specified := GeneralPlanEnvironment.selected_specification plan position
  have empty : declaration.rule.premises = [] := by simpa only [elaborated, BindingMetadata.annotate] using noPremises
  have operation : ScopedReflectiveExecution.binderOperation
      (GeneralPlanEnvironment.environment plan).reflection declaration.rule =
        ScopedReflectiveExecution.binderOperation permissions.reflection declaration.authored := by
    change ScopedReflectiveExecution.binderOperation plan.permissions.reflection declaration.rule = _
    rw [permissionsSaved, elaborated, BindingMetadata.binderOperation]
  constructor
  · intro firing
    cases firing with
    | @fire _ _ _ _ _ rule spec _ _ _ _ rulePosition specPosition admitted sorted matching typed premises reduced targetSorted =>
      have sameRule := Option.some.inj (declared.symm.trans rulePosition)
      have sameSpec := Option.some.inj (specified.symm.trans specPosition)
      cases sameRule
      cases sameSpec
      rw [empty] at premises
      cases premises
      refine ⟨.fire originalPosition noPremises ?_ ?_ ?_ ?_ typed.2 ?_ ?_, rfl, rfl⟩
      · simpa only [elaborated, BindingMetadata.admitted] using admitted
      · simpa only [saved] using (GeneralPlanEnvironment.typing_iff plan bound type source).mp sorted
      · exact (BindingMetadata.traced_iff declaration.authored (some declaration.binding.spec)
          declaration.binding.spec bound.length 0 .left [] [] captured declaration.authored.left source trace).mp
          (by simpa only [elaborated, BindingMetadata.annotate] using matching)
      · simpa only [saved] using (typed_assignment plan declaration implicitTypes bound captured).mp typed.1
      · rw [operation, elaborated, BindingMetadata.reduct] at reduced
        exact reduced
      · simpa only [saved] using (GeneralPlanEnvironment.typing_iff plan bound type target).mp targetSorted
  · rintro ⟨firing, rfl, rfl⟩
    cases firing with
    | fire rulePosition originalEmpty admitted sorted matching typed objects reduced targetSorted =>
      have sameRule := Option.some.inj (originalPosition.symm.trans rulePosition)
      cases sameRule
      apply RootFiring.fire declared specified
      · simpa only [elaborated, BindingMetadata.admitted] using admitted
      · exact (GeneralPlanEnvironment.typing_iff plan bound type source).mpr (by simpa only [saved] using sorted)
      · simpa only [elaborated, BindingMetadata.annotate] using BindingMetadata.traced _ matching
      · exact ⟨(typed_assignment plan declaration implicitTypes bound _).mpr (by simpa only [saved] using typed), objects⟩
      · rw [empty]
        exact .nil
      · rw [operation, elaborated, BindingMetadata.reduct]
        exact reduced
      · exact (GeneralPlanEnvironment.typing_iff plan bound type target).mpr (by simpa only [saved] using targetSorted)

/-- The full original lambda declaration family, not a selected beta-only
language, supplies the semantics of every retained scheduled occurrence. -/
theorem lambda_occurrences (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern) :
    (∃ answer ∈ Scheduled.receipts (Scheduled.finishSource
        (GeneralPlanEnvironment.environment AuthoredPlans.lambdaPlan) bound type source),
      answer.index = index ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = completed ∧ answer.history = history ∧ answer.target = target) ↔
    RootFiring Controls.lambdaEnvironment bound type source index trace captured completed history target := by
  rw [Scheduled.finishSource_occurrences _ AuthoredPlans.lambda_environment_admitted,
    AuthoredPlans.lambda_environment_original]

theorem letCase_occurrences (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern) :
    (∃ answer ∈ Scheduled.receipts (Scheduled.finishSource
        (GeneralPlanEnvironment.environment AuthoredPlans.letCasePlan) bound type source),
      answer.index = index ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = completed ∧ answer.history = history ∧ answer.target = target) ↔
    RootFiring Controls.LetCaseControls.environment bound type source index trace captured completed history target := by
  rw [Scheduled.finishSource_occurrences _ AuthoredPlans.letCase_environment_admitted,
    AuthoredPlans.letCase_environment_original]

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.SourceReadout
