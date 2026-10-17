import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledReadout
import Mettapedia.OSLF.MeTTaIL.StructuralDescentControls
import Mettapedia.OSLF.MeTTaIL.StructuralDescentAuthoredValidity
import Mettapedia.OSLF.MeTTaIL.StructuralDescentPremiseFreeAdmission

/-!
# Original authored sources through generic plan admission

The same generic elaborator and structural-descent refinement admit the
original full lambda profile, partial-recursive machine, and sorted let/case
language. Plans retain source declaration positions and authored binding data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.AuthoredPlans

open Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise GeneralExecutionAdmission
open StructuralDescent.Controls

def snapshot (language : LanguageDef) : Snapshot where
  language := language
  freeTypes := []
  provider := {signatures := [], rows := []}

def lambdaPlan := Plan.compile
  (snapshot Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language) rootPermissions

def letCasePlan := Plan.compile
  (snapshot Mettapedia.OSLF.NativeTypes.Instances.LetCase.language) rootPermissions

#guard lambdaPlan.complete
#guard letCasePlan.complete
#guard partrecPlan.complete
#guard lambdaPlan.equations.isEmpty
#guard letCasePlan.equations.isEmpty
#guard partrecPlan.equations.isEmpty
#guard checkEnvironment (GeneralPlanEnvironment.environment lambdaPlan)
#guard checkEnvironment (GeneralPlanEnvironment.environment letCasePlan)
#guard checkEnvironment (GeneralPlanEnvironment.environment partrecPlan)

#guard lambdaPlan.rules.map (·.declarationIndex) == [0, 1, 2, 3]
#guard letCasePlan.rules.map (·.declarationIndex) == [0, 1, 2, 3, 4]
#guard partrecPlan.rules.map (·.declarationIndex) == List.range 19

private theorem environment_eq {first second : Environment}
    (language : first.language = second.language) (free : first.free = second.free)
    (provider : first.provider = second.provider)
    (specifications : first.specifications = second.specifications)
    (reflection : first.reflection = second.reflection)
    (dynamic : first.dynamic = second.dynamic) : first = second := by
  cases first
  cases second
  cases language
  cases free
  cases provider
  cases specifications
  cases reflection
  cases dynamic
  rfl

private theorem stratification_only (stratification : Bool) :
    ∀ obligation ∈ (if stratification then [] else [Obligation.childStratification]),
      obligation = Obligation.childStratification := by
  cases stratification <;> simp

theorem lambda_environment_original :
    GeneralPlanEnvironment.environment lambdaPlan = lambdaEnvironment := by
  change GeneralPlanEnvironment.environment (Plan.refine (GeneralExecutionAdmission.compile _ _)) = _
  rw [Plan.refinement_environment]
  simp +decide [GeneralPlanEnvironment.environment, List.zipIdx, GeneralExecutionAdmission.compile,
    GeneralExecutionAdmission.rules, selectedRules, selected, rootPermissions, snapshot,
    rulePlan?, GeneralRuleBindingInference.compile?, GeneralRuleBindingInference.BindingPlan.elaborate,
    GeneralRuleBindingInference.BindingPlan.implicitTypes, RulePlan.rule,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.language,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.lamCongRule,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLRule,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRRule,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLSpec,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRSpec,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLStep,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRStep,
    GeneralEquationCanonicalTemplates.checkRule,
    GeneralEquationCanonicalTemplates.checkBinding,
    Pattern.freeFvarNames, GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow,
    GeneralPremise.premiseFlow, GeneralPremise.schemaValuesChecked,
    lambdaEnvironment, authoredEnvironment]
  funext name
  rfl

theorem letCase_environment_original :
    GeneralPlanEnvironment.environment letCasePlan =
      StructuralDescent.Controls.LetCaseControls.environment := by
  change GeneralPlanEnvironment.environment (Plan.refine (GeneralExecutionAdmission.compile _ _)) = _
  rw [Plan.refinement_environment]
  simp +decide [GeneralPlanEnvironment.environment, List.zipIdx, GeneralExecutionAdmission.compile,
    GeneralExecutionAdmission.rules, selectedRules, selected, rootPermissions, snapshot,
    rulePlan?, GeneralRuleBindingInference.compile?, GeneralRuleBindingInference.BindingPlan.elaborate,
    GeneralRuleBindingInference.BindingPlan.implicitTypes, RulePlan.rule,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.language,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.letRule,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.caseRule,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.letInitialCongruence,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.letBodyCongruence,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.caseBodyCongruence,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.letTerm,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.returnValue,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.caseTerm,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.pair,
    GeneralEquationCanonicalTemplates.checkRule,
    GeneralEquationCanonicalTemplates.checkBinding,
    Pattern.freeFvarNames, GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow,
    GeneralPremise.premiseFlow, GeneralPremise.schemaValuesChecked,
    StructuralDescent.Controls.LetCaseControls.environment, authoredEnvironment]
  funext name
  rfl

theorem lambda_environment_admitted :
    checkEnvironment (GeneralPlanEnvironment.environment lambdaPlan) = true := by
  rw [lambda_environment_original]
  exact lambda_structural_admission

theorem letCase_environment_admitted :
    checkEnvironment (GeneralPlanEnvironment.environment letCasePlan) = true := by
  rw [letCase_environment_original]
  exact StructuralDescent.Controls.LetCaseControls.structurally_admitted

theorem lambda_plan_complete : lambdaPlan.complete = true := by
  have ready : Plan.structuralReady (GeneralExecutionAdmission.compile
      (snapshot Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language) rootPermissions) = true := by
    simpa only [Plan.structuralReady, lambdaPlan, Plan.compile, Plan.refinement_environment]
      using lambda_environment_admitted
  simp only [Plan.complete, lambdaPlan, Plan.compile, Plan.refine, ready, ite_true]
  simp only [GeneralExecutionAdmission.compile, snapshot,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.authored_language_valid,
    List.isEmpty_nil, if_true]
  simp +decide [List.zipIdx,
    selectedRules, selected, rootPermissions,
    GeneralRuleBindingInference.compile?, GeneralRuleBindingInference.BindingPlan.elaborate,
    GeneralRuleBindingInference.BindingPlan.implicitTypes,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.language,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.lamCongRule,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLRule,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRRule,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLSpec,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRSpec,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLStep,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRStep,
    GeneralEquationCanonicalTemplates.checkRule,
    GeneralEquationCanonicalTemplates.checkBinding,
    Pattern.freeFvarNames, GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow,
    GeneralPremise.premiseFlow, GeneralPremise.schemaValuesChecked,
    ruleObligations]
  exact stratification_only _

theorem letCase_plan_complete : letCasePlan.complete = true := by
  have ready : Plan.structuralReady (GeneralExecutionAdmission.compile
      (snapshot Mettapedia.OSLF.NativeTypes.Instances.LetCase.language) rootPermissions) = true := by
    simpa only [Plan.structuralReady, letCasePlan, Plan.compile, Plan.refinement_environment]
      using letCase_environment_admitted
  simp only [Plan.complete, letCasePlan, Plan.compile, Plan.refine, ready, ite_true]
  simp only [GeneralExecutionAdmission.compile, snapshot,
    AuthoredValidity.letCase_valid, List.isEmpty_nil, if_true]
  simp +decide [List.zipIdx,
    selectedRules, selected, rootPermissions,
    GeneralRuleBindingInference.compile?, GeneralRuleBindingInference.BindingPlan.elaborate,
    GeneralRuleBindingInference.BindingPlan.implicitTypes,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.language,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.letRule,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.caseRule,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.letInitialCongruence,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.letBodyCongruence,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.caseBodyCongruence,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.letTerm,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.returnValue,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.caseTerm,
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.pair,
    GeneralEquationCanonicalTemplates.checkRule,
    GeneralEquationCanonicalTemplates.checkBinding,
    Pattern.freeFvarNames, GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow,
    GeneralPremise.premiseFlow, GeneralPremise.schemaValuesChecked,
    ruleObligations]
  exact stratification_only _

theorem partrec_premise_free :
    ∀ rule ∈ Mettapedia.Languages.PartrecMachine.partrecMachine.rewrites, rule.premises = [] := by
  intro rule member
  simp only [Mettapedia.Languages.PartrecMachine.partrecMachine_rewrites,
    Mettapedia.Languages.PartrecMachine.rewrites, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem partrec_environment_admitted : checkEnvironment partrecEnvironment = true :=
  premise_free_admitted partrecSnapshot rootPermissions partrec_premise_free

theorem partrec_plan_complete : partrecPlan.complete = true := by
  have ready : Plan.structuralReady (GeneralExecutionAdmission.compile partrecSnapshot rootPermissions) = true := by
    simpa only [Plan.structuralReady, partrecPlan, partrecEnvironment, Plan.compile,
      Plan.refinement_environment] using partrec_environment_admitted
  simp only [Plan.complete, partrecPlan, Plan.compile, Plan.refine, ready, ite_true]
  simp only [GeneralExecutionAdmission.compile, partrecSnapshot,
    Mettapedia.Languages.PartrecMachine.partrecMachine_validate_eq_nil,
    List.isEmpty_nil, if_true]
  simp +decide [List.zipIdx, selectedRules, selected, rootPermissions,
    Mettapedia.Languages.PartrecMachine.partrecMachine, LanguageDef.ofCore,
    Mettapedia.Languages.PartrecMachine.rewrites,
    GeneralRuleBindingInference.compile?, GeneralRuleBindingInference.rootInput,
    GeneralRuleBindingInference.rootArguments, GeneralRuleBindingInference.rootDeclared,
    GeneralRuleBindingInference.BindingPlan.elaborate,
    GeneralRuleBindingInference.BindingPlan.implicitTypes,
    GeneralEquationCanonicalTemplates.checkRule,
    GeneralEquationCanonicalTemplates.checkBinding,
    Pattern.freeFvarNames, GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow,
    ruleObligations]
  exact stratification_only _

#eval lambdaPlan.obligations
#eval letCasePlan.obligations
#eval partrecPlan.obligations

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.AuthoredPlans
