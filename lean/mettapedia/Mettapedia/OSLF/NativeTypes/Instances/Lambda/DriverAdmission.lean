import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver

open Mettapedia.OSLF.Framework

/-!
# Authored declaration selection in the public lambda driver

The four switches select the original rule indices before elaboration.
Logical and cube choices do not change operational selection. Binding
inference preserves each selected declaration's name, patterns and premises.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.DriverAdmission

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Examples.ScopedLamCongExecution
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver

private def origin (plan : RulePlan) : RewriteRule × Nat :=
  (plan.authored, plan.declarationIndex)

private theorem origin_of_checked {snapshot : Snapshot} {index : Nat} {rule : RewriteRule}
    (admitted : (rulePlan? snapshot index rule).isSome = true) :
    (rulePlan? snapshot index rule).map origin = some (rule, index) := by
  cases checked : rulePlan? snapshot index rule with
  | none => simp only [checked, Option.isSome_none] at admitted; contradiction
  | some plan =>
    have readout := rulePlan_readout checked
    simp only [Option.map_some, origin, readout.1, readout.2.1]

theorem beta_origin :
    (rulePlan? Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot 0 betaRule).map origin =
      some (betaRule, 0) := by
  apply origin_of_checked
  simp only [rulePlan?, GeneralRuleBindingInference.compile?]
  simp only [betaRule, GeneralRuleBindingInference.BindingPlan.elaborate,
    GeneralRuleBindingInference.BindingPlan.implicitTypes,
    GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow,
    Pattern.freeFvarNames, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append]
  decide +kernel

theorem lamCong_origin :
    (rulePlan? Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot 1 lamCongRule).map origin =
      some (lamCongRule, 1) := by
  apply origin_of_checked
  simp only [rulePlan?, GeneralRuleBindingInference.compile?]
  simp only [lamCongRule, GeneralRuleBindingInference.BindingPlan.elaborate,
    GeneralRuleBindingInference.BindingPlan.implicitTypes,
    GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow, GeneralPremise.premiseFlow,
    Pattern.freeFvarNames, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append]
  decide +kernel

theorem appCongL_origin :
    (rulePlan? Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot 2 LambdaAuthoredFullRuleProfile.appCongLRule).map origin =
      some (LambdaAuthoredFullRuleProfile.appCongLRule, 2) := by
  apply origin_of_checked
  simp only [rulePlan?, GeneralRuleBindingInference.compile?]
  simp only [LambdaAuthoredFullRuleProfile.appCongLRule, LambdaAuthoredFullRuleProfile.appCongLStep,
    GeneralRuleBindingInference.BindingPlan.elaborate,
    GeneralRuleBindingInference.BindingPlan.implicitTypes,
    GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow, GeneralPremise.premiseFlow,
    Pattern.freeFvarNames, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append]
  decide +kernel

theorem appCongR_origin :
    (rulePlan? Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot 3 LambdaAuthoredFullRuleProfile.appCongRRule).map origin =
      some (LambdaAuthoredFullRuleProfile.appCongRRule, 3) := by
  apply origin_of_checked
  simp only [rulePlan?, GeneralRuleBindingInference.compile?]
  simp only [LambdaAuthoredFullRuleProfile.appCongRRule, LambdaAuthoredFullRuleProfile.appCongRStep,
    GeneralRuleBindingInference.BindingPlan.elaborate,
    GeneralRuleBindingInference.BindingPlan.implicitTypes,
    GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow, GeneralPremise.premiseFlow,
    Pattern.freeFvarNames, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append]
  decide +kernel

theorem selected_authored (configuration : Configuration) :
    (generated configuration).plan.rules.map (fun entry => (entry.authored, entry.declarationIndex)) =
      LambdaAuthoredFullRuleProfile.language.rewrites.zipIdx.filter
        (fun entry => (selectedIndices configuration.rules).contains entry.2) := by
  change (compile (generated configuration).snapshot (fragment configuration).operational).rules.map
    (fun entry => (entry.authored, entry.declarationIndex)) = _
  rw [original_snapshot]
  change (GeneralExecutionAdmission.rules Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot
    (fragment configuration).operational).map origin = _
  simp only [GeneralExecutionAdmission.rules, List.map_filterMap]
  have originalRules : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot.language.rewrites =
      [betaRule, lamCongRule, LambdaAuthoredFullRuleProfile.appCongLRule,
        LambdaAuthoredFullRuleProfile.appCongRRule] := rfl
  simp only [selectedRules, originalRules, List.zipIdx, List.filter_cons, List.filter_nil]
  rcases configuration with ⟨⟨beta, lamCong, appCongL, appCongR⟩, logic, vertex⟩
  cases beta <;> cases lamCong <;> cases appCongL <;> cases appCongR <;>
    simp [selected, fragment, selectedIndices, List.zipIdx,
      beta_origin, lamCong_origin, appCongL_origin, appCongR_origin,
      LambdaAuthoredFullRuleProfile.language]

theorem selected_indices (configuration : Configuration) :
    (generated configuration).plan.rules.map RulePlan.declarationIndex =
      selectedIndices configuration.rules := by
  have origins := congrArg (List.map Prod.snd) (selected_authored configuration)
  simp only [List.map_map, Function.comp_def] at origins
  rw [origins]
  rcases configuration with ⟨⟨beta, lamCong, appCongL, appCongR⟩, logic, vertex⟩
  cases beta <;> cases lamCong <;> cases appCongL <;> cases appCongR <;>
    simp [selectedIndices, LambdaAuthoredFullRuleProfile.language, List.zipIdx]

theorem declaration_readout (configuration : Configuration)
    (entry : RulePlan) (_listed : entry ∈ (generated configuration).plan.rules) :
    entry.rule.name = entry.authored.name ∧
      entry.rule.left = entry.authored.left ∧
      entry.rule.right = entry.authored.right ∧
      entry.rule.premises = entry.authored.premises :=
  GeneralRuleBindingInference.elaborate_source entry.binding entry.authored

#print axioms selected_authored
#print axioms selected_indices

theorem operational_selection_independent (rules : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Selection)
    (firstLogic secondLogic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (firstVertex secondVertex :
      Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.chosen.language) :
    (generated ⟨rules, firstLogic, firstVertex⟩).plan =
      (generated ⟨rules, secondLogic, secondVertex⟩).plan := rfl

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.DriverAdmission
