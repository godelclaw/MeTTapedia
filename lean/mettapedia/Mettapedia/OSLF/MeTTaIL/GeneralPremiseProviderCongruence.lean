import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! Static rule selection depends on provider signatures. Replacing rows
preserves that selection; checking the replacement rows remains a separate
admission obligation. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding

theorem signature_congr {before after : ProviderSnapshot} (same : before.signatures = after.signatures)
    (relation : String) (arity : Nat) : signature? before relation arity = signature? after relation arity := by
  simp only [signature?,same]

theorem premiseFlow_signatures_congr {before after : ProviderSnapshot}
    (same : before.signatures = after.signatures) (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (available : List String) (premise : Premise) :
    premiseFlow language before rule spec available premise = premiseFlow language after rule spec available premise := by
  induction premise generalizing available with
  | relationQuery relation arguments => simp only [premiseFlow,signature_congr same]
  | freshness _ => rfl
  | congruence _ _ => rfl
  | scopedStep _ => rfl
  | forAll collection parameter body ih => simp only [premiseFlow,ih]

theorem premisesFlow_signatures_congr {before after : ProviderSnapshot}
    (same : before.signatures = after.signatures) (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (available : List String) (premises : List Premise) :
    premisesFlow language before rule spec available premises = premisesFlow language after rule spec available premises := by
  induction premises generalizing available with
  | nil => rfl
  | cons premise rest ih =>
    simp only [premisesFlow,premiseFlow_signatures_congr same,ih]

theorem rulePremisesAdmitted_signatures_congr {before after : ProviderSnapshot}
    (same : before.signatures = after.signatures) (language : LanguageDef)
    (rule : RewriteRule) (spec : RuleBindingSpec) :
    rulePremisesAdmitted language before rule spec = rulePremisesAdmitted language after rule spec := by
  simp only [rulePremisesAdmitted,premisesFlow_signatures_congr same]

end Mettapedia.OSLF.MeTTaIL.GeneralPremise

namespace Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

open Syntax

theorem rulePlan_congr {before after : Snapshot} (language : before.language = after.language)
    (signatures : before.provider.signatures = after.provider.signatures) (index : Nat) (rule : RewriteRule) :
    rulePlan? before index rule = rulePlan? after index rule := by
  unfold rulePlan?
  rw [language]
  cases binding : GeneralRuleBindingInference.compile? after.language rule with
  | none => rfl
  | some binding =>
    simp only [GeneralPremise.rulePremisesAdmitted_signatures_congr signatures]

theorem ruleObligations_congr {before after : Snapshot} (language : before.language = after.language)
    (signatures : before.provider.signatures = after.provider.signatures) (index : Nat) (rule : RewriteRule) :
    ruleObligations before index rule = ruleObligations after index rule := by
  unfold ruleObligations
  rw [language]
  cases binding : GeneralRuleBindingInference.compile? after.language rule with
  | none => rfl
  | some binding =>
    simp only [GeneralPremise.rulePremisesAdmitted_signatures_congr signatures]

theorem equationPlan_congr {before after : Snapshot} (language : before.language = after.language)
    (signatures : before.provider.signatures = after.provider.signatures) (index : Nat) (equation : Equation)
    (direction : ScopedEquationExecution.Orientation) :
    equationPlan? before index equation direction = equationPlan? after index equation direction := by
  unfold equationPlan?
  dsimp only
  rw [language]
  cases binding : GeneralRuleBindingInference.compile? after.language (ScopedEquationExecution.orientedRule equation direction) with
  | none => rfl
  | some binding =>
    simp only [GeneralPremise.rulePremisesAdmitted_signatures_congr signatures]

theorem equationObligations_congr {before after : Snapshot} (language : before.language = after.language)
    (signatures : before.provider.signatures = after.provider.signatures) (index : Nat) (equation : Equation)
    (direction : ScopedEquationExecution.Orientation) :
    equationObligations before index equation direction = equationObligations after index equation direction := by
  unfold equationObligations
  dsimp only
  rw [language]
  cases binding : GeneralRuleBindingInference.compile? after.language (ScopedEquationExecution.orientedRule equation direction) with
  | none => rfl
  | some binding =>
    simp only [GeneralPremise.rulePremisesAdmitted_signatures_congr signatures]

theorem rules_congr {before after : Snapshot} (language : before.language = after.language)
    (signatures : before.provider.signatures = after.provider.signatures) (permissions : Permissions) :
    rules before permissions = rules after permissions := by
  have selected : selectedRules before permissions = selectedRules after permissions := by
    simp only [selectedRules,language]
  unfold rules
  rw [selected]
  congr 1
  funext entry
  exact rulePlan_congr language signatures entry.2 entry.1

theorem equations_congr {before after : Snapshot} (language : before.language = after.language)
    (signatures : before.provider.signatures = after.provider.signatures) (permissions : Permissions) :
    equations before permissions = equations after permissions := by
  have selected : selectedEquations before permissions = selectedEquations after permissions := by
    simp only [selectedEquations,language]
  unfold equations
  rw [selected]
  congr 1
  funext entry
  exact equationPlan_congr language signatures entry.2.1 entry.1 entry.2.2

theorem executionLanguage_congr {before after : Snapshot} (language : before.language = after.language)
    (signatures : before.provider.signatures = after.provider.signatures) (permissions : Permissions) :
    executionLanguage before permissions = executionLanguage after permissions := by
  simp only [executionLanguage,language,rules_congr language signatures permissions]

theorem compile_obligations_congr {before after : Snapshot} (language : before.language = after.language)
    (free : before.freeTypes = after.freeTypes)
    (signatures : before.provider.signatures = after.provider.signatures)
    (rows : GeneralPremise.checkProviderClosed before.language before.free before.provider =
      GeneralPremise.checkProviderClosed after.language after.free after.provider)
    (permissions : Permissions) :
    (compile before permissions).obligations = (compile after permissions).obligations := by
  have freeCheck : checkFreeContext before = checkFreeContext after := by
    simp only [checkFreeContext,language,free]
  have selectedRule : selectedRules before permissions = selectedRules after permissions := by
    simp only [selectedRules,language]
  have selectedEquation : selectedEquations before permissions = selectedEquations after permissions := by
    simp only [selectedEquations,language]
  have missingRules : missing permissions.ruleIndices before.language.rewrites.length =
      missing permissions.ruleIndices after.language.rewrites.length := by rw [language]
  have missingEquations : missing permissions.equationIndices before.language.equations.length =
      missing permissions.equationIndices after.language.equations.length := by rw [language]
  have ruleChecks : (selectedRules before permissions).flatMap (fun (rule,index) => ruleObligations before index rule) =
      (selectedRules after permissions).flatMap (fun (rule,index) => ruleObligations after index rule) := by
    rw [selectedRule]
    congr 1
    funext entry
    exact ruleObligations_congr language signatures entry.2 entry.1
  have equationChecks : (selectedEquations before permissions).flatMap
      (fun (equation,index,direction) => equationObligations before index equation direction) =
      (selectedEquations after permissions).flatMap
      (fun (equation,index,direction) => equationObligations after index equation direction) := by
    rw [selectedEquation]
    congr 1
    funext entry
    exact equationObligations_congr language signatures entry.2.1 entry.1 entry.2.2
  have sets : setDecompositionFree before permissions = setDecompositionFree after permissions := by
    simp only [setDecompositionFree,language,selectedRule,selectedEquation]
  change _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ = _
  rw [freeCheck,rows,missingRules,missingEquations,ruleChecks,equationChecks,
    executionLanguage_congr language signatures permissions,sets,language]
  rfl

theorem complete_replace_provider {before after : Snapshot} (language : before.language = after.language)
    (free : before.freeTypes = after.freeTypes)
    (signatures : before.provider.signatures = after.provider.signatures)
    (permissions : Permissions) (admitted : (compile before permissions).complete = true)
    (closed : GeneralPremise.checkProviderClosed after.language after.free after.provider = true) :
    (compile after permissions).complete = true := by
  have priorClosed := (complete_snapshot_checks admitted).2.2.1
  have rows : GeneralPremise.checkProviderClosed before.language before.free before.provider =
      GeneralPremise.checkProviderClosed after.language after.free after.provider := by rw [priorClosed,closed]
  have same := compile_obligations_congr language free signatures rows permissions
  unfold Plan.complete at admitted ⊢
  rw [← same]
  exact admitted

#print axioms rules_congr
#print axioms equations_congr
#print axioms complete_replace_provider

end Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
