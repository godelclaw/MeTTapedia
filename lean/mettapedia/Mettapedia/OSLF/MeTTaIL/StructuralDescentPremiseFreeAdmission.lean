import Mettapedia.OSLF.MeTTaIL.StructuralDescentPlan

/-! # Generic structural admission of premise-free authored declarations -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent

open Syntax GeneralPremise GeneralExecutionAdmission

/-- Premise-free presentations require no recursive descent side condition.
Every selected rule still passes the original scoped binding admission. -/
theorem premise_free_admitted (snapshot : Snapshot) (permissions : Permissions)
    (premiseFree : ∀ rule ∈ snapshot.language.rewrites, rule.premises = []) :
    checkEnvironment (GeneralPlanEnvironment.environment (Plan.compile snapshot permissions)) = true := by
  apply List.all_eq_true.mpr
  rintro ⟨rule, ordinal⟩ member
  have ruleAt := List.mk_mem_zipIdx_iff_getElem?.mp member
  change ((Plan.compile snapshot permissions).rules.map RulePlan.rule)[ordinal]? = some rule at ruleAt
  rw [List.getElem?_map] at ruleAt
  obtain ⟨declaration, position, same⟩ := Option.map_eq_some_iff.mp ruleAt
  have originalMember : declaration ∈ (GeneralExecutionAdmission.compile snapshot permissions).rules := by
    simpa only [Plan.compile, Plan.rules_preserved] using List.mem_of_getElem? position
  obtain ⟨authored, index, source, _, compiled⟩ := compiled_rule_origin originalMember
  have info := rulePlan_readout compiled
  have noPremises : declaration.rule.premises = [] := by
    have preserved := GeneralRuleBindingInference.elaborate_source declaration.binding declaration.authored
    change (declaration.binding.elaborate declaration.authored).premises = []
    rw [preserved.2.2.2, info.2.1]
    exact premiseFree authored (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp source))
  rw [← same]
  change (match specification? (GeneralPlanEnvironment.environment (Plan.compile snapshot permissions)) ordinal with
    | none => false | some spec => checkRule declaration.rule spec) = true
  rw [GeneralPlanEnvironment.selected_specification _ position]
  simp only [StructuralDescent.checkRule, noPremises, checkPremises, Bool.and_true]
  exact info.2.2.2.1

end Mettapedia.OSLF.MeTTaIL.StructuralDescent
