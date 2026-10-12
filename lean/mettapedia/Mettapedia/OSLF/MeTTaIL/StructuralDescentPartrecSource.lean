import Mettapedia.OSLF.MeTTaIL.StructuralDescentSourceReadout

/-! # Original partial-recursive-machine declarations and scoped receipts -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.PartrecSource

open Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise GeneralExecutionAdmission
open StructuralDescent.Controls

private theorem all_implicit_empty :
    partrecPlan.rules.all (fun declaration => declaration.binding.implicitTypes.isEmpty) = true := by
  simp only [partrecPlan, Plan.compile, Plan.rules_preserved]
  simp +decide [GeneralExecutionAdmission.compile, GeneralExecutionAdmission.rules,
    partrecSnapshot, List.zipIdx, selectedRules, selected, rootPermissions, rulePlan?,
    Mettapedia.Languages.PartrecMachine.partrecMachine, LanguageDef.ofCore,
    Mettapedia.Languages.PartrecMachine.rewrites,
    GeneralRuleBindingInference.compile?, GeneralRuleBindingInference.rootInput,
    GeneralRuleBindingInference.rootArguments, GeneralRuleBindingInference.rootDeclared,
    GeneralRuleBindingInference.BindingPlan.elaborate,
    GeneralRuleBindingInference.BindingPlan.implicitTypes,
    GeneralEquationCanonicalTemplates.checkRule,
    GeneralEquationCanonicalTemplates.checkBinding,
    Pattern.freeFvarNames, GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow]

theorem implicit_types_empty (declaration : RulePlan) (member : declaration ∈ partrecPlan.rules) :
    declaration.binding.implicitTypes = [] :=
  List.isEmpty_iff.mp (List.all_eq_true.mp all_implicit_empty declaration member)

theorem original_order : partrecPlan.rules.map RulePlan.declarationIndex =
    List.range partrecSnapshot.language.rewrites.length := by
  simp only [partrecPlan, Plan.compile, Plan.rules_preserved]
  simp +decide [GeneralExecutionAdmission.compile, GeneralExecutionAdmission.rules,
    partrecSnapshot, List.zipIdx, selectedRules, selected, rootPermissions, rulePlan?,
    Mettapedia.Languages.PartrecMachine.partrecMachine, LanguageDef.ofCore,
    Mettapedia.Languages.PartrecMachine.rewrites,
    GeneralRuleBindingInference.compile?, GeneralRuleBindingInference.rootInput,
    GeneralRuleBindingInference.rootArguments, GeneralRuleBindingInference.rootDeclared,
    GeneralRuleBindingInference.BindingPlan.elaborate,
    GeneralRuleBindingInference.BindingPlan.implicitTypes,
    GeneralEquationCanonicalTemplates.checkRule,
    GeneralEquationCanonicalTemplates.checkBinding,
    Pattern.freeFvarNames, GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow]

theorem no_premises (declaration : RulePlan) (member : declaration ∈ partrecPlan.rules) :
    declaration.authored.premises = [] := by
  have original : declaration ∈ (GeneralExecutionAdmission.compile partrecSnapshot rootPermissions).rules := by
    simpa only [partrecPlan, Plan.compile, Plan.rules_preserved] using member
  obtain ⟨authored, index, source, _, compiled⟩ := compiled_rule_origin original
  have info := rulePlan_readout compiled
  rw [info.2.1]
  exact AuthoredPlans.partrec_premise_free authored
    (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp source))

/-- Every selected occurrence is exactly an original-source scoped match and
RHS instance. The theorem is uniform in input terms, ambient binders, result
sort, traced alternatives and captured values. -/
theorem occurrences (ordinal : Nat) (declaration : RulePlan)
    (position : partrecPlan.rules[ordinal]? = some declaration)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List Event) (target : Pattern) :
    (∃ answer ∈ Scheduled.receipts (Scheduled.finishSource partrecEnvironment bound type source),
      answer.index = ordinal ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = completed ∧ answer.history = history ∧ answer.target = target) ↔
    SourceReadout.PremiseFreeFiring partrecSnapshot rootPermissions.reflection declaration.binding.spec
      bound type source declaration.declarationIndex trace captured target ∧
      completed = captured ∧ history = [] := by
  rw [Scheduled.finishSource_occurrences _ AuthoredPlans.partrec_environment_admitted]
  exact SourceReadout.premise_free_root_iff partrecSnapshot rootPermissions ordinal declaration position
    (implicit_types_empty declaration (List.mem_of_getElem? position))
    (no_premises declaration (List.mem_of_getElem? position)) bound type source trace captured completed history target

#print axioms original_order
#print axioms occurrences

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.PartrecSource
