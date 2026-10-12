import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonical
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalSyntax
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-!
# Explicit canonical-template admission for the selected presentation

The gate checks authored rule and equation templates, including literal query
inputs. Accepted templates agree with their display-erased presentation.
Outside this gate erasing a query or repeated capture can change the literal
raw semantics; no unrestricted alpha-invariance assertion is made.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalTemplates

open Syntax GeneralExecutionAdmission

/-- The selected declarations are checked, so deselected capabilities remain
outside this presentation's claim. -/
def checkPlan (plan : Plan) : Bool :=
  plan.rules.all (fun selected => checkRule selected.rule && checkBinding selected.binding.spec) &&
    plan.equations.all (fun selected => checkRule selected.rule && checkBinding selected.binding.spec)

theorem compiled_plan_canonical (snapshot : Snapshot) (permissions : Permissions) :
    checkPlan (compile snapshot permissions) = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro selected member
    exact Bool.and_eq_true_iff.mpr (compiled_rule_canonical member)
  · apply List.all_eq_true.mpr
    intro selected member
    exact Bool.and_eq_true_iff.mpr (compiled_equation_canonical member)

theorem plan_rule_fixed {plan : Plan} (checked : checkPlan plan = true)
    {selected : RulePlan} (member : selected ∈ plan.rules) : normalizeRule selected.rule = selected.rule := by
  apply rule_fixed
  exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).1 _ member)).1

theorem plan_equation_fixed {plan : Plan} (checked : checkPlan plan = true)
    {selected : EquationPlan} (member : selected ∈ plan.equations) : normalizeRule selected.rule = selected.rule := by
  apply rule_fixed
  exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 _ member)).1

theorem plan_rule_spine_fixed {plan : Plan} (checked : checkPlan plan = true)
    {selected : RulePlan} (member : selected ∈ plan.rules)
    {occurrence : MetavariableOccurrence} (authored : occurrence ∈ selected.binding.spec.occurrences) :
    occurrence.arguments.map Pattern.eraseBinderMetadata = occurrence.arguments := by
  apply patterns_fixed
  have binding := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).1 _ member)).2
  exact List.all_eq_true.mp binding _ authored

theorem plan_equation_spine_fixed {plan : Plan} (checked : checkPlan plan = true)
    {selected : EquationPlan} (member : selected ∈ plan.equations)
    {occurrence : MetavariableOccurrence} (authored : occurrence ∈ selected.binding.spec.occurrences) :
    occurrence.arguments.map Pattern.eraseBinderMetadata = occurrence.arguments := by
  apply patterns_fixed
  have binding := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 _ member)).2
  exact List.all_eq_true.mp binding _ authored


end Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalTemplates
