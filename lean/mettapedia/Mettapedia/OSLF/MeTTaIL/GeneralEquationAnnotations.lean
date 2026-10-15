import Mettapedia.OSLF.MeTTaIL.GeneralEquationAdmission

/-!
# Equation schema checks under inferred binding annotations

Compiled declarations retain the original schema and attach a checked binding
specification. Attaching that specification does not change occurrence sites,
variable spines, static balance or the admission result computed from it.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationAnnotations

open Syntax RuleBinding GeneralEquationAdmission

theorem sitePattern_bindings (rule : RewriteRule) (annotation : Option RuleBindingSpec)
    (site : RulePatternSite) :
    sitePattern? {rule with bindings := annotation} site = sitePattern? rule site := by
  cases site <;> rfl

theorem siteDepth_bindings (rule : RewriteRule) (annotation : Option RuleBindingSpec)
    (site : RulePatternSite) :
    siteBinderDepth? {rule with bindings := annotation} site = siteBinderDepth? rule site := by
  cases site <;> rfl

theorem occurrenceDeclared_bindings (rule : RewriteRule) (annotation : Option RuleBindingSpec)
    (row : MetavariableOccurrence) :
    occurrenceDeclared {rule with bindings := annotation} row = occurrenceDeclared rule row := by
  simp only [occurrenceDeclared, sitePattern_bindings]

theorem occurrenceDepth_bindings (rule : RewriteRule) (annotation : Option RuleBindingSpec)
    (site : RulePatternSite) (path : List Nat) :
    occurrenceDepthAtSite? {rule with bindings := annotation} site path = occurrenceDepthAtSite? rule site path := by
  simp only [occurrenceDepthAtSite?, sitePattern_bindings, siteDepth_bindings]

theorem arguments_bindings (rule : RewriteRule) (annotation : Option RuleBindingSpec)
    (spec : RuleBindingSpec) (name : String) (site : RulePatternSite) (path : List Nat) :
    arguments? {rule with bindings := annotation} spec name site path = arguments? rule spec name site path := by
  simp only [arguments?, occurrenceDeclared_bindings]

theorem admitted_bindings (rule : RewriteRule) (annotation : Option RuleBindingSpec) (spec : RuleBindingSpec) :
    admittedFor {rule with bindings := annotation} spec = admittedFor rule spec := by
  simp only [admittedFor, occurrenceDeclared_bindings, occurrenceDepth_bindings]

mutual
  theorem checkSide_bindings (rule : RewriteRule) (annotation : Option RuleBindingSpec)
      (spec : RuleBindingSpec) (site : RulePatternSite) (path : List Nat) (depth : Nat) (pattern : Pattern) :
      checkSide {rule with bindings := annotation} spec site path depth pattern = checkSide rule spec site path depth pattern := by
    cases pattern with
    | fvar name => simp only [checkSide, arguments_bindings]
    | bvar index => simp only [checkSide]
    | apply label arguments =>
        simp only [checkSide]
        exact checkArguments_bindings rule annotation spec site path depth 0 arguments
    | lambda display body =>
        simp only [checkSide]
        exact checkSide_bindings rule annotation spec site (path ++ [0]) (depth + 1) body
    | multiLambda arity display body =>
        simp only [checkSide]
        exact checkSide_bindings rule annotation spec site (path ++ [0]) (depth + arity) body
    | subst body replacement => simp only [checkSide]
    | collection kind elements rest =>
        simp only [checkSide]
        rw [checkArguments_bindings rule annotation spec site path depth 0 elements]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem checkArguments_bindings (rule : RewriteRule) (annotation : Option RuleBindingSpec)
      (spec : RuleBindingSpec) (site : RulePatternSite) (path : List Nat) (depth index : Nat) (patterns : List Pattern) :
      checkArguments {rule with bindings := annotation} spec site path depth index patterns =
        checkArguments rule spec site path depth index patterns := by
    cases patterns with
    | nil => simp only [checkArguments]
    | cons first rest =>
        simp only [checkArguments]
        rw [checkSide_bindings rule annotation spec site (path ++ [index]) depth first,
          checkArguments_bindings rule annotation spec site path depth (index + 1) rest]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem checkRule_bindings (rule : RewriteRule) (annotation : Option RuleBindingSpec) (spec : RuleBindingSpec) :
    checkRule {rule with bindings := annotation} spec = checkRule rule spec := by
  simp only [checkRule, admitted_bindings, checkSide_bindings]

end Mettapedia.OSLF.MeTTaIL.GeneralEquationAnnotations
