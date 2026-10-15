import Mettapedia.OSLF.MeTTaIL.RuleBinding

/-!
# Canonical authored templates and occurrence spines

These syntax checks inspect binder display metadata in actual rule sides,
premises and explicit occurrence arguments. Accepted templates equal their
display-erased presentation. No operational-language dependency is needed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalTemplates

open Syntax

def checkPremise : Premise → Bool
  | .freshness condition => condition.term.hasCanonicalBinderMetadata
  | .congruence source target => source.hasCanonicalBinderMetadata && target.hasCanonicalBinderMetadata
  | .scopedStep step => step.source.hasCanonicalBinderMetadata && step.target.hasCanonicalBinderMetadata
  | .relationQuery _ arguments => arguments.all Pattern.hasCanonicalBinderMetadata
  | .forAll _ _ body => checkPremise body

def normalizePremise : Premise → Premise
  | .freshness condition => .freshness {condition with term := condition.term.eraseBinderMetadata}
  | .congruence source target => .congruence source.eraseBinderMetadata target.eraseBinderMetadata
  | .scopedStep step => .scopedStep {step with
      source := step.source.eraseBinderMetadata
      target := step.target.eraseBinderMetadata}
  | .relationQuery relation arguments => .relationQuery relation (arguments.map Pattern.eraseBinderMetadata)
  | .forAll collection parameter body => .forAll collection parameter (normalizePremise body)

def checkRule (rule : RewriteRule) : Bool :=
  rule.left.hasCanonicalBinderMetadata && rule.right.hasCanonicalBinderMetadata && rule.premises.all checkPremise

def normalizeRule (rule : RewriteRule) : RewriteRule :=
  {rule with
    left := rule.left.eraseBinderMetadata
    right := rule.right.eraseBinderMetadata
    premises := rule.premises.map normalizePremise}

def checkEquation (equation : Equation) : Bool :=
  equation.left.hasCanonicalBinderMetadata && equation.right.hasCanonicalBinderMetadata &&
    equation.premises.all checkPremise

def normalizeEquation (equation : Equation) : Equation :=
  {equation with
    left := equation.left.eraseBinderMetadata
    right := equation.right.eraseBinderMetadata
    premises := equation.premises.map normalizePremise}

def checkLanguage (language : LanguageDef) : Bool :=
  language.rewrites.all checkRule && language.equations.all checkEquation

def checkBinding (binding : RuleBindingSpec) : Bool :=
  binding.occurrences.all fun occurrence => occurrence.arguments.all Pattern.hasCanonicalBinderMetadata

theorem patterns_fixed (patterns : List Pattern)
    (checked : patterns.all Pattern.hasCanonicalBinderMetadata = true) :
    patterns.map Pattern.eraseBinderMetadata = patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
      simp only [List.all_cons, Bool.and_eq_true] at checked
      simp only [List.map_cons, Pattern.eraseBinderMetadata_eq_self_of_canonical checked.1, ih checked.2]

theorem premise_fixed (premise : Premise) (checked : checkPremise premise = true) :
    normalizePremise premise = premise := by
  cases premise with
  | freshness condition =>
      cases condition
      simp only [checkPremise] at checked
      simp only [normalizePremise, Pattern.eraseBinderMetadata_eq_self_of_canonical checked]
  | congruence source target =>
      simp only [checkPremise, Bool.and_eq_true] at checked
      simp only [normalizePremise, Pattern.eraseBinderMetadata_eq_self_of_canonical checked.1,
        Pattern.eraseBinderMetadata_eq_self_of_canonical checked.2]
  | scopedStep step =>
      cases step
      simp only [checkPremise, Bool.and_eq_true] at checked
      simp only [normalizePremise, Pattern.eraseBinderMetadata_eq_self_of_canonical checked.1,
        Pattern.eraseBinderMetadata_eq_self_of_canonical checked.2]
  | relationQuery relation arguments => exact congrArg (Premise.relationQuery relation) (patterns_fixed arguments checked)
  | forAll collection parameter body =>
      exact congrArg (Premise.forAll collection parameter) (premise_fixed body checked)
termination_by premise

theorem premises_fixed (premises : List Premise) (checked : premises.all checkPremise = true) :
    premises.map normalizePremise = premises := by
  induction premises with
  | nil => rfl
  | cons premise premises ih =>
      simp only [List.all_cons, Bool.and_eq_true] at checked
      simp only [List.map_cons, premise_fixed premise checked.1, ih checked.2]

theorem rule_fixed (rule : RewriteRule) (checked : checkRule rule = true) : normalizeRule rule = rule := by
  simp only [checkRule, Bool.and_eq_true] at checked
  cases rule
  simp only [normalizeRule, Pattern.eraseBinderMetadata_eq_self_of_canonical checked.1.1,
    Pattern.eraseBinderMetadata_eq_self_of_canonical checked.1.2, premises_fixed _ checked.2]

theorem equation_fixed (equation : Equation) (checked : checkEquation equation = true) :
    normalizeEquation equation = equation := by
  simp only [checkEquation, Bool.and_eq_true] at checked
  cases equation
  simp only [normalizeEquation, Pattern.eraseBinderMetadata_eq_self_of_canonical checked.1.1,
    Pattern.eraseBinderMetadata_eq_self_of_canonical checked.1.2, premises_fixed _ checked.2]

def namedLiteralRule : RewriteRule where
  name := "named-literal"
  typeContext := []
  premises := [.relationQuery "inspect" [.lambda (some "display") (.bvar 0)]]
  left := .apply "A" []
  right := .lambda (some "display") (.bvar 0)

theorem named_literal_requires_admission : checkRule namedLiteralRule = false := by decide +kernel

theorem named_literal_normalization_changes_template : normalizeRule namedLiteralRule ≠ namedLiteralRule := by
  intro same
  have right := congrArg RewriteRule.right same
  simp only [normalizeRule, namedLiteralRule, Pattern.eraseBinderMetadata,
    Pattern.lambda.injEq] at right
  cases right.1

end Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalTemplates
