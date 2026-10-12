import Mettapedia.OSLF.NativeTypes.Modal.NativeRuleInstantiationSubstitution

/-!
# Computed authored profile for positive operational reindexing

Schema scope and the actual source-selected binder operation are checked
alongside positive premises, closed provider rows and structural descent.
These checks expose the required operational profile independently of the
executor's broader fixed-snapshot admission.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalProfile

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding

inductive ScopedPremise : Premise → Prop where
  | query {relation : String} {arguments : List Pattern} :
      (∀ argument ∈ arguments, argument.isWellScopedAt 0 = true) →
      ScopedPremise (.relationQuery relation arguments)
  | child {source target : Pattern} : source.isWellScopedAt 0 = true →
      target.isWellScopedAt 0 = true → ScopedPremise (.congruence source target)
  | scopedChild {step : ScopedStepPremise} :
      step.source.isWellScopedAt step.binders.length = true →
      step.target.isWellScopedAt step.binders.length = true → ScopedPremise (.scopedStep step)
  | quantified {collection parameter : String} {body : Premise} :
      ScopedPremise body → ScopedPremise (.forAll collection parameter body)

def checkPremise : Premise → Bool
  | .freshness _ => false
  | .relationQuery _ arguments => arguments.all (fun argument => argument.isWellScopedAt 0)
  | .congruence source target => source.isWellScopedAt 0 && target.isWellScopedAt 0
  | .scopedStep step => step.source.isWellScopedAt step.binders.length && step.target.isWellScopedAt step.binders.length
  | .forAll _ _ body => checkPremise body

theorem checkPremise_exact (premise : Premise) : checkPremise premise = true ↔ ScopedPremise premise := by
  induction premise with
  | freshness condition => simp only [checkPremise, Bool.false_eq_true]; constructor <;> intro h <;> cases h
  | relationQuery relation arguments =>
      simp only [checkPremise, List.all_eq_true]
      constructor
      · exact ScopedPremise.query
      · intro admitted; cases admitted with | query scopes => exact scopes
  | congruence source target =>
      simp only [checkPremise, Bool.and_eq_true]
      constructor
      · rintro ⟨sourceScope, targetScope⟩; exact .child sourceScope targetScope
      · intro admitted; cases admitted with | child sourceScope targetScope => exact ⟨sourceScope, targetScope⟩
  | scopedStep step =>
      simp only [checkPremise, Bool.and_eq_true]
      constructor
      · rintro ⟨sourceScope, targetScope⟩; exact .scopedChild sourceScope targetScope
      · intro admitted; cases admitted with | scopedChild sourceScope targetScope => exact ⟨sourceScope, targetScope⟩
  | forAll collection parameter body ih =>
      rw [show checkPremise (.forAll collection parameter body) = checkPremise body from rfl, ih]
      constructor
      · exact ScopedPremise.quantified
      · intro admitted; cases admitted with | quantified scopes => exact scopes

structure ScopedRule (rule : RewriteRule) : Prop where
  left : rule.left.isWellScopedAt 0 = true
  right : rule.right.isWellScopedAt 0 = true
  premises : ∀ premise ∈ rule.premises, ScopedPremise premise

def checkRule (rule : RewriteRule) : Bool :=
  rule.left.isWellScopedAt 0 && rule.right.isWellScopedAt 0 && rule.premises.all checkPremise

theorem checkRule_exact (rule : RewriteRule) : checkRule rule = true ↔ ScopedRule rule := by
  simp only [checkRule, Bool.and_eq_true, List.all_eq_true, checkPremise_exact]
  constructor
  · rintro ⟨⟨left, right⟩, premises⟩; exact ⟨left, right, premises⟩
  · intro admitted; exact ⟨⟨admitted.left, admitted.right⟩, admitted.premises⟩

def checkScopedRules (environment : Environment) : Bool := environment.language.rewrites.all checkRule

theorem scopedRules_exact (environment : Environment) :
    checkScopedRules environment = true ↔ ∀ rule ∈ environment.language.rewrites, ScopedRule rule := by
  simp only [checkScopedRules, List.all_eq_true, checkRule_exact]

def checkOrdinaryRules (environment : Environment) : Bool :=
  environment.language.rewrites.all fun rule =>
    (ReflectiveSubstitution.substitutionPresentationForRule? environment.reflection rule).isNone

theorem ordinaryRules_exact (environment : Environment) :
    checkOrdinaryRules environment = true ↔ ∀ rule ∈ environment.language.rewrites,
      ReflectiveSubstitution.substitutionPresentationForRule? environment.reflection rule = none := by
  simp only [checkOrdinaryRules, List.all_eq_true, Option.isNone_iff_eq_none]

structure Admitted (environment : Environment) : Prop where
  prerequisites : NativeOperationalAdmission.Prerequisites environment
  scopes : ∀ rule ∈ environment.language.rewrites, ScopedRule rule
  ordinary : ∀ rule ∈ environment.language.rewrites,
    ReflectiveSubstitution.substitutionPresentationForRule? environment.reflection rule = none

def check (environment : Environment) : Bool :=
  NativeOperationalAdmission.checkPrerequisites environment && checkScopedRules environment && checkOrdinaryRules environment

theorem check_exact (environment : Environment) : check environment = true ↔ Admitted environment := by
  simp only [check, Bool.and_eq_true, NativeOperationalAdmission.prerequisites_exact,
    scopedRules_exact, ordinaryRules_exact]
  constructor
  · rintro ⟨⟨prerequisites, scopes⟩, ordinary⟩; exact ⟨prerequisites, scopes, ordinary⟩
  · intro admitted; exact ⟨⟨admitted.prerequisites, admitted.scopes⟩, admitted.ordinary⟩

end Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalProfile
