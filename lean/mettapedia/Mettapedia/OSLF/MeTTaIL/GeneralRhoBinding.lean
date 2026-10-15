import Mettapedia.GSLT.Examples.ScopedRhoBinding
import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCertified
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy

/-!
# An admitted companion to the original rho declarations

The companion retains the original COMM source patterns and premises. Its
added metadata declares the unmatched parallel collection and the received
name dependency of the input body. The selected operational profile executes
declaration zero with literal repeated-channel matching and the authored
reflective binder operation. Structural equation closure and canonical name
matching are separate semantic profiles.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open Mettapedia.GSLT.LanguageDef.ReflectionExtension

def comm : RewriteRule :=
  { rhoCommRewrite with
    typeContext := rhoCommRewrite.typeContext ++
      [("rest", .collection .hashBag (.base "Proc"))]
    bindings := some scopedCommBindingSpec }

def language : LanguageDef :=
  { rhoCalc with rewrites := [comm, scopedParCongRewrite] }

theorem comm_original_source :
    comm.name = rhoCommRewrite.name ∧ comm.left = rhoCommRewrite.left ∧
      comm.right = rhoCommRewrite.right ∧ comm.premises = rhoCommRewrite.premises :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem language_original_grammar :
    language.types = rhoCalc.types ∧ language.terms = rhoCalc.terms ∧
      language.equations = rhoCalc.equations :=
  ⟨rfl, rfl, rfl⟩

def snapshot : GeneralExecutionAdmission.Snapshot where
  language := language
  freeTypes := []
  provider := ⟨[], []⟩

def permissions : GeneralExecutionAdmission.Permissions where
  sites := .all
  ruleIndices := some [0]
  equationIndices := some []
  includeDerivedEquations := false
  reflection := rhoReflectionProfile

def plan : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile snapshot permissions

def declaration : GeneralExecutionAdmission.RulePlan where
  declarationIndex := 0
  authored := comm
  binding := ⟨scopedCommBindingSpec, .authored⟩

theorem comm_admitted : admittedFor comm scopedCommBindingSpec = true := by
  decide +kernel

theorem dependencies_declared : dependencySortsDeclared language scopedCommBindingSpec = true := by
  decide +kernel

theorem binding_compiled : GeneralRuleBindingInference.compile? language comm =
    some declaration.binding := by
  simp only [GeneralRuleBindingInference.compile?, show comm.bindings = some scopedCommBindingSpec from rfl,
    comm_admitted, dependencies_declared, Bool.true_and, ↓reduceIte]
  rfl

theorem premises_admitted : GeneralPremise.rulePremisesAdmitted language snapshot.provider comm
    scopedCommBindingSpec = true := by
  simp [GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow,
    GeneralPremise.namesAvailable, comm, rhoCommRewrite, Pattern.freeFvarNames]

theorem canonical_comm : GeneralEquationCanonicalTemplates.checkRule comm = true := by
  decide +kernel

theorem canonical_spines :
    GeneralEquationCanonicalTemplates.checkBinding scopedCommBindingSpec = true := by
  decide +kernel

theorem rule_plan_compiled : GeneralExecutionAdmission.rulePlan? snapshot 0 comm = some declaration := by
  simp only [GeneralExecutionAdmission.rulePlan?, Option.bind_eq_bind,
    show snapshot.language = language from rfl,
    binding_compiled, Option.bind_some, show declaration.binding.spec = scopedCommBindingSpec from rfl,
    show declaration.binding.elaborate comm = comm from rfl,
    premises_admitted, canonical_comm, canonical_spines, Bool.and_self, ↓reduceIte]
  rfl

theorem selected_rules : GeneralExecutionAdmission.selectedRules snapshot permissions = [(comm, 0)] := rfl

theorem compiled_rules : plan.rules = [declaration] := by
  unfold plan GeneralExecutionAdmission.compile GeneralExecutionAdmission.rules
  simp only [selected_rules, List.filterMap_cons, rule_plan_compiled, List.filterMap_nil]

theorem compilation_complete : plan.complete = true := by
  have validated : language.validate = [] := scoped_rho_validates
  have reflected : Reflection.validate language rhoReflectionProfile = [] := by decide +kernel
  have strata : GeneralPremise.checkStepStratification
      (GeneralExecutionAdmission.executionLanguage snapshot permissions) = true := by
    change GeneralPremise.checkStepStratification
      { language with rewrites := plan.rules.map GeneralExecutionAdmission.RulePlan.rule } = true
    rw [compiled_rules]
    rfl
  have ruleChecks : (GeneralExecutionAdmission.selectedRules snapshot permissions).flatMap
      (fun (rule, index) => GeneralExecutionAdmission.ruleObligations snapshot index rule) = [] := by
    rw [selected_rules]
    simp only [List.flatMap_cons, List.flatMap_nil, GeneralExecutionAdmission.ruleObligations,
      show snapshot.language = language from rfl, binding_compiled,
      show declaration.binding.elaborate comm = comm from rfl,
      show declaration.binding.spec = scopedCommBindingSpec from rfl, premises_admitted,
      canonical_comm, canonical_spines, Bool.and_self,
      ↓reduceIte, List.nil_append]
  have equationSelection : GeneralExecutionAdmission.selectedEquations snapshot permissions = [] := rfl
  have freeChecked : GeneralExecutionAdmission.checkFreeContext snapshot = true := rfl
  have providerChecked : GeneralPremise.checkProviderClosed snapshot.language snapshot.free
      snapshot.provider = true := rfl
  have missingRules : GeneralExecutionAdmission.missing permissions.ruleIndices
      snapshot.language.rewrites.length = [] := rfl
  have missingEquations : GeneralExecutionAdmission.missing permissions.equationIndices
      snapshot.language.equations.length = [] := rfl
  apply List.isEmpty_iff.mpr
  change (GeneralExecutionAdmission.compile snapshot permissions).obligations = []
  dsimp only [GeneralExecutionAdmission.compile]
  rw [show snapshot.language.validate = [] from validated, freeChecked, providerChecked,
    show Reflection.validate snapshot.language permissions.reflection = [] from reflected,
    missingRules, missingEquations, ruleChecks, equationSelection, strata]
  rfl

theorem compilation_has_no_equations : plan.equations = [] := by
  rfl

theorem compiled_rule : declaration.rule = comm := rfl

theorem substitution_selected :
    ReflectiveSubstitution.substitutionPresentationForRule? rhoReflectionProfile comm =
      some rhoReflectivePresentation.toReflectivePresentationDecl := by
  decide +kernel

theorem binder_operation :
    ScopedReflectiveExecution.binderOperation rhoReflectionProfile comm =
      ScopedRuleInstantiation.reflectiveOperation
        rhoReflectivePresentation.toReflectivePresentationDecl := by
  simp only [ScopedReflectiveExecution.binderOperation, substitution_selected]

def rootValue (ambient : Nat) (body : Pattern) : ContextualValue :=
  ⟨[], ambient, body⟩

def bodyValue (ambient : Nat) (body : Pattern) : ContextualValue :=
  ⟨[.base "Name"], ambient, body⟩

private theorem root_occurrence_identity :
    occurrenceAssignment 0 0 [] = Pattern.bvar := by
  funext index
  simp [occurrenceAssignment]

private theorem body_occurrence_identity :
    occurrenceAssignment 1 1 [.bvar 0] = Pattern.bvar := by
  funext index
  by_cases localIndex : index < 1
  · have zero : index = 0 := by omega
    subst index
    rfl
  · simp only [occurrenceAssignment, localIndex, ↓reduceIte]
    congr 1
    omega

private theorem root_recovery_identity (ambient : Nat) :
    recoveryAssignment 0 0 ambient [] = Pattern.bvar := by
  funext index
  simp [recoveryAssignment]

private theorem body_recovery_identity (ambient : Nat) :
    recoveryAssignment 1 1 ambient [0] = Pattern.bvar := by
  funext index
  by_cases localIndex : index < 1
  · have zero : index = 0 := by omega
    subst index
    rfl
  · simp only [recoveryAssignment, localIndex, ↓reduceIte]
    congr 1
    omega

theorem instantiate_root {ambient : Nat} {body : Pattern}
    (safe : body.isWellScopedAt ambient = true) :
    instantiateValue? (rootValue ambient body) ambient 0 [] = some body := by
  simp [instantiateValue?, rootValue, root_occurrence_identity,
    ContextSubstitution.substitute_id, safe]

theorem instantiate_body {ambient : Nat} {body : Pattern}
    (safe : body.isWellScopedAt (ambient + 1) = true) :
    instantiateValue? (bodyValue ambient body) ambient 1 [.bvar 0] = some body := by
  simp [instantiateValue?, bodyValue, body_occurrence_identity,
    ContextSubstitution.substitute_id, safe, Nat.add_comm, Pattern.isWellScopedAt]

theorem recover_root {ambient : Nat} {body : Pattern}
    (safe : body.isWellScopedAt ambient = true) :
    recoverValue? [] ambient 0 [] body = some (rootValue ambient body) := by
  simp [recoverValue?, safe, variableSpine?, root_recovery_identity,
    ContextSubstitution.substitute_id, rootValue, instantiateValue?, root_occurrence_identity]

theorem recover_body {ambient : Nat} {body : Pattern}
    (safe : body.isWellScopedAt (ambient + 1) = true) :
    recoverValue? [.base "Name"] ambient 1 [.bvar 0] body =
      some (bodyValue ambient body) := by
  simp [recoverValue?, safe, variableSpine?, Nat.add_comm, body_recovery_identity,
    ContextSubstitution.substitute_id, bodyValue, instantiateValue?, body_occurrence_identity,
    Pattern.isWellScopedAt]

end Mettapedia.OSLF.MeTTaIL.GeneralRho
