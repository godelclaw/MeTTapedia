import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
import Mettapedia.OSLF.MeTTaIL.GeneralEquationAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalSyntax
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesGenerator
import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

/-!
# Admission plans compiled from authored language snapshots

Selection retains original declaration positions. An equation may be admitted
for witnessed execution while its finite-coverage requirement remains open.
The compiler contains no supplied completeness proof or external stratum.
Typing, provider and binding checks use the actual immutable snapshot data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

open Syntax RuleBinding ScopedRuleMatching GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted

structure Snapshot where
  language : LanguageDef
  freeTypes : List (String × TypeExpr)
  provider : GeneralPremise.ProviderSnapshot
  deriving Repr

def Snapshot.free (snapshot : Snapshot) : FreeTypeContext :=
  fun name => (snapshot.freeTypes.find? fun entry => entry.1 == name).map Prod.snd

structure Permissions where
  sites : OperationalPermissions := .all
  ruleIndices : Option (List Nat) := none
  equationIndices : Option (List Nat) := none
  equationDirections : List ScopedEquationExecution.Orientation := [.forward, .reverse]
  includeDerivedEquations : Bool := true
  reflection : Reflection.ReflectionProfile := Reflection.ReflectionProfile.empty
  deriving DecidableEq, Repr

def selected (selection : Option (List Nat)) (index : Nat) : Bool :=
  match selection with
  | none => true
  | some indices => indices.contains index

theorem selected_spec (selection : Option (List Nat)) (index : Nat) :
    selected selection index = true ↔ selection = none ∨ ∃ indices, selection = some indices ∧ index ∈ indices := by
  cases selection <;> simp [selected]

inductive Obligation where
  | invalidLanguage
  | invalidFreeContext
  | invalidProvider
  | invalidReflection
  | missingRule (index : Nat)
  | missingEquation (index : Nat)
  | ruleBinding (index : Nat)
  | rulePremises (index : Nat)
  | ruleCanonical (index : Nat)
  | equationBinding (index : Nat) (direction : ScopedEquationExecution.Orientation)
  | equationPremises (index : Nat) (direction : ScopedEquationExecution.Orientation)
  | equationCanonical (index : Nat) (direction : ScopedEquationExecution.Orientation)
  | equationBound (index : Nat) (direction : ScopedEquationExecution.Orientation)
  | childStratification
  | derivedEquationCoverage
  deriving DecidableEq, Repr

structure RulePlan where
  declarationIndex : Nat
  authored : RewriteRule
  binding : GeneralRuleBindingInference.BindingPlan
  deriving Repr

def RulePlan.rule (plan : RulePlan) : RewriteRule :=
  plan.binding.elaborate plan.authored

structure EquationPlan where
  declarationIndex : Nat
  authored : Equation
  direction : ScopedEquationExecution.Orientation
  binding : GeneralRuleBindingInference.BindingPlan
  coverageReady : Bool
  deriving Repr

def EquationPlan.rule (plan : EquationPlan) : RewriteRule :=
  plan.binding.elaborate (ScopedEquationExecution.orientedRule plan.authored plan.direction)

structure Plan where
  snapshot : Snapshot
  permissions : Permissions
  rules : List RulePlan
  equations : List EquationPlan
  obligations : List Obligation
  deriving Repr

def declaredType (language : LanguageDef) (type : TypeExpr) : Bool :=
  type.baseNames.all fun name => language.typeNames.contains name

def checkFreeContext (snapshot : Snapshot) : Bool :=
  decide (snapshot.freeTypes.map Prod.fst).Nodup &&
    snapshot.freeTypes.all fun entry => declaredType snapshot.language entry.2

def rulePlan? (snapshot : Snapshot) (index : Nat) (rule : RewriteRule) : Option RulePlan := do
  let binding ← GeneralRuleBindingInference.compile? snapshot.language rule
  if GeneralPremise.rulePremisesAdmitted snapshot.language snapshot.provider
      (binding.elaborate rule) binding.spec &&
      GeneralEquationCanonicalTemplates.checkRule rule &&
      GeneralEquationCanonicalTemplates.checkBinding binding.spec then
    some ⟨index, rule, binding⟩
  else none

def ruleObligations (snapshot : Snapshot) (index : Nat) (rule : RewriteRule) : List Obligation :=
  match GeneralRuleBindingInference.compile? snapshot.language rule with
  | none => [.ruleBinding index]
  | some binding =>
      if GeneralEquationCanonicalTemplates.checkRule rule &&
          GeneralEquationCanonicalTemplates.checkBinding binding.spec then
        if GeneralPremise.rulePremisesAdmitted snapshot.language snapshot.provider
            (binding.elaborate rule) binding.spec
          then [] else [.rulePremises index]
      else [.ruleCanonical index]

def equationPlan? (snapshot : Snapshot) (index : Nat) (equation : Equation)
    (direction : ScopedEquationExecution.Orientation) : Option EquationPlan := do
  let rule := ScopedEquationExecution.orientedRule equation direction
  let binding ← GeneralRuleBindingInference.compile? snapshot.language rule
  if GeneralPremise.rulePremisesAdmitted snapshot.language snapshot.provider
      (binding.elaborate rule) binding.spec &&
      GeneralEquationCanonicalTemplates.checkRule rule &&
      GeneralEquationCanonicalTemplates.checkBinding binding.spec then
    some ⟨index, equation, direction, binding,
      GeneralEquationAdmission.checkRule (binding.elaborate rule) binding.spec⟩
  else none

def equationObligations (snapshot : Snapshot) (index : Nat) (equation : Equation)
    (direction : ScopedEquationExecution.Orientation) : List Obligation :=
  let rule := ScopedEquationExecution.orientedRule equation direction
  match GeneralRuleBindingInference.compile? snapshot.language rule with
  | none => [.equationBinding index direction]
  | some binding =>
      if GeneralEquationCanonicalTemplates.checkRule rule &&
          GeneralEquationCanonicalTemplates.checkBinding binding.spec then
        if GeneralPremise.rulePremisesAdmitted snapshot.language snapshot.provider
            (binding.elaborate rule) binding.spec then
          if GeneralEquationAdmission.checkRule (binding.elaborate rule) binding.spec then []
          else [.equationBound index direction]
        else [.equationPremises index direction]
      else [.equationCanonical index direction]

def missing (selection : Option (List Nat)) (length : Nat) : List Nat :=
  selection.getD [] |>.filter fun index => !(index < length)

def selectedRules (snapshot : Snapshot) (permissions : Permissions) : List (RewriteRule × Nat) :=
  snapshot.language.rewrites.zipIdx.filter fun (_, index) => selected permissions.ruleIndices index

def selectedEquations (snapshot : Snapshot) (permissions : Permissions) :
    List (Equation × Nat × ScopedEquationExecution.Orientation) :=
  (snapshot.language.equations.zipIdx.filter fun (_, index) =>
    selected permissions.equationIndices index).flatMap fun (equation, index) =>
      permissions.equationDirections.eraseDups.map fun direction => (equation, index, direction)

def rules (snapshot : Snapshot) (permissions : Permissions) : List RulePlan :=
  (selectedRules snapshot permissions).filterMap fun (rule, index) => rulePlan? snapshot index rule

def equations (snapshot : Snapshot) (permissions : Permissions) : List EquationPlan :=
  (selectedEquations snapshot permissions).filterMap fun (equation, index, direction) =>
    equationPlan? snapshot index equation direction

/-- Child strata use the selected actual declarations, preserving their order. -/
def executionLanguage (snapshot : Snapshot) (permissions : Permissions) : LanguageDef :=
  { snapshot.language with rewrites := (rules snapshot permissions).map RulePlan.rule }

def compile (snapshot : Snapshot) (permissions : Permissions) : Plan where
  snapshot := snapshot
  permissions := permissions
  rules := rules snapshot permissions
  equations := equations snapshot permissions
  obligations :=
    (if snapshot.language.validate.isEmpty then [] else [.invalidLanguage]) ++
    (if checkFreeContext snapshot then [] else [.invalidFreeContext]) ++
    (if GeneralPremise.checkProviderClosed snapshot.language snapshot.free snapshot.provider
      then [] else [.invalidProvider]) ++
    (if (Reflection.validate snapshot.language permissions.reflection).isEmpty
      then [] else [.invalidReflection]) ++
    (missing permissions.ruleIndices snapshot.language.rewrites.length).map Obligation.missingRule ++
    (missing permissions.equationIndices snapshot.language.equations.length).map Obligation.missingEquation ++
    (selectedRules snapshot permissions).flatMap (fun (rule, index) => ruleObligations snapshot index rule) ++
    (selectedEquations snapshot permissions).flatMap
      (fun (equation, index, direction) => equationObligations snapshot index equation direction) ++
    (if GeneralPremise.checkStepStratification (executionLanguage snapshot permissions)
      then [] else [.childStratification]) ++
    (if permissions.includeDerivedEquations &&
        (snapshot.language.usesCollection .hashBag || snapshot.language.usesCollection .hashSet ||
          snapshot.language.hasAlgebraDeclarations)
      then [.derivedEquationCoverage] else [])

def Plan.complete (plan : Plan) : Bool := plan.obligations.isEmpty

theorem rulePlan_readout {snapshot : Snapshot} {index : Nat} {rule : RewriteRule} {plan : RulePlan}
    (compiled : rulePlan? snapshot index rule = some plan) :
    plan.declarationIndex = index ∧ plan.authored = rule ∧
      GeneralRuleBindingInference.compile? snapshot.language rule = some plan.binding ∧
      admittedFor plan.rule plan.binding.spec = true ∧
      dependencySortsDeclared snapshot.language plan.binding.spec = true ∧
      GeneralPremise.rulePremisesAdmitted snapshot.language snapshot.provider plan.rule plan.binding.spec = true := by
  simp only [rulePlan?, Option.bind_eq_bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨binding, checked, compiled⟩ := compiled
  split at compiled
  next supported =>
    cases Option.some.inj compiled
    have admitted := GeneralRuleBindingInference.compile_admitted checked
    exact ⟨rfl, rfl, checked, admitted.1, admitted.2,
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp supported).1).1⟩
  next => contradiction

theorem compiled_rule_origin {snapshot : Snapshot} {permissions : Permissions} {plan : RulePlan}
    (member : plan ∈ (compile snapshot permissions).rules) :
    ∃ rule index, (rule, index) ∈ snapshot.language.rewrites.zipIdx ∧
      selected permissions.ruleIndices index = true ∧
      rulePlan? snapshot index rule = some plan := by
  obtain ⟨⟨rule, index⟩, selectedMember, checked⟩ := List.mem_filterMap.mp member
  rcases List.mem_filter.mp selectedMember with ⟨authored, enabled⟩
  exact ⟨rule, index, authored, enabled, checked⟩

theorem equationPlan_readout {snapshot : Snapshot} {index : Nat} {equation : Equation}
    {direction : ScopedEquationExecution.Orientation} {plan : EquationPlan}
    (compiled : equationPlan? snapshot index equation direction = some plan) :
    plan.declarationIndex = index ∧ plan.authored = equation ∧ plan.direction = direction ∧
      admittedFor plan.rule plan.binding.spec = true ∧
      dependencySortsDeclared snapshot.language plan.binding.spec = true ∧
      GeneralPremise.rulePremisesAdmitted snapshot.language snapshot.provider
        plan.rule plan.binding.spec = true ∧
      plan.coverageReady = GeneralEquationAdmission.checkRule plan.rule plan.binding.spec := by
  simp only [equationPlan?, Option.bind_eq_bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨binding, checked, compiled⟩ := compiled
  split at compiled
  next supported =>
    cases Option.some.inj compiled
    have admitted := GeneralRuleBindingInference.compile_admitted checked
    exact ⟨rfl, rfl, rfl, admitted.1, admitted.2,
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp supported).1).1, rfl⟩
  next => contradiction

theorem rulePlan_canonical {snapshot : Snapshot} {index : Nat} {rule : RewriteRule}
    {plan : RulePlan} (compiled : rulePlan? snapshot index rule = some plan) :
    GeneralEquationCanonicalTemplates.checkRule plan.rule = true ∧
      GeneralEquationCanonicalTemplates.checkBinding plan.binding.spec = true := by
  simp only [rulePlan?, Option.bind_eq_bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨binding, _, compiled⟩ := compiled
  split at compiled
  next supported =>
    cases Option.some.inj compiled
    simp only [Bool.and_eq_true] at supported
    exact ⟨supported.1.2, supported.2⟩
  next => contradiction

theorem equationPlan_canonical {snapshot : Snapshot} {index : Nat} {equation : Equation}
    {direction : ScopedEquationExecution.Orientation} {plan : EquationPlan}
    (compiled : equationPlan? snapshot index equation direction = some plan) :
    GeneralEquationCanonicalTemplates.checkRule plan.rule = true ∧
      GeneralEquationCanonicalTemplates.checkBinding plan.binding.spec = true := by
  simp only [equationPlan?, Option.bind_eq_bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨binding, _, compiled⟩ := compiled
  split at compiled
  next supported =>
    cases Option.some.inj compiled
    simp only [Bool.and_eq_true] at supported
    exact ⟨supported.1.2, supported.2⟩
  next => contradiction

theorem rule_canonical_rejection {snapshot : Snapshot} {index : Nat} {rule : RewriteRule}
    {binding : GeneralRuleBindingInference.BindingPlan}
    (inferred : GeneralRuleBindingInference.compile? snapshot.language rule = some binding)
    (rejected : GeneralEquationCanonicalTemplates.checkRule rule = false) :
    rulePlan? snapshot index rule = none ∧
      ruleObligations snapshot index rule = [.ruleCanonical index] := by
  simp [rulePlan?, ruleObligations, inferred, rejected]

theorem equation_canonical_rejection {snapshot : Snapshot} {index : Nat}
    {equation : Equation} {direction : ScopedEquationExecution.Orientation}
    {binding : GeneralRuleBindingInference.BindingPlan}
    (inferred : GeneralRuleBindingInference.compile? snapshot.language
      (ScopedEquationExecution.orientedRule equation direction) = some binding)
    (rejected : GeneralEquationCanonicalTemplates.checkRule
      (ScopedEquationExecution.orientedRule equation direction) = false) :
    equationPlan? snapshot index equation direction = none ∧
      equationObligations snapshot index equation direction = [.equationCanonical index direction] := by
  simp [equationPlan?, equationObligations, inferred, rejected]

theorem compiled_equation_origin {snapshot : Snapshot} {permissions : Permissions} {plan : EquationPlan}
    (member : plan ∈ (compile snapshot permissions).equations) :
    ∃ equation index direction, (equation, index) ∈ snapshot.language.equations.zipIdx ∧
      selected permissions.equationIndices index = true ∧
      direction ∈ permissions.equationDirections ∧
      equationPlan? snapshot index equation direction = some plan := by
  obtain ⟨⟨equation, index, direction⟩, selectedMember, checked⟩ := List.mem_filterMap.mp member
  obtain ⟨⟨authoredEquation, authoredIndex⟩, pairMember, represented⟩ := List.mem_flatMap.mp selectedMember
  obtain ⟨authoredDirection, directionMember, equality⟩ := List.mem_map.mp represented
  cases equality
  rcases List.mem_filter.mp pairMember with ⟨authored, enabled⟩
  exact ⟨equation, index, direction, authored, enabled,
    List.mem_eraseDups.mp directionMember, checked⟩

theorem compiled_rule_canonical {snapshot : Snapshot} {permissions : Permissions}
    {plan : RulePlan} (member : plan ∈ (compile snapshot permissions).rules) :
    GeneralEquationCanonicalTemplates.checkRule plan.rule = true ∧
      GeneralEquationCanonicalTemplates.checkBinding plan.binding.spec = true := by
  obtain ⟨_, _, _, _, checked⟩ := compiled_rule_origin member
  exact rulePlan_canonical checked

theorem compiled_equation_canonical {snapshot : Snapshot} {permissions : Permissions}
    {plan : EquationPlan} (member : plan ∈ (compile snapshot permissions).equations) :
    GeneralEquationCanonicalTemplates.checkRule plan.rule = true ∧
      GeneralEquationCanonicalTemplates.checkBinding plan.binding.spec = true := by
  obtain ⟨_, _, _, _, _, _, checked⟩ := compiled_equation_origin member
  exact equationPlan_canonical checked

theorem ruleObligations_empty_iff (snapshot : Snapshot) (index : Nat) (rule : RewriteRule) :
    ruleObligations snapshot index rule = [] ↔ ∃ plan, rulePlan? snapshot index rule = some plan := by
  unfold ruleObligations rulePlan?
  cases declared : GeneralRuleBindingInference.compile? snapshot.language rule with
  | none => simp
  | some binding =>
      cases admitted : GeneralPremise.rulePremisesAdmitted snapshot.language snapshot.provider
          (binding.elaborate rule) binding.spec <;>
        cases canonical : GeneralEquationCanonicalTemplates.checkRule rule <;>
          cases spines : GeneralEquationCanonicalTemplates.checkBinding binding.spec <;>
            simp_all

theorem equationObligations_empty_iff (snapshot : Snapshot) (index : Nat) (equation : Equation)
    (direction : ScopedEquationExecution.Orientation) :
    equationObligations snapshot index equation direction = [] ↔
      ∃ plan, equationPlan? snapshot index equation direction = some plan ∧ plan.coverageReady = true := by
  unfold equationObligations equationPlan?
  dsimp only
  cases declared : GeneralRuleBindingInference.compile? snapshot.language
      (ScopedEquationExecution.orientedRule equation direction) with
  | none => simp
  | some binding =>
      cases admitted : GeneralPremise.rulePremisesAdmitted snapshot.language snapshot.provider
          (binding.elaborate (ScopedEquationExecution.orientedRule equation direction)) binding.spec <;>
        cases balanced : GeneralEquationAdmission.checkRule
          (binding.elaborate (ScopedEquationExecution.orientedRule equation direction)) binding.spec <;>
          cases canonical : GeneralEquationCanonicalTemplates.checkRule
            (ScopedEquationExecution.orientedRule equation direction) <;>
            cases spines : GeneralEquationCanonicalTemplates.checkBinding binding.spec <;>
              simp_all

theorem complete_rule_coverage {snapshot : Snapshot} {permissions : Permissions}
    (complete : (compile snapshot permissions).complete = true)
    {rule : RewriteRule} {index : Nat}
    (authored : (rule, index) ∈ snapshot.language.rewrites.zipIdx)
    (enabled : selected permissions.ruleIndices index = true) :
    ∃ plan ∈ (compile snapshot permissions).rules, rulePlan? snapshot index rule = some plan := by
  have empty : (compile snapshot permissions).obligations = [] := List.isEmpty_iff.mp complete
  have selectedMember : (rule, index) ∈ selectedRules snapshot permissions :=
    List.mem_filter.mpr ⟨authored, enabled⟩
  have obligationsEmpty : ruleObligations snapshot index rule = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro obligation member
    have flatMember : obligation ∈ (selectedRules snapshot permissions).flatMap
        (fun (rule, index) => ruleObligations snapshot index rule) :=
      List.mem_flatMap.mpr ⟨(rule, index), selectedMember, member⟩
    have total : obligation ∈ (compile snapshot permissions).obligations := by
      simp only [compile, List.mem_append]
      tauto
    rw [empty] at total
    cases total
  obtain ⟨plan, checked⟩ := (ruleObligations_empty_iff snapshot index rule).mp obligationsEmpty
  exact ⟨plan, List.mem_filterMap.mpr ⟨(rule, index), selectedMember, checked⟩, checked⟩

theorem complete_equation_coverage {snapshot : Snapshot} {permissions : Permissions}
    (complete : (compile snapshot permissions).complete = true)
    {equation : Equation} {index : Nat} {direction : ScopedEquationExecution.Orientation}
    (authored : (equation, index) ∈ snapshot.language.equations.zipIdx)
    (enabled : selected permissions.equationIndices index = true)
    (allowed : direction ∈ permissions.equationDirections) :
    ∃ plan ∈ (compile snapshot permissions).equations,
      equationPlan? snapshot index equation direction = some plan ∧ plan.coverageReady = true := by
  have empty : (compile snapshot permissions).obligations = [] := List.isEmpty_iff.mp complete
  have selectedMember : (equation, index, direction) ∈ selectedEquations snapshot permissions := by
    exact List.mem_flatMap.mpr ⟨(equation, index), List.mem_filter.mpr ⟨authored, enabled⟩,
      List.mem_map.mpr ⟨direction, List.mem_eraseDups.mpr allowed, rfl⟩⟩
  have obligationsEmpty : equationObligations snapshot index equation direction = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro obligation member
    have flatMember : obligation ∈ (selectedEquations snapshot permissions).flatMap
        (fun (equation, index, direction) => equationObligations snapshot index equation direction) :=
      List.mem_flatMap.mpr ⟨(equation, index, direction), selectedMember, member⟩
    have total : obligation ∈ (compile snapshot permissions).obligations := by
      simp only [compile, List.mem_append]
      tauto
    rw [empty] at total
    cases total
  obtain ⟨plan, checked, finite⟩ :=
    (equationObligations_empty_iff snapshot index equation direction).mp obligationsEmpty
  exact ⟨plan, List.mem_filterMap.mpr ⟨(equation, index, direction), selectedMember, checked⟩,
    checked, finite⟩

theorem complete_snapshot_checks {snapshot : Snapshot} {permissions : Permissions}
    (complete : (compile snapshot permissions).complete = true) :
    snapshot.language.validate.isEmpty = true ∧ checkFreeContext snapshot = true ∧
      GeneralPremise.checkProviderClosed snapshot.language snapshot.free snapshot.provider = true ∧
      GeneralPremise.checkStepStratification (executionLanguage snapshot permissions) = true := by
  have empty : (compile snapshot permissions).obligations = [] := List.isEmpty_iff.mp complete
  have language : snapshot.language.validate.isEmpty = true := by
    by_contra failed
    have rejected : snapshot.language.validate.isEmpty = false := Bool.eq_false_iff.mpr failed
    have bad : Obligation.invalidLanguage ∈ (compile snapshot permissions).obligations := by
      simp [compile, rejected]
    rw [empty] at bad
    cases bad
  have free : checkFreeContext snapshot = true := by
    by_contra failed
    have rejected : checkFreeContext snapshot = false := Bool.eq_false_iff.mpr failed
    have bad : Obligation.invalidFreeContext ∈ (compile snapshot permissions).obligations := by
      simp [compile, rejected]
    rw [empty] at bad
    cases bad
  have provider : GeneralPremise.checkProviderClosed snapshot.language snapshot.free snapshot.provider = true := by
    by_contra failed
    have rejected : GeneralPremise.checkProviderClosed snapshot.language snapshot.free snapshot.provider = false :=
      Bool.eq_false_iff.mpr failed
    have bad : Obligation.invalidProvider ∈ (compile snapshot permissions).obligations := by
      simp [compile, rejected]
    rw [empty] at bad
    cases bad
  have strata : GeneralPremise.checkStepStratification (executionLanguage snapshot permissions) = true := by
    by_contra failed
    have rejected : GeneralPremise.checkStepStratification (executionLanguage snapshot permissions) = false :=
      Bool.eq_false_iff.mpr failed
    have bad : Obligation.childStratification ∈ (compile snapshot permissions).obligations := by
      simp [compile, rejected]
    rw [empty] at bad
    cases bad
  exact ⟨language, free, provider, strata⟩

theorem complete_derived_equation_boundary {snapshot : Snapshot} {permissions : Permissions}
    (complete : (compile snapshot permissions).complete = true)
    (enabled : permissions.includeDerivedEquations = true) :
    snapshot.language.usesCollection .hashBag = false ∧
      snapshot.language.usesCollection .hashSet = false ∧
      snapshot.language.hasAlgebraDeclarations = false := by
  have empty : (compile snapshot permissions).obligations = [] := List.isEmpty_iff.mp complete
  have noLaws : (snapshot.language.usesCollection .hashBag ||
      snapshot.language.usesCollection .hashSet || snapshot.language.hasAlgebraDeclarations) = false := by
    by_contra failed
    have present : (snapshot.language.usesCollection .hashBag ||
        snapshot.language.usesCollection .hashSet || snapshot.language.hasAlgebraDeclarations) = true :=
      by cases actual : (snapshot.language.usesCollection .hashBag ||
          snapshot.language.usesCollection .hashSet || snapshot.language.hasAlgebraDeclarations) <;>
        simp_all
    have bad : Obligation.derivedEquationCoverage ∈ (compile snapshot permissions).obligations := by
      simp [compile, enabled, present]
    rw [empty] at bad
    cases bad
  cases bag : snapshot.language.usesCollection .hashBag <;>
    cases set : snapshot.language.usesCollection .hashSet <;>
      cases algebra : snapshot.language.hasAlgebraDeclarations <;> simp_all

theorem complete_reflection {snapshot : Snapshot} {permissions : Permissions}
    (complete : (compile snapshot permissions).complete = true) :
    Reflection.validate snapshot.language permissions.reflection = [] := by
  have empty : (compile snapshot permissions).obligations = [] := List.isEmpty_iff.mp complete
  by_contra failed
  have rejected : (Reflection.validate snapshot.language permissions.reflection).isEmpty = false := by
    cases h : (Reflection.validate snapshot.language permissions.reflection).isEmpty with
    | false => rfl
    | true => exact False.elim (failed (List.isEmpty_iff.mp h))
  have bad : Obligation.invalidReflection ∈ (compile snapshot permissions).obligations := by
    simp [compile, rejected]
  rw [empty] at bad
  cases bad

end Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
