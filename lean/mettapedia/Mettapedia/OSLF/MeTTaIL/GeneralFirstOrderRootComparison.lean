import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProfile
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineComparison

/-!
# Whole-profile comparison of scoped and ordinary first-order firings

The two matching relations are independently defined. For an unconditional,
sorted first-order row, inferred dependency-free metadata does not change its
ordinary instance or contractum. Both directions retain an actual scoped
firing witness; the comparison is not an assumption of executor completeness.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch Match MatchSpec
open Mettapedia.GSLT.LanguageDef.WellSorted

 theorem inferred_zero (rule : RewriteRule) :
    GeneralPremise.checkZeroDependencies (GeneralRuleBindingInference.inferredSpec rule) = true := by
  simp [GeneralPremise.checkZeroDependencies, GeneralRuleBindingInference.inferredSpec]

 theorem rootFiring_readout {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {index : Nat} {source target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index =
      some (GeneralRuleBindingInference.inferredSpec rule))
    (shape : checkRuleShape rule = true)
    (firing : GeneralPremise.RootFiring environment bound type source index trace captured completed history target) :
    ∃ bindings, MatchRel rule.left source bindings ∧ applyBindings bindings rule.right = target := by
  obtain ⟨left, right, premiseFree, _, rightBound⟩ := checkRuleShape_sound shape
  cases firing with
  | fire actualDeclared actualSpecified _ _ matching typed premises reduct _ =>
    have same := Option.some.inj (actualDeclared.symm.trans declared)
    subst same
    have sameSpec := Option.some.inj (actualSpecified.symm.trans specified)
    subst sameSpec
    rw [premiseFree] at premises
    cases premises
    exact rule_readout left right matching.matching (typed.rootValues (inferred_zero _)) reduct rightBound

 theorem rootFiring_construct {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {index : Nat} {source target : Pattern} {bindings : Bindings}
    (valid : environment.language.validate = [])
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index =
      some (GeneralRuleBindingInference.inferredSpec rule))
    (admitted : admittedFor rule (GeneralRuleBindingInference.inferredSpec rule) = true)
    (shape : checkRuleShape rule = true)
    (leftTyped : HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.left type)
    (rightTyped : HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.right type)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
    (matched : MatchRel rule.left source bindings) (endpoint : applyBindings bindings rule.right = target) :
    ∃ trace captured, GeneralPremise.RootFiring environment bound type source index trace captured captured [] target := by
  obtain ⟨left, right, premiseFree, unique, rightBound⟩ := checkRuleShape_sound shape
  have typed : CapturesTyped environment.language environment.free bound rule.typeContext bindings :=
    matching_captures_typed valid left matched leftTyped sourceTyped.1 sourceTyped.2.1 sourceTyped.2.2.1
  have names := raw_matching_defined left matched
  obtain ⟨captured, matching, compatible⟩ := scoped_instance (initial := []) left (NameCoherent.left rule) names typed unique
    (by intro _ member; cases member)
  rw [matchRel_correct matched left.isMatchCorrect] at matching
  have capturedTyped := compatible.typed typed unique
  have roots := compatible.rootValues typed
  have rhsNames : GeneralPremise.BoundNames captured rule.right.freeFvarNames :=
    fun name member => GeneralPremise.matching_bound_names matching name (rightBound name member)
  have rhsDefined : Defined bindings rule.right.freeFvarNames := fun name member => names name (rightBound name member)
  have dependencies : ∀ name ∈ rule.right.freeFvarNames,
      dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some [] := by
    intro name member
    obtain ⟨body, found⟩ := rhsDefined name member
    obtain ⟨expected, declared, _⟩ := typed (name, body) (raw_lookup_member found)
    exact inferred_dependencies_of_lookup rule unique declared
  obtain ⟨actualTarget, reduct⟩ := instantiation_total right (NameCoherent.right rule) rhsNames roots dependencies
    (operation := ScopedReflectiveExecution.binderOperation environment.reflection rule)
  have recovered := instantiation_readout right roots reduct
  have same : actualTarget = target :=
    recovered.symm.trans ((compatible.readout right rhsNames).trans endpoint)
  have rootReduct : reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
      rule (GeneralRuleBindingInference.inferredSpec rule) bound.length captured = some target := by
    exact reduct.trans (congrArg some same)
  have targetTyped : OpenPatternWellSorted environment.language environment.free bound type target := by
    rw [← endpoint]
    exact substituted_open right rightTyped rhsDefined typed
  obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.matches_trace matching
  exact ⟨trace, captured, .fire declared specified admitted sourceTyped traced capturedTyped
    (premiseFree ▸ .nil) rootReduct targetTyped⟩

 theorem rootFiring_iff_match {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {index : Nat} {source target : Pattern}
    (valid : environment.language.validate = [])
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index =
      some (GeneralRuleBindingInference.inferredSpec rule))
    (admitted : admittedFor rule (GeneralRuleBindingInference.inferredSpec rule) = true)
    (shape : checkRuleShape rule = true)
    (leftTyped : HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.left type)
    (rightTyped : HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.right type)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source) :
    (∃ trace captured completed history,
      GeneralPremise.RootFiring environment bound type source index trace captured completed history target) ↔
    ∃ bindings, MatchRel rule.left source bindings ∧ applyBindings bindings rule.right = target := by
  constructor
  · rintro ⟨trace, captured, completed, history, firing⟩
    exact rootFiring_readout declared specified shape firing
  · rintro ⟨bindings, matching, endpoint⟩
    obtain ⟨trace, captured, firing⟩ := rootFiring_construct valid declared specified admitted shape
      leftTyped rightTyped sourceTyped matching endpoint
    exact ⟨trace, captured, captured, [], firing⟩

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
