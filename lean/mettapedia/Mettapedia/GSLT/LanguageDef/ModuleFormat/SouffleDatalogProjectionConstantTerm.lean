import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionConstants

/-! Conditional term projection uses the actual retained child-step premise.
Its reference steps are exactly the successful constant projections, with the
projected value wrapped as an argument. Other term rules cannot fire here. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ConstantTerm

open Mettapedia.OSLF.MeTTaIL Syntax Match

def rule : RewriteRule := language.rewrites[36]'(by rw [authored_rule_count]; decide)
def call (source : Pattern) : Pattern := .apply "ProjectTerm" [.apply "dl-src:term-constant" [source]]
def result (value : Pattern) : Pattern := .apply "ValueArgument" [value]
def initial (source : Pattern) : Bindings := [("source", source)]
def extended (source value : Pattern) : Bindings := [("value", value), ("source", source)]
def premiseSource : Pattern := .apply "ProjectConstant" [.fvar "source"]
def premise : Premise := .congruence premiseSource (.fvar "value")

theorem rule_at : language.rewrites[36]? = some rule := by simp [rule]
theorem rule_left : rule.left =
    .apply "ProjectTerm" [.apply "dl-src:term-constant" [.fvar "source"]] := by decide +kernel
theorem rule_right : rule.right = .apply "ValueArgument" [.fvar "value"] := by decide +kernel
theorem rule_premises : rule.premises = [premise] := by decide +kernel

theorem match_call (source : Pattern) : matchPattern rule.left (call source) = [initial source] := by
  rw [rule_left]
  simp [call, initial, matchPattern, matchArgs, mergeBindings]

theorem source_instantiated (sites source : Pattern) :
    applyBindingsScoped sites (initial source) 0 premiseSource = .apply "ProjectConstant" [source] := by
  simp [premiseSource, initial, applyBindingsScoped_apply, applyBindingsScoped_fvar_zero, applyBindings]

theorem result_instantiated (sites source value : Pattern) :
    applyBindingsScoped sites (extended source value) 0 rule.right = result value := by
  rw [rule_right]
  simp [result, extended, applyBindingsScoped_apply, applyBindingsScoped_fvar_zero, applyBindings]

theorem step (environment : Engine.RelationEnv) {source value : Pattern}
    (projected : Reference.constant? source = some value) :
    ReferenceStep.Step environment language (call source) (result value) := by
  obtain ⟨child, childValid⟩ := (Constants.reference_exact environment source value).mpr projected
  have conditional : ReferenceStep.PremiseValid environment language (ReferenceStep.captureSites rule)
      (initial source) premise
      (.premiseStep child value [("value",value)] (extended source value)) (extended source value) := by
    refine ReferenceStep.PremiseValid.step (matched := [("value",value)]) rfl ?_ ?_ ?_
    · change ReferenceStep.StepValid environment language
        (applyBindingsScoped _ (initial source) 0 premiseSource) _ value
      rw [source_instantiated]
      exact childValid
    · simp [matchPattern]
    · simp [initial, extended, mergeBindings]
  have premises : ReferenceStep.PremisesValid environment language (ReferenceStep.captureSites rule)
      (initial source) rule.premises
      [.premiseStep child value [("value",value)] (extended source value)] (extended source value) := by
    rw [rule_premises]
    exact .cons conditional (.nil _)
  have matched : initial source ∈ ReflectiveCanonical.matchPatternForRule language rule (call source) := by
    simp only [ReflectiveCanonical.matchPatternForRule_eq_syntactic, match_call]
    exact List.mem_singleton_self _
  have valid := ReferenceStep.StepValid.rule rule_at matched premises
  rw [result_instantiated] at valid
  exact ⟨_, valid⟩

private theorem variable_rule_left :
    (language.rewrites[34]'(by rw [authored_rule_count]; decide)).left =
      .apply "ProjectTerm" [.apply "dl-src:term-variable" [.fvar "identifier"]] := by decide +kernel

private theorem anonymous_rule_left :
    (language.rewrites[35]'(by rw [authored_rule_count]; decide)).left =
      .apply "ProjectTerm" [.apply "dl-src:term-anonymous" []] := by decide +kernel

theorem step_readback (environment : Engine.RelationEnv) {source target : Pattern}
    (stepped : ReferenceStep.Step environment language (call source) target) :
    ∃ value, Reference.constant? source = some value ∧ target = result value := by
  obtain ⟨witness, valid⟩ := stepped
  cases valid with
  | @rule _ ruleIndex selected start final witnesses found matched premises =>
    have candidate := candidate_of_match found
      (by simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic, call] using matched)
    rw [term_candidates] at candidate
    simp only [List.mem_cons, List.not_mem_nil, or_false] at candidate
    rcases candidate with rfl | rfl | rfl
    · have atRule : language.rewrites[34]? =
          some (language.rewrites[34]'(by rw [authored_rule_count]; decide)) := by simp
      rw [atRule] at found
      cases Option.some.inj found
      simp only [ReflectiveCanonical.matchPatternForRule_eq_syntactic, variable_rule_left] at matched
      simp [call, matchPattern, matchArgs] at matched
    · have atRule : language.rewrites[35]? =
          some (language.rewrites[35]'(by rw [authored_rule_count]; decide)) := by simp
      rw [atRule] at found
      cases Option.some.inj found
      simp only [ReflectiveCanonical.matchPatternForRule_eq_syntactic, anonymous_rule_left] at matched
      simp [call, matchPattern, matchArgs] at matched
    · rw [rule_at] at found
      cases Option.some.inj found
      simp only [ReflectiveCanonical.matchPatternForRule_eq_syntactic, match_call, List.mem_singleton] at matched
      subst start
      rw [rule_premises] at premises
      cases premises with
      | cons conditional tail =>
        cases conditional with
        | base base _ => cases base
        | @step _ _ extension resultBindings _ childSource childTarget candidate childWitness
            endpoints child matchedValue merged =>
          simp only [premise, ReferenceStep.stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
          obtain ⟨rfl, rfl⟩ := endpoints
          change ReferenceStep.StepValid environment language
            (applyBindingsScoped _ (initial source) 0 premiseSource) _ _ at child
          rw [source_instantiated] at child
          have projected : Reference.constant? source = some candidate :=
            (Constants.reference_exact environment _ _).mp ⟨_, child⟩
          simp only [matchPattern, List.mem_singleton] at matchedValue
          subst extension
          simp [initial, mergeBindings] at merged
          cases merged
          cases tail
          exact ⟨_, projected, result_instantiated _ _ _⟩

theorem reference_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment language (call source) target ↔
      ∃ value, Reference.constant? source = some value ∧ target = result value := by
  constructor
  · exact step_readback environment
  · rintro ⟨value, projected, rfl⟩
    exact step environment projected

#print axioms match_call
#print axioms source_instantiated
#print axioms result_instantiated
#print axioms step
#print axioms step_readback
#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ConstantTerm
