import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionConstantTerm

/-! Complete structural argument projection for variables, anonymous arguments
and constants. Identifier and literal subtrees retain their original contents. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Terms

open Mettapedia.OSLF.MeTTaIL Syntax Match

def variableRule : RewriteRule := language.rewrites[34]'(by rw [authored_rule_count]; decide)
def anonymousRule : RewriteRule := language.rewrites[35]'(by rw [authored_rule_count]; decide)
def call (source : Pattern) : Pattern := .apply "ProjectTerm" [source]
def variableSource (identifier : Pattern) : Pattern := .apply "dl-src:term-variable" [identifier]
def anonymous : Pattern := .apply "dl-src:term-anonymous" []
def variableResult (identifier : Pattern) : Pattern :=
  .apply "VariableArgument" [.apply "Variable" [identifier]]
def anonymousResult : Pattern := .apply "AnonymousArgument" []
def variableBindings (identifier : Pattern) : Bindings := [("identifier",identifier)]

theorem variable_at : language.rewrites[34]? = some variableRule := by simp [variableRule]
theorem anonymous_at : language.rewrites[35]? = some anonymousRule := by simp [anonymousRule]
theorem variable_left : variableRule.left =
    .apply "ProjectTerm" [.apply "dl-src:term-variable" [.fvar "identifier"]] := by decide +kernel
theorem anonymous_left : anonymousRule.left = .apply "ProjectTerm" [anonymous] := by decide +kernel
theorem variable_right : variableRule.right =
    .apply "VariableArgument" [.apply "Variable" [.fvar "identifier"]] := by decide +kernel
theorem anonymous_right : anonymousRule.right = anonymousResult := by decide +kernel
theorem variable_premises : variableRule.premises = [] := by decide +kernel
theorem anonymous_premises : anonymousRule.premises = [] := by decide +kernel

theorem variable_match (identifier : Pattern) :
    matchPattern variableRule.left (call (variableSource identifier)) = [variableBindings identifier] := by
  rw [variable_left]
  simp [call,variableSource,variableBindings,matchPattern,matchArgs,mergeBindings]

theorem anonymous_match : matchPattern anonymousRule.left (call anonymous) = [[]] := by
  rw [anonymous_left]
  decide +kernel

theorem variable_instantiated (sites identifier : Pattern) :
    applyBindingsScoped sites (variableBindings identifier) 0 variableRule.right = variableResult identifier := by
  rw [variable_right]
  simp [variableResult,variableBindings,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem anonymous_instantiated (sites : Pattern) :
    applyBindingsScoped sites [] 0 anonymousRule.right = anonymousResult := by
  rw [anonymous_right]
  simp [anonymousResult,applyBindingsScoped_apply]

theorem variable_step (environment : Engine.RelationEnv) (identifier : Pattern) :
    ReferenceStep.Step environment language (call (variableSource identifier)) (variableResult identifier) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨34,variableRule,variable_at,variableBindings identifier,?_,variableBindings identifier,?_,
    variable_instantiated _ _⟩
  · rw [variable_match]
    exact List.mem_singleton_self _
  · rw [variable_premises]
    exact ⟨[],.nil _⟩

theorem anonymous_step (environment : Engine.RelationEnv) :
    ReferenceStep.Step environment language (call anonymous) anonymousResult := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨35,anonymousRule,anonymous_at,[],?_,[],?_,anonymous_instantiated _⟩
  · rw [anonymous_match]
    exact List.mem_singleton_self _
  · rw [anonymous_premises]
    exact ⟨[],.nil _⟩

theorem reference_of_step (environment : Engine.RelationEnv) (source target : Pattern)
    (stepped : ReferenceStep.Step environment language (call source) target) :
    Reference.term? source = some target := by
  obtain ⟨index,candidate,selected,found,initial,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectTerm" [source] target).mp stepped
  rw [term_candidates] at candidate
  simp only [List.mem_cons,List.not_mem_nil,or_false] at candidate
  rcases candidate with rfl | rfl | rfl
  · rw [variable_at] at found
    cases Option.some.inj found
    obtain ⟨arguments,sourceEqual,length⟩ := source_constructor_of_match "ProjectTerm" "dl-src:term-variable"
      [.fvar "identifier"] (by simpa only [variable_left] using matched)
    obtain ⟨identifier,rfl⟩ := List.length_eq_one_iff.mp length
    subst source
    change initial ∈ matchPattern variableRule.left (call (variableSource identifier)) at matched
    have initialEqual : initial = variableBindings identifier := by
      simpa only [variable_match,List.mem_singleton] using matched
    subst initial
    rw [variable_premises] at holds
    have same := (ReferenceStep.premises_nil_iff environment language _ _ _).mp holds
    subst final
    rw [variable_instantiated] at output
    rw [← output]
    rfl
  · rw [anonymous_at] at found
    cases Option.some.inj found
    obtain ⟨arguments,sourceEqual,length⟩ := source_constructor_of_match "ProjectTerm" "dl-src:term-anonymous" []
      (by simpa only [anonymous_left,anonymous] using matched)
    have nil : arguments = [] := List.length_eq_zero_iff.mp length
    subst arguments
    subst source
    change initial ∈ matchPattern anonymousRule.left (call anonymous) at matched
    have initialEqual : initial = [] := by simpa only [anonymous_match,List.mem_singleton] using matched
    subst initial
    rw [anonymous_premises] at holds
    have same := (ReferenceStep.premises_nil_iff environment language _ _ _).mp holds
    subst final
    rw [anonymous_instantiated] at output
    rw [← output]
    rfl
  · rw [ConstantTerm.rule_at] at found
    cases Option.some.inj found
    obtain ⟨arguments,sourceEqual,length⟩ := source_constructor_of_match "ProjectTerm" "dl-src:term-constant"
      [.fvar "source"] (by simpa only [ConstantTerm.rule_left] using matched)
    obtain ⟨literal,rfl⟩ := List.length_eq_one_iff.mp length
    subst source
    have actual : ReferenceStep.Step environment language (ConstantTerm.call literal) target := stepped
    obtain ⟨value,projected,rfl⟩ := ConstantTerm.step_readback environment actual
    change (Reference.constant? literal).map _ = some (ConstantTerm.result value)
    rw [projected]
    rfl

theorem step_of_reference (environment : Engine.RelationEnv) (source target : Pattern)
    (projected : Reference.term? source = some target) :
    ReferenceStep.Step environment language (call source) target := by
  unfold Reference.term? at projected
  split at projected
  · cases Option.some.inj projected
    exact variable_step environment _
  · cases Option.some.inj projected
    exact anonymous_step environment
  · obtain ⟨value,child,rfl⟩ := Option.map_eq_some_iff.mp projected
    exact ConstantTerm.step environment child
  · cases projected

theorem reference_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment language (call source) target ↔ Reference.term? source = some target :=
  ⟨reference_of_step environment source target,step_of_reference environment source target⟩

#print axioms reference_of_step
#print axioms step_of_reference
#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Terms
