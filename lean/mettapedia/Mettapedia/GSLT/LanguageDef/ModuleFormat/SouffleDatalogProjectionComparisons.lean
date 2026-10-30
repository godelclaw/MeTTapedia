import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionTerms
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionComparisonOperators

/-! Comparison compilation retains its left argument, right argument and
operator children in the declared premise order. No comparison is evaluated. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Comparisons

open Mettapedia.OSLF.MeTTaIL Syntax Match

def rule : RewriteRule := language.rewrites[41]'(by rw [authored_rule_count]; decide)
def call (source : Pattern) : Pattern := .apply "ProjectComparison" [source]
def source (left before operator after right : Pattern) : Pattern :=
  .apply "dl-src:comparison" [left,before,operator,after,right]
def initial (left before operator after right : Pattern) : Bindings :=
  [("before",before),("after",after),("right",right),("operator",operator),("left",left)]
def firstBindings (initial : Bindings) (first : Pattern) : Bindings := ("first",first) :: initial
def secondBindings (initial : Bindings) (first second : Pattern) : Bindings :=
  ("second",second) :: firstBindings initial first
def resultBindings (initial : Bindings) (first second result : Pattern) : Bindings :=
  ("result",result) :: secondBindings initial first second

def leftSource : Pattern := .apply "ProjectTerm" [.fvar "left"]
def rightSource : Pattern := .apply "ProjectTerm" [.fvar "right"]
def operatorSource : Pattern := .apply "ProjectComparisonOperator" [.fvar "operator",.fvar "first",.fvar "second"]
def leftPremise : Premise := .congruence leftSource (.fvar "first")
def rightPremise : Premise := .congruence rightSource (.fvar "second")
def operatorPremise : Premise := .congruence operatorSource (.fvar "result")

theorem rule_at : language.rewrites[41]? = some rule := by simp [rule]
theorem rule_left : rule.left = .apply "ProjectComparison" [.apply "dl-src:comparison"
    [.fvar "left",.fvar "before",.fvar "operator",.fvar "after",.fvar "right"]] := by decide +kernel
theorem rule_right : rule.right = .fvar "result" := by decide +kernel
theorem rule_premises : rule.premises = [leftPremise,rightPremise,operatorPremise] := by decide +kernel

theorem match_source (left before operator after right : Pattern) :
    matchPattern rule.left (call (source left before operator after right)) =
      [initial left before operator after right] := by
  rw [rule_left]
  simp [call,source,initial,matchPattern,matchArgs,mergeBindings]

theorem left_instantiated (sites left before operator after right : Pattern) :
    applyBindingsScoped sites (initial left before operator after right) 0 leftSource = Terms.call left := by
  simp [leftSource,initial,Terms.call,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem right_instantiated (sites left before operator after right first : Pattern) :
    applyBindingsScoped sites (firstBindings (initial left before operator after right) first) 0 rightSource =
      Terms.call right := by
  simp [rightSource,firstBindings,initial,Terms.call,applyBindingsScoped_apply,
    applyBindingsScoped_fvar_zero,applyBindings]

theorem operator_instantiated (sites left before operator after right first second : Pattern) :
    applyBindingsScoped sites (secondBindings (initial left before operator after right) first second) 0
      operatorSource = ComparisonOperators.call operator first second := by
  simp [operatorSource,secondBindings,firstBindings,initial,ComparisonOperators.call,
    applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem result_instantiated (sites left before operator after right first second result : Pattern) :
    applyBindingsScoped sites (resultBindings (initial left before operator after right) first second result) 0
      rule.right = result := by
  rw [rule_right]
  simp [resultBindings,applyBindingsScoped_fvar_zero,applyBindings]

theorem step (environment : Engine.RelationEnv)
    (left before operator after right first second result : Pattern)
    (leftProjected : Reference.term? left = some first)
    (rightProjected : Reference.term? right = some second)
    (operatorProjected : Reference.comparisonOperator? operator first second = some result) :
    ReferenceStep.Step environment language (call (source left before operator after right)) result := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨41,rule,rule_at,initial left before operator after right,?_,
    resultBindings (initial left before operator after right) first second result,?_,
    result_instantiated _ _ _ _ _ _ _ _ _⟩
  · rw [match_source]
    exact List.mem_singleton_self _
  · rw [rule_premises,ReferenceStep.premises_cons_iff]
    refine ⟨firstBindings (initial left before operator after right) first,?_,?_⟩
    · rw [leftPremise,ReferenceStep.congruence_iff]
      refine ⟨first,[("first",first)],?_,by simp [matchPattern],?_⟩
      · change ReferenceStep.Step environment language
          (applyBindingsScoped _ (initial left before operator after right) 0 leftSource) first
        rw [left_instantiated,Terms.reference_exact]
        exact leftProjected
      · simp [initial,firstBindings,mergeBindings]
    · rw [ReferenceStep.premises_cons_iff]
      refine ⟨secondBindings (initial left before operator after right) first second,?_,?_⟩
      · rw [rightPremise,ReferenceStep.congruence_iff]
        refine ⟨second,[("second",second)],?_,by simp [matchPattern],?_⟩
        · change ReferenceStep.Step environment language
            (applyBindingsScoped _ (firstBindings (initial left before operator after right) first) 0 rightSource) second
          rw [right_instantiated,Terms.reference_exact]
          exact rightProjected
        · simp [initial,firstBindings,secondBindings,mergeBindings]
      · rw [ReferenceStep.premises_cons_iff]
        refine ⟨resultBindings (initial left before operator after right) first second result,?_,⟨[],.nil _⟩⟩
        rw [operatorPremise,ReferenceStep.congruence_iff]
        refine ⟨result,[("result",result)],?_,by simp [matchPattern],?_⟩
        · change ReferenceStep.Step environment language
            (applyBindingsScoped _ (secondBindings (initial left before operator after right) first second) 0
              operatorSource) result
          rw [operator_instantiated,ComparisonOperators.reference_exact]
          exact operatorProjected
        · simp [initial,firstBindings,secondBindings,resultBindings,mergeBindings]

theorem reference_of_step (environment : Engine.RelationEnv) (input target : Pattern)
    (stepped : ReferenceStep.Step environment language (call input) target) :
    Reference.comparison? input = some target := by
  obtain ⟨index,candidate,selected,found,bindings,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectComparison" [input] target).mp stepped
  rw [comparison_candidates] at candidate
  have same : index = 41 := List.mem_singleton.mp candidate
  subst index
  rw [rule_at] at found
  cases Option.some.inj found
  obtain ⟨arguments,inputEqual,length⟩ := source_constructor_of_match "ProjectComparison" "dl-src:comparison"
    [.fvar "left",.fvar "before",.fvar "operator",.fvar "after",.fvar "right"]
    (by simpa only [rule_left] using matched)
  obtain ⟨left,rest,rfl,restLength⟩ := List.length_eq_succ_iff.mp length
  obtain ⟨before,operator,after,right,rfl⟩ := List.length_eq_four.mp restLength
  subst input
  change bindings ∈ matchPattern rule.left (call (source left before operator after right)) at matched
  have initialEqual : bindings = initial left before operator after right := by
    simpa only [match_source,List.mem_singleton] using matched
  subst bindings
  rw [rule_premises,ReferenceStep.premises_cons_iff] at holds
  obtain ⟨firstState,child,later⟩ := holds
  rw [leftPremise,ReferenceStep.congruence_iff] at child
  obtain ⟨first,extension,childStep,childMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (initial left before operator after right) 0 leftSource) first at childStep
  rw [left_instantiated,Terms.reference_exact] at childStep
  simp only [matchPattern,List.mem_singleton] at childMatched
  subst extension
  simp [initial,mergeBindings] at merged
  cases merged
  rw [ReferenceStep.premises_cons_iff] at later
  obtain ⟨secondState,child,later⟩ := later
  rw [rightPremise,ReferenceStep.congruence_iff] at child
  obtain ⟨second,extension,rightStep,rightMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (firstBindings (initial left before operator after right) first) 0 rightSource) second
    at rightStep
  rw [right_instantiated,Terms.reference_exact] at rightStep
  simp only [matchPattern,List.mem_singleton] at rightMatched
  subst extension
  simp [mergeBindings] at merged
  cases merged
  rw [ReferenceStep.premises_cons_iff] at later
  obtain ⟨resultState,child,remaining⟩ := later
  have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
  subst final
  rw [operatorPremise,ReferenceStep.congruence_iff] at child
  obtain ⟨result,extension,operatorStep,resultMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (secondBindings (initial left before operator after right) first second) 0 operatorSource)
    result at operatorStep
  rw [operator_instantiated,ComparisonOperators.reference_exact] at operatorStep
  simp only [matchPattern,List.mem_singleton] at resultMatched
  subst extension
  simp [mergeBindings] at merged
  cases merged
  change applyBindingsScoped _
    (resultBindings (initial left before operator after right) first second result) 0 rule.right = target at output
  rw [result_instantiated] at output
  rw [← output,Reference.comparison?]
  simp only [childStep,rightStep,Option.bind_eq_bind,Option.bind_some]
  exact operatorStep

theorem step_of_reference (environment : Engine.RelationEnv) (input target : Pattern)
    (projected : Reference.comparison? input = some target) :
    ReferenceStep.Step environment language (call input) target := by
  unfold Reference.comparison? at projected
  split at projected
  · rename_i left before operator after right
    cases leftProjected : Reference.term? left with
    | none => simp [leftProjected,Option.bind_eq_bind] at projected
    | some first =>
      cases rightProjected : Reference.term? right with
      | none => simp [leftProjected,rightProjected,Option.bind_eq_bind] at projected
      | some second =>
        simp only [leftProjected,rightProjected,Option.bind_eq_bind,Option.bind_some] at projected
        exact step environment left before operator after right first second target leftProjected rightProjected projected
  · cases projected

theorem reference_exact (environment : Engine.RelationEnv) (input target : Pattern) :
    ReferenceStep.Step environment language (call input) target ↔ Reference.comparison? input = some target :=
  ⟨reference_of_step environment input target,step_of_reference environment input target⟩

#print axioms step
#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Comparisons
