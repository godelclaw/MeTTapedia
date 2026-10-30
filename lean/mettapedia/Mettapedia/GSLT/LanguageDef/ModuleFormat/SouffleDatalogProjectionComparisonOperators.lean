import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionReference
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionRules

/-! Structural compilation of the six declared comparison operators.
Operands are retained in order; evaluating comparisons is a separate layer. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ComparisonOperators

open Mettapedia.OSLF.MeTTaIL Syntax Match

def sourceHead (kind : Fin 6) : String :=
  match kind.val with
  | 0 => "dl-src:comparison-equal"
  | 1 => "dl-src:comparison-different"
  | 2 => "dl-src:comparison-less"
  | 3 => "dl-src:comparison-less-equal"
  | 4 => "dl-src:comparison-greater"
  | _ => "dl-src:comparison-greater-equal"

def targetHead (kind : Fin 6) : String :=
  match kind.val with
  | 0 => "Equal"
  | 1 => "Different"
  | 2 => "Less"
  | 3 => "LessEqual"
  | 4 => "Greater"
  | _ => "GreaterEqual"

def rule (kind : Fin 6) : RewriteRule :=
  language.rewrites[42 + kind.val]'(by rw [authored_rule_count]; have := kind.isLt; omega)
def source (kind : Fin 6) : Pattern := .apply (sourceHead kind) []
def call (operator left right : Pattern) : Pattern := .apply "ProjectComparisonOperator" [operator,left,right]
def result (kind : Fin 6) (left right : Pattern) : Pattern := .apply (targetHead kind) [left,right]
def bindings (left right : Pattern) : Bindings := [("left",left),("right",right)]

theorem rule_at (kind : Fin 6) : language.rewrites[42 + kind.val]? = some (rule kind) := by simp [rule]
theorem rule_left (kind : Fin 6) : (rule kind).left =
    .apply "ProjectComparisonOperator" [source kind,.fvar "left",.fvar "right"] := by
  fin_cases kind <;> decide +kernel
theorem rule_right (kind : Fin 6) : (rule kind).right = result kind (.fvar "left") (.fvar "right") := by
  fin_cases kind <;> decide +kernel
theorem rule_premises (kind : Fin 6) : (rule kind).premises = [] := by
  fin_cases kind <;> decide +kernel

theorem match_call (kind : Fin 6) (left right : Pattern) :
    matchPattern (rule kind).left (call (source kind) left right) = [bindings left right] := by
  rw [rule_left]
  simp [source,call,bindings,matchPattern,matchArgs,mergeBindings]

theorem result_instantiated (sites : Pattern) (kind : Fin 6) (left right : Pattern) :
    applyBindingsScoped sites (bindings left right) 0 (rule kind).right = result kind left right := by
  rw [rule_right]
  simp [result,bindings,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem step (environment : Engine.RelationEnv) (kind : Fin 6) (left right : Pattern) :
    ReferenceStep.Step environment language (call (source kind) left right) (result kind left right) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨42 + kind.val,rule kind,rule_at kind,bindings left right,?_,bindings left right,?_,
    result_instantiated _ _ _ _⟩
  · rw [match_call]
    exact List.mem_singleton_self _
  · rw [rule_premises]
    exact ⟨[],.nil _⟩

theorem reference_of_step (environment : Engine.RelationEnv) (operator left right target : Pattern)
    (stepped : ReferenceStep.Step environment language (call operator left right) target) :
    Reference.comparisonOperator? operator left right = some target := by
  obtain ⟨index,candidate,selected,found,initial,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectComparisonOperator" [operator,left,right] target).mp stepped
  rw [comparison_operator_candidates] at candidate
  have represented : ∃ kind : Fin 6, index = 42 + kind.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at candidate
    rcases candidate with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨5,rfl⟩
  obtain ⟨kind,rfl⟩ := represented
  rw [rule_at] at found
  cases Option.some.inj found
  obtain ⟨children,operatorEqual,length⟩ := first_argument_constructor_of_match
    "ProjectComparisonOperator" (sourceHead kind) [] [.fvar "left",.fvar "right"]
    (by simpa only [rule_left,source] using matched)
  have nil : children = [] := List.length_eq_zero_iff.mp length
  subst children
  subst operator
  change initial ∈ matchPattern (rule kind).left (call (source kind) left right) at matched
  have initialEqual : initial = bindings left right := by
    simpa only [match_call,List.mem_singleton] using matched
  subst initial
  rw [rule_premises] at holds
  have same := (ReferenceStep.premises_nil_iff environment language _ _ _).mp holds
  subst final
  rw [result_instantiated] at output
  rw [← output]
  fin_cases kind <;> rfl

theorem step_of_reference (environment : Engine.RelationEnv) (operator left right target : Pattern)
    (projected : Reference.comparisonOperator? operator left right = some target) :
    ReferenceStep.Step environment language (call operator left right) target := by
  unfold Reference.comparisonOperator? at projected
  split at projected
  · cases Option.some.inj projected; exact step environment 0 left right
  · cases Option.some.inj projected; exact step environment 1 left right
  · cases Option.some.inj projected; exact step environment 2 left right
  · cases Option.some.inj projected; exact step environment 3 left right
  · cases Option.some.inj projected; exact step environment 4 left right
  · cases Option.some.inj projected; exact step environment 5 left right
  · cases projected

theorem reference_exact (environment : Engine.RelationEnv) (operator left right target : Pattern) :
    ReferenceStep.Step environment language (call operator left right) target ↔
      Reference.comparisonOperator? operator left right = some target :=
  ⟨reference_of_step environment operator left right target,
    step_of_reference environment operator left right target⟩

#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ComparisonOperators
