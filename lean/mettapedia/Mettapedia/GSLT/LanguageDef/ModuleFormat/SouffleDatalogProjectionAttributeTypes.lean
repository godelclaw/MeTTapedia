import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionReference
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionRules

/-! The four authored primitive type projections agree with their independent
structural reading. Unknown constructors and non-nullary forms have no result. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.AttributeTypes

open Mettapedia.OSLF.MeTTaIL Syntax Match

def sourceHead (kind : Fin 4) : String :=
  match kind.val with
  | 0 => "dl-src:type-symbol"
  | 1 => "dl-src:type-number"
  | 2 => "dl-src:type-unsigned"
  | _ => "dl-src:type-float"
def targetHead (kind : Fin 4) : String :=
  match kind.val with
  | 0 => "SymbolType"
  | 1 => "NumberType"
  | 2 => "UnsignedType"
  | _ => "FloatType"
def rule (kind : Fin 4) : RewriteRule :=
  language.rewrites[16 + kind.val]'(by rw [authored_rule_count]; have := kind.isLt; omega)
def source (kind : Fin 4) : Pattern := .apply (sourceHead kind) []
def call (input : Pattern) : Pattern := .apply "ProjectAttributeType" [input]
def result (kind : Fin 4) : Pattern := .apply (targetHead kind) []

theorem rule_at (kind : Fin 4) : language.rewrites[16 + kind.val]? = some (rule kind) := by simp [rule]
theorem rule_left (kind : Fin 4) : (rule kind).left = call (source kind) := by
  fin_cases kind <;> decide +kernel
theorem rule_right (kind : Fin 4) : (rule kind).right = result kind := by
  fin_cases kind <;> decide +kernel
theorem rule_premises (kind : Fin 4) : (rule kind).premises = [] := by
  fin_cases kind <;> decide +kernel

theorem match_call (kind : Fin 4) : matchPattern (rule kind).left (call (source kind)) = [[]] := by
  rw [rule_left]
  simp [source,call,matchPattern,matchArgs,mergeBindings]

theorem result_instantiated (sites : Pattern) (kind : Fin 4) :
    applyBindingsScoped sites [] 0 (rule kind).right = result kind := by
  rw [rule_right]
  simp [result,applyBindingsScoped_apply]

theorem step (environment : Engine.RelationEnv) (kind : Fin 4) :
    ReferenceStep.Step environment language (call (source kind)) (result kind) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨16 + kind.val,rule kind,rule_at kind,[],?_,[],?_,result_instantiated _ _⟩
  · rw [match_call]
    exact List.mem_singleton_self _
  · rw [rule_premises]
    exact ⟨[],.nil _⟩

theorem reference_of_step (environment : Engine.RelationEnv) (input target : Pattern)
    (stepped : ReferenceStep.Step environment language (call input) target) :
    Reference.attributeType? input = some target := by
  obtain ⟨index,candidate,selected,found,initial,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectAttributeType" [input] target).mp stepped
  rw [attribute_type_candidates] at candidate
  have represented : ∃ kind : Fin 4, index = 16 + kind.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at candidate
    rcases candidate with rfl | rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  obtain ⟨kind,rfl⟩ := represented
  rw [rule_at] at found
  cases Option.some.inj found
  obtain ⟨children,inputEqual,length⟩ := source_constructor_of_match
    "ProjectAttributeType" (sourceHead kind) [] (by simpa only [rule_left,call,source] using matched)
  have nil : children = [] := List.length_eq_zero_iff.mp length
  subst children
  subst input
  change initial ∈ matchPattern (rule kind).left (call (source kind)) at matched
  have initialEqual : initial = [] := by simpa only [match_call,List.mem_singleton] using matched
  subst initial
  rw [rule_premises] at holds
  have same := (ReferenceStep.premises_nil_iff environment language _ _ _).mp holds
  subst final
  rw [result_instantiated] at output
  rw [← output]
  fin_cases kind <;> rfl

theorem step_of_reference (environment : Engine.RelationEnv) (input target : Pattern)
    (projected : Reference.attributeType? input = some target) :
    ReferenceStep.Step environment language (call input) target := by
  unfold Reference.attributeType? at projected
  split at projected
  · cases Option.some.inj projected; exact step environment 0
  · cases Option.some.inj projected; exact step environment 1
  · cases Option.some.inj projected; exact step environment 2
  · cases Option.some.inj projected; exact step environment 3
  · cases projected

theorem reference_exact (environment : Engine.RelationEnv) (input target : Pattern) :
    ReferenceStep.Step environment language (call input) target ↔ Reference.attributeType? input = some target :=
  ⟨reference_of_step environment input target,step_of_reference environment input target⟩

#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.AttributeTypes
