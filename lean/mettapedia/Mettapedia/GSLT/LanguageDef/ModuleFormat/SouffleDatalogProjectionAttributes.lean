import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionAttributeTypes

/-! An attribute preserves its identifier and compiles its declared type through
the actual child rule, retaining that child in the source witness. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Attributes

open Mettapedia.OSLF.MeTTaIL Syntax Match

def rule : RewriteRule := language.rewrites[15]'(by rw [authored_rule_count]; decide)
def call (input : Pattern) : Pattern := .apply "ProjectAttribute" [input]
def source (identifier before after sourceType : Pattern) : Pattern :=
  .apply "dl-src:attr" [identifier,before,after,sourceType]
def result (identifier targetType : Pattern) : Pattern := .apply "Attribute" [identifier,targetType]
def initial (identifier before after sourceType : Pattern) : Bindings :=
  [("before",before),("sourceType",sourceType),("after",after),("identifier",identifier)]
def extended (identifier before after sourceType targetType : Pattern) : Bindings :=
  ("targetType",targetType) :: initial identifier before after sourceType

def childSource : Pattern := .apply "ProjectAttributeType" [.fvar "sourceType"]
def premise : Premise := .congruence childSource (.fvar "targetType")

theorem rule_at : language.rewrites[15]? = some rule := by simp [rule]
theorem rule_left : rule.left = .apply "ProjectAttribute" [.apply "dl-src:attr"
    [.fvar "identifier",.fvar "before",.fvar "after",.fvar "sourceType"]] := by decide +kernel
theorem rule_right : rule.right = .apply "Attribute" [.fvar "identifier",.fvar "targetType"] := by decide +kernel
theorem rule_premises : rule.premises = [premise] := by decide +kernel

theorem match_source (identifier before after sourceType : Pattern) :
    matchPattern rule.left (call (source identifier before after sourceType)) =
      [initial identifier before after sourceType] := by
  rw [rule_left]
  simp [call,source,initial,matchPattern,matchArgs,mergeBindings]

theorem child_instantiated (sites identifier before after sourceType : Pattern) :
    applyBindingsScoped sites (initial identifier before after sourceType) 0 childSource =
      AttributeTypes.call sourceType := by
  simp [childSource,initial,AttributeTypes.call,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem result_instantiated (sites identifier before after sourceType targetType : Pattern) :
    applyBindingsScoped sites (extended identifier before after sourceType targetType) 0 rule.right =
      result identifier targetType := by
  rw [rule_right]
  simp [result,extended,initial,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem step (environment : Engine.RelationEnv) (identifier before after sourceType targetType : Pattern)
    (projected : Reference.attributeType? sourceType = some targetType) :
    ReferenceStep.Step environment language (call (source identifier before after sourceType))
      (result identifier targetType) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨15,rule,rule_at,initial identifier before after sourceType,?_,
    extended identifier before after sourceType targetType,?_,result_instantiated _ _ _ _ _ _⟩
  · rw [match_source]
    exact List.mem_singleton_self _
  · rw [rule_premises,ReferenceStep.premises_cons_iff]
    refine ⟨extended identifier before after sourceType targetType,?_,⟨[],.nil _⟩⟩
    rw [premise,ReferenceStep.congruence_iff]
    refine ⟨targetType,[("targetType",targetType)],?_,by simp [matchPattern],?_⟩
    · change ReferenceStep.Step environment language
        (applyBindingsScoped _ (initial identifier before after sourceType) 0 childSource) _
      rw [child_instantiated,AttributeTypes.reference_exact]
      exact projected
    · simp [initial,extended,mergeBindings]

theorem reference_of_step (environment : Engine.RelationEnv) (input target : Pattern)
    (stepped : ReferenceStep.Step environment language (call input) target) :
    Reference.attribute? input = some target := by
  obtain ⟨index,candidate,selected,found,bindings,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectAttribute" [input] target).mp stepped
  rw [attribute_candidates] at candidate
  have same : index = 15 := List.mem_singleton.mp candidate
  subst index
  rw [rule_at] at found
  cases Option.some.inj found
  obtain ⟨arguments,inputEqual,length⟩ := source_constructor_of_match "ProjectAttribute" "dl-src:attr"
    [.fvar "identifier",.fvar "before",.fvar "after",.fvar "sourceType"]
    (by simpa only [rule_left] using matched)
  obtain ⟨identifier,before,after,sourceType,rfl⟩ := List.length_eq_four.mp length
  subst input
  change bindings ∈ matchPattern rule.left (call (source identifier before after sourceType)) at matched
  have initialEqual : bindings = initial identifier before after sourceType := by
    simpa only [match_source,List.mem_singleton] using matched
  subst bindings
  rw [rule_premises,ReferenceStep.premises_cons_iff] at holds
  obtain ⟨middle,child,remaining⟩ := holds
  have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
  subst final
  rw [premise,ReferenceStep.congruence_iff] at child
  obtain ⟨targetType,extension,childStep,resultMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (initial identifier before after sourceType) 0 childSource) targetType at childStep
  rw [child_instantiated,AttributeTypes.reference_exact] at childStep
  simp only [matchPattern,List.mem_singleton] at resultMatched
  subst extension
  simp [initial,mergeBindings] at merged
  cases merged
  change applyBindingsScoped _ (extended identifier before after sourceType targetType) 0 rule.right = target at output
  rw [result_instantiated] at output
  rw [← output]
  change (Reference.attributeType? sourceType).map _ = some (result identifier targetType)
  rw [childStep]
  rfl

theorem reference_exact (environment : Engine.RelationEnv) (input target : Pattern) :
    ReferenceStep.Step environment language (call input) target ↔ Reference.attribute? input = some target := by
  constructor
  · exact reference_of_step environment input target
  · intro projected
    unfold Reference.attribute? at projected
    split at projected
    · rename_i identifier before after sourceType
      obtain ⟨targetType,child,targetEqual⟩ := Option.map_eq_some_iff.mp projected
      rw [← targetEqual]
      exact step environment identifier before after sourceType targetType child
    · cases projected

#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Attributes
