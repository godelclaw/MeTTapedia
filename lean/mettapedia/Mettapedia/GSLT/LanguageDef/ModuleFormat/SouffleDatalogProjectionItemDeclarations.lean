import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionRelations

/-! A grouped declaration first compiles its attributes, then expands its
relation names over the same complete program suffix. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ItemDeclarations

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Reference (program projectedAttributes)

def rule : RewriteRule := language.rewrites[5]'(by rw [authored_rule_count]; decide)
def source (space relations before start attributes : Pattern) : Pattern :=
  .apply "dl-src:item-declaration" [.apply "dl-src:declaration" [space,relations,before,start,attributes]]
def call (input : Pattern) (tail : List Pattern) : Pattern := .apply "ProjectItemInto" [input,program tail]
def initial (space relations before start attributes : Pattern) (tail : List Pattern) : Bindings :=
  [("tail",program tail),("relations",relations),("start",start),("attributes",attributes),
    ("before",before),("space",space)]
def withAttributes (initial : Bindings) (fields : List Pattern) : Bindings :=
  ("attrs",projectedAttributes fields) :: initial
def extended (initial : Bindings) (fields result : List Pattern) : Bindings :=
  ("out",program result) :: withAttributes initial fields

def attributesSource : Pattern := .apply "ProjectAttributes" [.fvar "attributes"]
def relationsSource : Pattern := .apply "ProjectRelationsInto" [.fvar "relations",.fvar "attrs",.fvar "tail"]
def attributesPremise : Premise := .congruence attributesSource (.fvar "attrs")
def relationsPremise : Premise := .congruence relationsSource (.fvar "out")

theorem rule_at : language.rewrites[5]? = some rule := by simp [rule]
theorem rule_left : rule.left = .apply "ProjectItemInto"
    [source (.fvar "space") (.fvar "relations") (.fvar "before") (.fvar "start") (.fvar "attributes"),
      .fvar "tail"] := by decide +kernel
theorem rule_right : rule.right = .fvar "out" := by decide +kernel
theorem rule_premises : rule.premises = [attributesPremise,relationsPremise] := by decide +kernel

theorem match_source (space relations before start attributes : Pattern) (tail : List Pattern) :
    matchPattern rule.left (call (source space relations before start attributes) tail) =
      [initial space relations before start attributes tail] := by
  rw [rule_left]
  simp [call,source,initial,matchPattern,matchArgs,mergeBindings]

theorem attributes_instantiated (sites space relations before start attributes : Pattern) (tail : List Pattern) :
    applyBindingsScoped sites (initial space relations before start attributes tail) 0 attributesSource =
      AttributeLists.call attributes := by
  simp [attributesSource,initial,AttributeLists.call,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem relations_instantiated (sites space relations before start attributes : Pattern)
    (tail fields : List Pattern) :
    applyBindingsScoped sites (withAttributes (initial space relations before start attributes tail) fields) 0
      relationsSource = Relations.call relations fields tail := by
  simp [relationsSource,withAttributes,initial,Relations.call,applyBindingsScoped_apply,
    applyBindingsScoped_fvar_zero,applyBindings]

theorem result_instantiated (sites : Pattern) (initial : Bindings) (fields result : List Pattern) :
    applyBindingsScoped sites (extended initial fields result) 0 rule.right = program result := by
  rw [rule_right]
  simp [extended,applyBindingsScoped_fvar_zero,applyBindings]

theorem meaning (space relations before start attributes : Pattern) (tail : List Pattern) :
    Reference.itemInto? (source space relations before start attributes) tail =
      (Reference.attributes? attributes).bind (fun fields => Reference.relationsInto? relations fields tail) := rfl

theorem step (environment : Engine.RelationEnv) (space relations before start attributes : Pattern)
    (tail fields result : List Pattern) (fieldsProjected : Reference.attributes? attributes = some fields)
    (relationsProjected : Reference.relationsInto? relations fields tail = some result) :
    ReferenceStep.Step environment language (call (source space relations before start attributes) tail)
      (program result) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨5,rule,rule_at,initial space relations before start attributes tail,?_,
    extended (initial space relations before start attributes tail) fields result,?_,result_instantiated _ _ _ _⟩
  · rw [match_source]
    exact List.mem_singleton_self _
  · rw [rule_premises,ReferenceStep.premises_cons_iff]
    refine ⟨withAttributes (initial space relations before start attributes tail) fields,?_,?_⟩
    · rw [attributesPremise,ReferenceStep.congruence_iff]
      refine ⟨projectedAttributes fields,[("attrs",projectedAttributes fields)],?_,by simp [matchPattern],?_⟩
      · change ReferenceStep.Step environment language
          (applyBindingsScoped _ (initial space relations before start attributes tail) 0 attributesSource) _
        rw [attributes_instantiated,AttributeLists.reference_exact,fieldsProjected]
        rfl
      · simp [initial,withAttributes,mergeBindings]
    · rw [ReferenceStep.premises_cons_iff]
      refine ⟨extended (initial space relations before start attributes tail) fields result,?_,⟨[],.nil _⟩⟩
      rw [relationsPremise,ReferenceStep.congruence_iff]
      refine ⟨program result,[("out",program result)],?_,by simp [matchPattern],?_⟩
      · change ReferenceStep.Step environment language
          (applyBindingsScoped _ (withAttributes (initial space relations before start attributes tail) fields) 0
            relationsSource) _
        rw [relations_instantiated,Relations.reference_exact,relationsProjected]
        rfl
      · simp [initial,withAttributes,extended,mergeBindings]

theorem readback (environment : Engine.RelationEnv) (input target : Pattern) (tail : List Pattern)
    (bindings final : Bindings) (matched : bindings ∈ matchPattern rule.left (call input tail))
    (holds : ∃ witnesses, ReferenceStep.PremisesValid environment language
      (ReferenceStep.captureSites rule) bindings rule.premises witnesses final)
    (output : applyBindingsScoped (ReferenceStep.captureSites rule) final 0 rule.right = target) :
    (Reference.itemInto? input tail).map program = some target := by
  obtain ⟨arguments,inputEqual,length⟩ := nested_first_argument_constructor_of_match
    "ProjectItemInto" "dl-src:item-declaration" "dl-src:declaration"
    [.fvar "space",.fvar "relations",.fvar "before",.fvar "start",.fvar "attributes"] [.fvar "tail"]
    (by simpa only [rule_left,source,call] using matched)
  obtain ⟨space,rest,rfl,restLength⟩ := List.length_eq_succ_iff.mp length
  obtain ⟨relations,before,start,attributes,rfl⟩ := List.length_eq_four.mp restLength
  subst input
  change bindings ∈ matchPattern rule.left (call (source space relations before start attributes) tail) at matched
  have initialEqual : bindings = initial space relations before start attributes tail := by
    simpa only [match_source,List.mem_singleton] using matched
  subst bindings
  rw [rule_premises,ReferenceStep.premises_cons_iff] at holds
  obtain ⟨middle,child,later⟩ := holds
  rw [attributesPremise,ReferenceStep.congruence_iff] at child
  obtain ⟨fieldsResult,extension,fieldsStep,fieldsMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (initial space relations before start attributes tail) 0 attributesSource) fieldsResult at fieldsStep
  rw [attributes_instantiated,AttributeLists.reference_exact] at fieldsStep
  obtain ⟨fields,fieldsProjected,rfl⟩ := Option.map_eq_some_iff.mp fieldsStep
  simp only [matchPattern,List.mem_singleton] at fieldsMatched
  subst extension
  simp [initial,mergeBindings] at merged
  cases merged
  rw [ReferenceStep.premises_cons_iff] at later
  obtain ⟨last,child,remaining⟩ := later
  have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
  subst final
  rw [relationsPremise,ReferenceStep.congruence_iff] at child
  obtain ⟨result,extension,relationsStep,resultMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (withAttributes (initial space relations before start attributes tail) fields) 0 relationsSource)
    result at relationsStep
  rw [relations_instantiated,Relations.reference_exact] at relationsStep
  obtain ⟨statements,relationsProjected,rfl⟩ := Option.map_eq_some_iff.mp relationsStep
  simp only [matchPattern,List.mem_singleton] at resultMatched
  subst extension
  simp [mergeBindings] at merged
  cases merged
  change applyBindingsScoped _ (extended (initial space relations before start attributes tail) fields statements)
    0 rule.right = target at output
  rw [result_instantiated] at output
  rw [← output]
  change (Reference.itemInto? (source space relations before start attributes) tail).map program = _
  rw [meaning,fieldsProjected]
  simp only [Option.bind_some,relationsProjected]
  rfl

#print axioms step
#print axioms readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ItemDeclarations
