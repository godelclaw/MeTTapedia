import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionAttributeLists

/-! Grouped relation declarations compile through their actual recursive rule.
The theorem quantifies over arbitrary attribute and statement suffix vectors,
so declaration order and duplicates are preserved. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Relations

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Reference (vector program projectedAttributes declaration)

def rule (kind : Fin 2) : RewriteRule :=
  language.rewrites[10 + kind.val]'(by rw [authored_rule_count]; have := kind.isLt; omega)
def call (input : Pattern) (attributes tail : List Pattern) : Pattern :=
  .apply "ProjectRelationsInto" [input,projectedAttributes attributes,program tail]
def one (identifier : Pattern) : Pattern := .apply "dl-src:relations-one" [identifier]
def more (identifier before after rest : Pattern) : Pattern :=
  .apply "dl-src:relations-more" [identifier,before,after,rest]
def oneBindings (identifier : Pattern) (attributes tail : List Pattern) : Bindings :=
  [("attrs",vector attributes),("rest",vector tail),("identifier",identifier)]
def moreBindings (identifier before after rest : Pattern) (attributes tail : List Pattern) : Bindings :=
  [("attrs",vector attributes),("tail",program tail),("before",before),("relations",rest),
    ("after",after),("identifier",identifier)]
def extended (identifier before after rest : Pattern) (attributes tail result : List Pattern) : Bindings :=
  ("rest",vector result) :: moreBindings identifier before after rest attributes tail

def childSource : Pattern := .apply "ProjectRelationsInto"
  [.fvar "relations",.apply "ProjectedAttributes" [.fvar "attrs"],.fvar "tail"]
def premise : Premise := .congruence childSource (.apply "Program" [.fvar "rest"])
def lhs (kind : Fin 2) : Pattern :=
  if kind.val = 0 then .apply "ProjectRelationsInto"
    [.apply "dl-src:relations-one" [.fvar "identifier"],.apply "ProjectedAttributes" [.fvar "attrs"],
      .apply "Program" [.collection .vec [] (some "rest")]]
  else .apply "ProjectRelationsInto"
    [.apply "dl-src:relations-more" [.fvar "identifier",.fvar "before",.fvar "after",.fvar "relations"],
      .apply "ProjectedAttributes" [.fvar "attrs"],.fvar "tail"]
def rhs : Pattern := .apply "Program" [.collection .vec
  [.apply "Declaration" [.apply "RelationDeclaration"
    [.apply "Relation" [.apply "dl-src:qualified-name-one" [.fvar "identifier"]],.fvar "attrs"]]] (some "rest")]

theorem rule_at (kind : Fin 2) : language.rewrites[10 + kind.val]? = some (rule kind) := by simp [rule]
theorem rule_left (kind : Fin 2) : (rule kind).left = lhs kind := by fin_cases kind <;> decide +kernel
theorem rule_right (kind : Fin 2) : (rule kind).right = rhs := by fin_cases kind <;> decide +kernel
theorem one_premises : (rule 0).premises = [] := by decide +kernel
theorem more_premises : (rule 1).premises = [premise] := by decide +kernel

theorem match_one (identifier : Pattern) (attributes tail : List Pattern) :
    matchPattern (rule 0).left (call (one identifier) attributes tail) = [oneBindings identifier attributes tail] := by
  rw [rule_left]
  simp [lhs,call,one,oneBindings,projectedAttributes,program,vector,matchPattern,matchArgs,mergeBindings]

theorem match_more (identifier before after rest : Pattern) (attributes tail : List Pattern) :
    matchPattern (rule 1).left (call (more identifier before after rest) attributes tail) =
      [moreBindings identifier before after rest attributes tail] := by
  rw [rule_left]
  simp [lhs,call,more,moreBindings,projectedAttributes,program,vector,matchPattern,matchArgs,mergeBindings]

theorem rhs_plain (sites : Pattern) (bindings : Bindings) (kind : Fin 2) :
    applyBindingsScoped sites bindings 0 (rule kind).right = applyBindings bindings rhs := by
  rw [rule_right]
  apply applyBindingsScoped_zero_of_binderFree
  decide +kernel

theorem one_instantiated (sites identifier : Pattern) (attributes tail : List Pattern) :
    applyBindingsScoped sites (oneBindings identifier attributes tail) 0 (rule 0).right =
      program (declaration identifier attributes :: tail) := by
  rw [rhs_plain]
  simp [rhs,oneBindings,declaration,Reference.relation,program,vector,applyBindings]

theorem more_instantiated (sites identifier before after rest : Pattern) (attributes tail result : List Pattern) :
    applyBindingsScoped sites (extended identifier before after rest attributes tail result) 0 (rule 1).right =
      program (declaration identifier attributes :: result) := by
  rw [rhs_plain]
  simp [rhs,extended,moreBindings,declaration,Reference.relation,program,vector,applyBindings]

theorem child_instantiated (sites identifier before after rest : Pattern) (attributes tail : List Pattern) :
    applyBindingsScoped sites (moreBindings identifier before after rest attributes tail) 0 childSource =
      call rest attributes tail := by
  simp [childSource,call,moreBindings,projectedAttributes,applyBindingsScoped_apply,
    applyBindingsScoped_fvar_zero,applyBindings]

theorem one_step (environment : Engine.RelationEnv) (identifier : Pattern) (attributes tail : List Pattern) :
    ReferenceStep.Step environment language (call (one identifier) attributes tail)
      (program (declaration identifier attributes :: tail)) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨10,rule 0,rule_at 0,oneBindings identifier attributes tail,?_,oneBindings identifier attributes tail,?_,
    one_instantiated _ _ _ _⟩
  · rw [match_one]
    exact List.mem_singleton_self _
  · rw [one_premises]
    exact ⟨[],.nil _⟩

theorem more_step (environment : Engine.RelationEnv) (identifier before after rest : Pattern)
    (attributes tail result : List Pattern)
    (child : ReferenceStep.Step environment language (call rest attributes tail) (program result)) :
    ReferenceStep.Step environment language (call (more identifier before after rest) attributes tail)
      (program (declaration identifier attributes :: result)) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨11,rule 1,rule_at 1,moreBindings identifier before after rest attributes tail,?_,
    extended identifier before after rest attributes tail result,?_,more_instantiated _ _ _ _ _ _ _ _⟩
  · rw [match_more]
    exact List.mem_singleton_self _
  · rw [more_premises,ReferenceStep.premises_cons_iff]
    refine ⟨extended identifier before after rest attributes tail result,?_,⟨[],.nil _⟩⟩
    rw [premise,ReferenceStep.congruence_iff]
    refine ⟨program result,[("rest",vector result)],?_,?_,?_⟩
    · change ReferenceStep.Step environment language
        (applyBindingsScoped _ (moreBindings identifier before after rest attributes tail) 0 childSource) _
      rw [child_instantiated]
      exact child
    · simp [program,matchPattern,matchArgs,mergeBindings]
    · simp [extended,moreBindings,mergeBindings]

theorem reference_of_step (environment : Engine.RelationEnv) (input target : Pattern) (attributes tail : List Pattern)
    (stepped : ReferenceStep.Step environment language (call input attributes tail) target) :
    ∃ result, Reference.relationsInto? input attributes tail = some result ∧ target = program result := by
  obtain ⟨index,candidate,selected,found,bindings,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectRelationsInto" [input,projectedAttributes attributes,program tail] target).mp stepped
  rw [relations_candidates] at candidate
  simp only [List.mem_cons,List.not_mem_nil,or_false] at candidate
  rcases candidate with rfl | rfl
  · have atRule : language.rewrites[10]? = some (rule 0) := rule_at 0
    rw [atRule] at found
    cases Option.some.inj found
    obtain ⟨arguments,inputEqual,length⟩ := first_argument_constructor_of_match "ProjectRelationsInto"
      "dl-src:relations-one" [.fvar "identifier"]
      [.apply "ProjectedAttributes" [.fvar "attrs"],.apply "Program" [.collection .vec [] (some "rest")]]
      (by simpa [rule_left,lhs] using matched)
    obtain ⟨identifier,rfl⟩ := List.length_eq_one_iff.mp length
    subst input
    change bindings ∈ matchPattern (rule 0).left (call (one identifier) attributes tail) at matched
    have initialEqual : bindings = oneBindings identifier attributes tail := by
      simpa only [match_one,List.mem_singleton] using matched
    subst bindings
    rw [one_premises] at holds
    have same := (ReferenceStep.premises_nil_iff environment language _ _ _).mp holds
    subst final
    rw [one_instantiated] at output
    exact ⟨_,rfl,output.symm⟩
  · have atRule : language.rewrites[11]? = some (rule 1) := rule_at 1
    rw [atRule] at found
    cases Option.some.inj found
    obtain ⟨arguments,inputEqual,length⟩ := first_argument_constructor_of_match "ProjectRelationsInto"
      "dl-src:relations-more" [.fvar "identifier",.fvar "before",.fvar "after",.fvar "relations"]
      [.apply "ProjectedAttributes" [.fvar "attrs"],.fvar "tail"]
      (by simpa [rule_left,lhs] using matched)
    obtain ⟨identifier,before,after,rest,rfl⟩ := List.length_eq_four.mp length
    subst input
    change bindings ∈ matchPattern (rule 1).left (call (more identifier before after rest) attributes tail) at matched
    have initialEqual : bindings = moreBindings identifier before after rest attributes tail := by
      simpa only [match_more,List.mem_singleton] using matched
    subst bindings
    rw [more_premises,ReferenceStep.premises_cons_iff] at holds
    obtain ⟨middle,child,remaining⟩ := holds
    have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
    subst final
    rw [premise,ReferenceStep.congruence_iff] at child
    obtain ⟨candidate,extension,childStep,resultMatched,merged⟩ := child
    change ReferenceStep.Step environment language
      (applyBindingsScoped _ (moreBindings identifier before after rest attributes tail) 0 childSource) candidate at childStep
    rw [child_instantiated] at childStep
    obtain ⟨result,resultProjected,rfl⟩ := reference_of_step environment rest candidate attributes tail childStep
    simp [program,matchPattern,matchArgs,mergeBindings] at resultMatched
    subst extension
    simp [mergeBindings] at merged
    cases merged
    change applyBindingsScoped _ (extended identifier before after rest attributes tail result) 0 (rule 1).right = target
      at output
    rw [more_instantiated] at output
    refine ⟨declaration identifier attributes :: result,?_,output.symm⟩
    change (Reference.relationsInto? rest attributes tail).map _ = _
    rw [resultProjected]
    rfl
termination_by sizeOf input
decreasing_by simp_all; omega

theorem step_of_reference (environment : Engine.RelationEnv) (input : Pattern) (attributes tail result : List Pattern)
    (projected : Reference.relationsInto? input attributes tail = some result) :
    ReferenceStep.Step environment language (call input attributes tail) (program result) := by
  unfold Reference.relationsInto? at projected
  split at projected
  · cases Option.some.inj projected
    exact one_step environment _ attributes tail
  · rename_i identifier before after rest
    obtain ⟨values,child,rfl⟩ := Option.map_eq_some_iff.mp projected
    exact more_step environment identifier before after rest attributes tail values
      (step_of_reference environment rest attributes tail values child)
  · cases projected
termination_by sizeOf input
decreasing_by simp_all; omega

theorem reference_exact (environment : Engine.RelationEnv) (input target : Pattern) (attributes tail : List Pattern) :
    ReferenceStep.Step environment language (call input attributes tail) target ↔
      (Reference.relationsInto? input attributes tail).map program = some target := by
  constructor
  · intro stepped
    obtain ⟨result,projected,rfl⟩ := reference_of_step environment input target attributes tail stepped
    rw [projected]
    rfl
  · intro projected
    obtain ⟨result,child,rfl⟩ := Option.map_eq_some_iff.mp projected
    exact step_of_reference environment input attributes tail result child

#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Relations
