import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionBodies

/-! A complete positive clause retains its atom head and ordered body. Child
results are unpacked only through the actual declared premise patterns. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Clauses

open Mettapedia.OSLF.MeTTaIL Syntax Match

def rule : RewriteRule := language.rewrites[21]'(by rw [authored_rule_count]; decide)
def call (input : Pattern) : Pattern := .apply "ProjectRule" [input]
def source (head before after body : Pattern) : Pattern := .apply "dl-src:rule" [head,before,after,body]
def result (relation tuple : Pattern) (literals : List Pattern) : Pattern :=
  .apply "PositiveRule" [.apply "Clause" [relation,tuple,Reference.vector literals]]
def initial (head before after body : Pattern) : Bindings :=
  [("before",before),("body",body),("after",after),("head",head)]
def withHead (initial : Bindings) (relation tuple : Pattern) : Bindings :=
  ("relation",relation) :: ("tuple",tuple) :: initial
def withBody (initial : Bindings) (relation tuple : Pattern) (literals : List Pattern) : Bindings :=
  ("literals",Reference.vector literals) :: withHead initial relation tuple

def headSource : Pattern := .apply "ProjectAtom" [.fvar "head"]
def bodySource : Pattern := .apply "ProjectBody" [.fvar "body"]
def headPremise : Premise := .congruence headSource (.apply "PositiveAtom" [.fvar "relation",.fvar "tuple"])
def bodyPremise : Premise := .congruence bodySource (.apply "ProjectedBody" [.fvar "literals"])

theorem rule_at : language.rewrites[21]? = some rule := by simp [rule]
theorem rule_left : rule.left = .apply "ProjectRule" [.apply "dl-src:rule"
    [.fvar "head",.fvar "before",.fvar "after",.fvar "body"]] := by decide +kernel
theorem rule_right : rule.right = .apply "PositiveRule" [.apply "Clause"
    [.fvar "relation",.fvar "tuple",.fvar "literals"]] := by decide +kernel
theorem rule_premises : rule.premises = [headPremise,bodyPremise] := by decide +kernel

theorem match_source (head before after body : Pattern) :
    matchPattern rule.left (call (source head before after body)) = [initial head before after body] := by
  rw [rule_left]
  simp [call,source,initial,matchPattern,matchArgs,mergeBindings]

theorem head_instantiated (sites head before after body : Pattern) :
    applyBindingsScoped sites (initial head before after body) 0 headSource = Atoms.call head := by
  simp [headSource,initial,Atoms.call,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem body_instantiated (sites head before after body relation tuple : Pattern) :
    applyBindingsScoped sites (withHead (initial head before after body) relation tuple) 0 bodySource =
      Bodies.call body := by
  simp [bodySource,withHead,initial,Bodies.call,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem result_instantiated (sites head before after body relation tuple : Pattern) (literals : List Pattern) :
    applyBindingsScoped sites (withBody (initial head before after body) relation tuple literals) 0 rule.right =
      result relation tuple literals := by
  rw [rule_right]
  simp [result,withBody,withHead,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem step (environment : Engine.RelationEnv) (head before after body relation tuple : Pattern)
    (literals : List Pattern) (headProjected : Reference.atom? head = some (relation,tuple))
    (bodyProjected : Reference.body? body = some literals) :
    ReferenceStep.Step environment language (call (source head before after body)) (result relation tuple literals) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨21,rule,rule_at,initial head before after body,?_,
    withBody (initial head before after body) relation tuple literals,?_,result_instantiated _ _ _ _ _ _ _ _⟩
  · rw [match_source]
    exact List.mem_singleton_self _
  · rw [rule_premises,ReferenceStep.premises_cons_iff]
    refine ⟨withHead (initial head before after body) relation tuple,?_,?_⟩
    · rw [headPremise,ReferenceStep.congruence_iff]
      refine ⟨Atoms.wrap (relation,tuple),[("tuple",tuple),("relation",relation)],?_,?_,?_⟩
      · change ReferenceStep.Step environment language
          (applyBindingsScoped _ (initial head before after body) 0 headSource) _
        rw [head_instantiated,Atoms.reference_exact,headProjected]
        rfl
      · simp [Atoms.wrap,matchPattern,matchArgs,mergeBindings]
      · simp [initial,withHead,mergeBindings]
    · rw [ReferenceStep.premises_cons_iff]
      refine ⟨withBody (initial head before after body) relation tuple literals,?_,⟨[],.nil _⟩⟩
      rw [bodyPremise,ReferenceStep.congruence_iff]
      refine ⟨Reference.projectedBody literals,[("literals",Reference.vector literals)],?_,?_,?_⟩
      · change ReferenceStep.Step environment language
          (applyBindingsScoped _ (withHead (initial head before after body) relation tuple) 0 bodySource) _
        rw [body_instantiated,Bodies.reference_exact,bodyProjected]
        rfl
      · simp [Reference.projectedBody,matchPattern,matchArgs,mergeBindings]
      · simp [initial,withHead,withBody,mergeBindings]

theorem reference_of_step (environment : Engine.RelationEnv) (input target : Pattern)
    (stepped : ReferenceStep.Step environment language (call input) target) :
    Reference.rule? input = some target := by
  obtain ⟨index,candidate,selected,found,bindings,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectRule" [input] target).mp stepped
  rw [rule_candidates] at candidate
  have same : index = 21 := List.mem_singleton.mp candidate
  subst index
  rw [rule_at] at found
  cases Option.some.inj found
  obtain ⟨arguments,inputEqual,length⟩ := source_constructor_of_match "ProjectRule" "dl-src:rule"
    [.fvar "head",.fvar "before",.fvar "after",.fvar "body"]
    (by simpa only [rule_left] using matched)
  obtain ⟨head,before,after,body,rfl⟩ := List.length_eq_four.mp length
  subst input
  change bindings ∈ matchPattern rule.left (call (source head before after body)) at matched
  have initialEqual : bindings = initial head before after body := by
    simpa only [match_source,List.mem_singleton] using matched
  subst bindings
  rw [rule_premises,ReferenceStep.premises_cons_iff] at holds
  obtain ⟨middle,child,later⟩ := holds
  rw [headPremise,ReferenceStep.congruence_iff] at child
  obtain ⟨headResult,extension,headStep,headMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (initial head before after body) 0 headSource) headResult at headStep
  rw [head_instantiated,Atoms.reference_exact] at headStep
  obtain ⟨⟨relation,tuple⟩,headProjected,rfl⟩ := Option.map_eq_some_iff.mp headStep
  simp [Atoms.wrap,matchPattern,matchArgs,mergeBindings] at headMatched
  subst extension
  simp [initial,mergeBindings] at merged
  cases merged
  rw [ReferenceStep.premises_cons_iff] at later
  obtain ⟨last,child,remaining⟩ := later
  have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
  subst final
  rw [bodyPremise,ReferenceStep.congruence_iff] at child
  obtain ⟨bodyResult,extension,bodyStep,bodyMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (withHead (initial head before after body) relation tuple) 0 bodySource) bodyResult at bodyStep
  rw [body_instantiated,Bodies.reference_exact] at bodyStep
  obtain ⟨literals,bodyProjected,rfl⟩ := Option.map_eq_some_iff.mp bodyStep
  simp [Reference.projectedBody,matchPattern,matchArgs,mergeBindings] at bodyMatched
  subst extension
  simp [mergeBindings] at merged
  cases merged
  change applyBindingsScoped _ (withBody (initial head before after body) relation tuple literals) 0 rule.right = target
    at output
  rw [result_instantiated] at output
  rw [← output,Reference.rule?]
  simp only [headProjected,bodyProjected,Option.bind_eq_bind,Option.bind_some]
  rfl

theorem step_of_reference (environment : Engine.RelationEnv) (input target : Pattern)
    (projected : Reference.rule? input = some target) :
    ReferenceStep.Step environment language (call input) target := by
  unfold Reference.rule? at projected
  split at projected
  · rename_i head before after body
    cases headProjected : Reference.atom? head with
    | none => simp [headProjected,Option.bind_eq_bind] at projected
    | some headResult =>
      obtain ⟨relation,tuple⟩ := headResult
      cases bodyProjected : Reference.body? body with
      | none => simp [headProjected,bodyProjected,Option.bind_eq_bind] at projected
      | some literals =>
        simp only [headProjected,bodyProjected,Option.bind_eq_bind,Option.bind_some] at projected
        cases Option.some.inj projected
        exact step environment head before after body relation tuple literals headProjected bodyProjected
  · cases projected

theorem reference_exact (environment : Engine.RelationEnv) (input target : Pattern) :
    ReferenceStep.Step environment language (call input) target ↔ Reference.rule? input = some target :=
  ⟨reference_of_step environment input target,step_of_reference environment input target⟩

#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Clauses
