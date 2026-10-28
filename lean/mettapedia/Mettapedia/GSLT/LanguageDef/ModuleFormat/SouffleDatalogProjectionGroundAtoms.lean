import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionConstantLists

/-! Ground-atom compilation is the authored child-tuple rule. Relation-name
syntax is copied intact, and the constant-tuple proof covers arbitrary finite
arity and malformed tails. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.GroundAtoms

open Mettapedia.OSLF.MeTTaIL Syntax Match

def rule : RewriteRule := language.rewrites[27]'(by rw [authored_rule_count]; decide)
def call (source : Pattern) : Pattern := .apply "ProjectGroundAtom" [source]
def source (name before after constants : Pattern) : Pattern :=
  .apply "dl-src:ground-atom" [name,before,after,constants]
def result (name : Pattern) (values : List Pattern) : Pattern :=
  .apply "GroundFact" [Reference.relation name,Reference.groundTuple values]
def initial (name before after constants : Pattern) : Bindings :=
  [("before",before),("constants",constants),("after",after),("relation",name)]
def extended (name before after constants : Pattern) (values : List Pattern) : Bindings :=
  ("tuple",Reference.groundTuple values) :: initial name before after constants

def childSource : Pattern := .apply "ProjectConstants" [.fvar "constants"]
def premise : Premise := .congruence childSource (.fvar "tuple")

theorem rule_at : language.rewrites[27]? = some rule := by simp [rule]
theorem rule_left : rule.left = .apply "ProjectGroundAtom" [.apply "dl-src:ground-atom"
    [.fvar "relation",.fvar "before",.fvar "after",.fvar "constants"]] := by decide +kernel
theorem rule_right : rule.right = .apply "GroundFact"
    [.apply "Relation" [.fvar "relation"],.fvar "tuple"] := by decide +kernel
theorem rule_premises : rule.premises = [premise] := by decide +kernel

theorem match_source (name before after constants : Pattern) :
    matchPattern rule.left (call (source name before after constants)) = [initial name before after constants] := by
  rw [rule_left]
  simp [call,source,initial,matchPattern,matchArgs,mergeBindings]

theorem child_instantiated (sites name before after constants : Pattern) :
    applyBindingsScoped sites (initial name before after constants) 0 childSource = ConstantLists.call constants := by
  simp [childSource, initial, ConstantLists.call, applyBindingsScoped_apply,
    applyBindingsScoped_fvar_zero,applyBindings]

theorem result_instantiated (sites name before after constants : Pattern) (values : List Pattern) :
    applyBindingsScoped sites (extended name before after constants values) 0 rule.right = result name values := by
  rw [rule_right]
  simp [result,extended,initial,Reference.relation,applyBindingsScoped_apply,
    applyBindingsScoped_fvar_zero,applyBindings]

theorem step (environment : Engine.RelationEnv) (name before after constants : Pattern) (values : List Pattern)
    (projected : Reference.constants? constants = some values) :
    ReferenceStep.Step environment language (call (source name before after constants)) (result name values) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨27,rule,rule_at,initial name before after constants,?_,extended name before after constants values,?_,
    result_instantiated _ _ _ _ _ _⟩
  · rw [match_source]
    exact List.mem_singleton_self _
  · rw [rule_premises,ReferenceStep.premises_cons_iff]
    refine ⟨extended name before after constants values,?_,⟨[],.nil _⟩⟩
    rw [premise,ReferenceStep.congruence_iff]
    refine ⟨Reference.groundTuple values,[("tuple",Reference.groundTuple values)],?_,by simp [matchPattern],?_⟩
    · change ReferenceStep.Step environment language
        (applyBindingsScoped _ (initial name before after constants) 0 childSource) _
      rw [child_instantiated,ConstantLists.reference_exact,projected]
      rfl
    · simp [initial,extended,mergeBindings]

theorem reference_of_step (environment : Engine.RelationEnv) (input target : Pattern)
    (stepped : ReferenceStep.Step environment language (call input) target) :
    Reference.groundAtom? input = some target := by
  obtain ⟨index,candidate,selected,found,bindings,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectGroundAtom" [input] target).mp stepped
  rw [ground_atom_candidates] at candidate
  have same : index = 27 := List.mem_singleton.mp candidate
  subst index
  rw [rule_at] at found
  cases Option.some.inj found
  obtain ⟨arguments,inputEqual,length⟩ := source_constructor_of_match "ProjectGroundAtom" "dl-src:ground-atom"
    [.fvar "relation",.fvar "before",.fvar "after",.fvar "constants"]
    (by simpa only [rule_left] using matched)
  obtain ⟨name,before,after,constants,rfl⟩ := List.length_eq_four.mp length
  subst input
  change bindings ∈ matchPattern rule.left (call (source name before after constants)) at matched
  have initialEqual : bindings = initial name before after constants := by
    simpa only [match_source,List.mem_singleton] using matched
  subst bindings
  rw [rule_premises,ReferenceStep.premises_cons_iff] at holds
  obtain ⟨middle,child,remaining⟩ := holds
  have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
  subst final
  rw [premise,ReferenceStep.congruence_iff] at child
  obtain ⟨tuple,extension,childStep,tupleMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (initial name before after constants) 0 childSource) tuple at childStep
  rw [child_instantiated,ConstantLists.reference_exact] at childStep
  obtain ⟨values,valuesProjected,rfl⟩ := Option.map_eq_some_iff.mp childStep
  simp only [matchPattern,List.mem_singleton] at tupleMatched
  subst extension
  simp [initial,mergeBindings] at merged
  cases merged
  change applyBindingsScoped _ (extended name before after constants values) 0 rule.right = target at output
  rw [result_instantiated] at output
  rw [← output]
  change (Reference.constants? constants).map _ = some (result name values)
  rw [valuesProjected]
  rfl

theorem reference_exact (environment : Engine.RelationEnv) (input target : Pattern) :
    ReferenceStep.Step environment language (call input) target ↔ Reference.groundAtom? input = some target := by
  constructor
  · exact reference_of_step environment input target
  · intro projected
    unfold Reference.groundAtom? at projected
    split at projected
    · rename_i name before after constants
      obtain ⟨values,valuesProjected,targetEqual⟩ := Option.map_eq_some_iff.mp projected
      rw [← targetEqual]
      exact step environment name before after constants values valuesProjected
    · cases projected

#print axioms step
#print axioms reference_of_step
#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.GroundAtoms
