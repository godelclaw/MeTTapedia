import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
import Mettapedia.OSLF.MeTTaIL.ReferenceStepRuleViews

/-! Source-independent fact enumeration. The two authored rules enumerate an
ordered vector; a compiled clause filters their results with its own atom
pattern, sharing the clause's variable bindings across premises. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

namespace DatalogLookupAuthoring
open DatalogAuthoring
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../../../../metta/gslt/module/DatalogIRLookup.module"
#module_roundtrip DatalogIRLookup
end DatalogLookupAuthoring

namespace DatalogIR.Lookup

open Mettapedia.OSLF.MeTTaIL Syntax Match
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def language? : Option LanguageDef := DatalogLookupAuthoring.DatalogIRLookup.language.toOption
def language : LanguageDef := module_language_view% language?
theorem language_exact : language? = some language := by decide +kernel

def here : RewriteRule := language.rewrites[0]'(by decide +kernel)
def later : RewriteRule := language.rewrites[1]'(by decide +kernel)
def vector (facts : List Pattern) : Pattern := .collection .vec facts none
def call (facts : List Pattern) : Pattern := .apply "LookupFact" [vector facts]
def initial (fact : Pattern) (rest : List Pattern) : Bindings := [("rest",vector rest),("fact",fact)]
def extended (fact : Pattern) (rest : List Pattern) (result : Pattern) : Bindings :=
  ("result",result) :: initial fact rest

def childSource : Pattern := .apply "LookupFact" [.fvar "rest"]
def premise : Premise := .congruence childSource (.fvar "result")

theorem here_at : language.rewrites[0]? = some here := by simp [here]
theorem later_at : language.rewrites[1]? = some later := by simp [later]
theorem here_left : here.left = .apply "LookupFact" [.collection .vec [.fvar "fact"] (some "rest")] := by decide +kernel
theorem later_left : later.left = here.left := by decide +kernel
theorem here_right : here.right = .fvar "fact" := by decide +kernel
theorem later_right : later.right = .fvar "result" := by decide +kernel
theorem here_premises : here.premises = [] := by decide +kernel
theorem later_premises : later.premises = [premise] := by decide +kernel

theorem match_here (fact : Pattern) (rest : List Pattern) :
    matchPattern here.left (call (fact :: rest)) = [initial fact rest] := by
  rw [here_left]
  simp [call,vector,initial,matchPattern,matchArgs,mergeBindings]

theorem match_later (fact : Pattern) (rest : List Pattern) :
    matchPattern later.left (call (fact :: rest)) = [initial fact rest] := by
  rw [later_left]
  exact match_here fact rest

theorem child_instantiated (sites fact : Pattern) (rest : List Pattern) :
    applyBindingsScoped sites (initial fact rest) 0 childSource = call rest := by
  simp [childSource,initial,call,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem here_instantiated (sites fact : Pattern) (rest : List Pattern) :
    applyBindingsScoped sites (initial fact rest) 0 here.right = fact := by
  rw [here_right]
  simp [initial,applyBindingsScoped_fvar_zero,applyBindings]

theorem later_instantiated (sites fact result : Pattern) (rest : List Pattern) :
    applyBindingsScoped sites (extended fact rest result) 0 later.right = result := by
  rw [later_right]
  simp [extended,applyBindingsScoped_fvar_zero,applyBindings]

theorem here_step (environment : Engine.RelationEnv) (fact : Pattern) (rest : List Pattern) :
    ReferenceStep.Step environment language (call (fact :: rest)) fact := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨0,here,here_at,initial fact rest,?_,initial fact rest,?_,here_instantiated _ _ _⟩
  · rw [match_here]; exact List.mem_singleton_self _
  · rw [here_premises]; exact ⟨[],.nil _⟩

theorem later_step (environment : Engine.RelationEnv) (fact result : Pattern) (rest : List Pattern)
    (child : ReferenceStep.Step environment language (call rest) result) :
    ReferenceStep.Step environment language (call (fact :: rest)) result := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨1,later,later_at,initial fact rest,?_,extended fact rest result,?_,later_instantiated _ _ _ _⟩
  · rw [match_later]; exact List.mem_singleton_self _
  · rw [later_premises,ReferenceStep.premises_cons_iff]
    refine ⟨extended fact rest result,?_,⟨[],.nil _⟩⟩
    rw [premise,ReferenceStep.congruence_iff]
    refine ⟨result,[("result",result)],?_,by simp [matchPattern],?_⟩
    · change ReferenceStep.Step environment language
        (applyBindingsScoped _ (initial fact rest) 0 childSource) result
      rw [child_instantiated]; exact child
    · simp [initial,extended,mergeBindings]

theorem member_step (environment : Engine.RelationEnv) {facts : List Pattern} {result : Pattern}
    (member : result ∈ facts) : ReferenceStep.Step environment language (call facts) result := by
  induction facts with
  | nil => cases member
  | cons fact rest ih =>
    rcases List.mem_cons.mp member with rfl | present
    · exact here_step environment result rest
    · exact later_step environment fact result rest (ih present)

theorem step_member (environment : Engine.RelationEnv) (facts : List Pattern) (result : Pattern)
    (stepped : ReferenceStep.Step environment language (call facts) result) : result ∈ facts := by
  induction facts generalizing result with
  | nil =>
    obtain ⟨index,rule,found,bindings,matched,rest⟩ :=
      (ReferenceStep.step_rule_iff environment language _ _).mp stepped
    have bound := (List.getElem?_eq_some_iff.mp found).1
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl
    · rw [here_at] at found
      cases Option.some.inj found
      simp [here_left,call,vector,matchPattern,matchArgs] at matched
    · rw [later_at] at found
      cases Option.some.inj found
      simp [later_left,here_left,call,vector,matchPattern,matchArgs] at matched
  | cons fact rest ih =>
    obtain ⟨index,rule,found,bindings,matched,final,holds,output⟩ :=
      (ReferenceStep.step_rule_iff environment language _ _).mp stepped
    have bound := (List.getElem?_eq_some_iff.mp found).1
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl
    · rw [here_at] at found
      cases Option.some.inj found
      have initialEqual : bindings = initial fact rest := by
        simpa only [match_here,List.mem_singleton] using matched
      subst bindings
      rw [here_premises] at holds
      have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp holds
      subst final
      rw [here_instantiated] at output
      rw [← output]
      exact List.mem_cons_self
    · rw [later_at] at found
      cases Option.some.inj found
      have initialEqual : bindings = initial fact rest := by
        simpa only [match_later,List.mem_singleton] using matched
      subst bindings
      rw [later_premises,ReferenceStep.premises_cons_iff] at holds
      obtain ⟨middle,child,remaining⟩ := holds
      have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
      subst final
      rw [premise,ReferenceStep.congruence_iff] at child
      obtain ⟨candidate,extension,childStep,candidateMatched,merged⟩ := child
      change ReferenceStep.Step environment language
        (applyBindingsScoped _ (initial fact rest) 0 childSource) candidate at childStep
      rw [child_instantiated] at childStep
      have present := ih candidate childStep
      simp only [matchPattern,List.mem_singleton] at candidateMatched
      subst extension
      simp [initial,mergeBindings] at merged
      cases merged
      change applyBindingsScoped _ (extended fact rest candidate) 0 later.right = result at output
      rw [later_instantiated] at output
      rw [← output]
      exact List.mem_cons_of_mem _ present

theorem reference_exact (environment : Engine.RelationEnv) (facts : List Pattern) (result : Pattern) :
    ReferenceStep.Step environment language (call facts) result ↔ result ∈ facts :=
  ⟨step_member environment facts result,member_step environment⟩

#guard language.rewrites.length == 2
#guard language.validate.isEmpty

#print axioms member_step
#print axioms reference_exact

end DatalogIR.Lookup
end Mettapedia.GSLT.LanguageDef.ModuleFormat
