import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionItems

/-! The source list is traversed right to left, threading the complete suffix
through both actual child premises. The resulting program remains in source order. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ProgramItems

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Reference (program)

def rule (kind : Fin 2) : RewriteRule :=
  language.rewrites[3 + kind.val]'(by rw [authored_rule_count]; have := kind.isLt; omega)
def call (input : Pattern) (tail : List Pattern) : Pattern := .apply "ProjectItemsInto" [input,program tail]
def empty : Pattern := .apply "dl-src:items-empty" []
def more (head gap rest : Pattern) : Pattern := .apply "dl-src:items-more" [head,gap,rest]
def emptyBindings (tail : List Pattern) : Bindings := [("tail",program tail)]
def initial (head gap rest : Pattern) (tail : List Pattern) : Bindings :=
  [("tail",program tail),("gap",gap),("rest",rest),("head",head)]
def withTail (initial : Bindings) (afterTail : List Pattern) : Bindings :=
  ("afterTail",program afterTail) :: initial
def extended (initial : Bindings) (afterTail result : List Pattern) : Bindings :=
  ("out",program result) :: withTail initial afterTail

def tailSource : Pattern := .apply "ProjectItemsInto" [.fvar "rest",.fvar "tail"]
def headSource : Pattern := .apply "ProjectItemInto" [.fvar "head",.fvar "afterTail"]
def tailPremise : Premise := .congruence tailSource (.fvar "afterTail")
def headPremise : Premise := .congruence headSource (.fvar "out")

def lhs (kind : Fin 2) : Pattern := .apply "ProjectItemsInto"
  [(if kind.val = 0 then empty else more (.fvar "head") (.fvar "gap") (.fvar "rest")),.fvar "tail"]
theorem rule_at (kind : Fin 2) : language.rewrites[3 + kind.val]? = some (rule kind) := by simp [rule]
theorem rule_left (kind : Fin 2) : (rule kind).left = lhs kind := by fin_cases kind <;> decide +kernel
theorem empty_right : (rule 0).right = .fvar "tail" := by decide +kernel
theorem more_right : (rule 1).right = .fvar "out" := by decide +kernel
theorem empty_premises : (rule 0).premises = [] := by decide +kernel
theorem more_premises : (rule 1).premises = [tailPremise,headPremise] := by decide +kernel

theorem match_empty (tail : List Pattern) :
    matchPattern (rule 0).left (call empty tail) = [emptyBindings tail] := by
  rw [rule_left]
  simp [lhs,call,empty,emptyBindings,matchPattern,matchArgs,mergeBindings]

theorem match_more (head gap rest : Pattern) (tail : List Pattern) :
    matchPattern (rule 1).left (call (more head gap rest) tail) = [initial head gap rest tail] := by
  rw [rule_left]
  simp [lhs,call,more,initial,matchPattern,matchArgs,mergeBindings]

theorem empty_instantiated (sites : Pattern) (tail : List Pattern) :
    applyBindingsScoped sites (emptyBindings tail) 0 (rule 0).right = program tail := by
  rw [empty_right]
  simp [emptyBindings,applyBindingsScoped_fvar_zero,applyBindings]

theorem result_instantiated (sites : Pattern) (initial : Bindings) (afterTail result : List Pattern) :
    applyBindingsScoped sites (extended initial afterTail result) 0 (rule 1).right = program result := by
  rw [more_right]
  simp [extended,applyBindingsScoped_fvar_zero,applyBindings]

theorem tail_instantiated (sites head gap rest : Pattern) (tail : List Pattern) :
    applyBindingsScoped sites (initial head gap rest tail) 0 tailSource = call rest tail := by
  simp [tailSource,initial,call,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem head_instantiated (sites head gap rest : Pattern) (tail afterTail : List Pattern) :
    applyBindingsScoped sites (withTail (initial head gap rest tail) afterTail) 0 headSource =
      Items.call head afterTail := by
  simp [headSource,withTail,initial,Items.call,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem empty_step (environment : Engine.RelationEnv) (tail : List Pattern) :
    ReferenceStep.Step environment language (call empty tail) (program tail) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨3,rule 0,rule_at 0,emptyBindings tail,?_,emptyBindings tail,?_,empty_instantiated _ _⟩
  · rw [match_empty]
    exact List.mem_singleton_self _
  · rw [empty_premises]
    exact ⟨[],.nil _⟩

theorem more_step (environment : Engine.RelationEnv) (head gap rest : Pattern) (tail afterTail result : List Pattern)
    (tailChild : ReferenceStep.Step environment language (call rest tail) (program afterTail))
    (headChild : ReferenceStep.Step environment language (Items.call head afterTail) (program result)) :
    ReferenceStep.Step environment language (call (more head gap rest) tail) (program result) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨4,rule 1,rule_at 1,initial head gap rest tail,?_,extended (initial head gap rest tail) afterTail result,?_,
    result_instantiated _ _ _ _⟩
  · rw [match_more]
    exact List.mem_singleton_self _
  · rw [more_premises,ReferenceStep.premises_cons_iff]
    refine ⟨withTail (initial head gap rest tail) afterTail,?_,?_⟩
    · rw [tailPremise,ReferenceStep.congruence_iff]
      refine ⟨program afterTail,[("afterTail",program afterTail)],?_,by simp [matchPattern],?_⟩
      · change ReferenceStep.Step environment language
          (applyBindingsScoped _ (initial head gap rest tail) 0 tailSource) _
        rw [tail_instantiated]
        exact tailChild
      · simp [initial,withTail,mergeBindings]
    · rw [ReferenceStep.premises_cons_iff]
      refine ⟨extended (initial head gap rest tail) afterTail result,?_,⟨[],.nil _⟩⟩
      rw [headPremise,ReferenceStep.congruence_iff]
      refine ⟨program result,[("out",program result)],?_,by simp [matchPattern],?_⟩
      · change ReferenceStep.Step environment language
          (applyBindingsScoped _ (withTail (initial head gap rest tail) afterTail) 0 headSource) _
        rw [head_instantiated]
        exact headChild
      · simp [initial,withTail,extended,mergeBindings]

theorem reference_of_step (environment : Engine.RelationEnv) (input target : Pattern) (tail : List Pattern)
    (stepped : ReferenceStep.Step environment language (call input tail) target) :
    (Reference.itemsInto? input tail).map program = some target := by
  obtain ⟨index,candidate,selected,found,bindings,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectItemsInto" [input,program tail] target).mp stepped
  rw [items_candidates] at candidate
  simp only [List.mem_cons,List.not_mem_nil,or_false] at candidate
  rcases candidate with rfl | rfl
  · have atRule : language.rewrites[3]? = some (rule 0) := rule_at 0
    rw [atRule] at found
    cases Option.some.inj found
    obtain ⟨arguments,inputEqual,length⟩ := first_argument_constructor_of_match "ProjectItemsInto"
      "dl-src:items-empty" [] [.fvar "tail"] (by simpa [rule_left,lhs,empty] using matched)
    have nil : arguments = [] := List.length_eq_zero_iff.mp length
    subst arguments
    subst input
    change bindings ∈ matchPattern (rule 0).left (call empty tail) at matched
    have initialEqual : bindings = emptyBindings tail := by simpa only [match_empty,List.mem_singleton] using matched
    subst bindings
    rw [empty_premises] at holds
    have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp holds
    subst final
    rw [empty_instantiated] at output
    rw [← output]
    rfl
  · have atRule : language.rewrites[4]? = some (rule 1) := rule_at 1
    rw [atRule] at found
    cases Option.some.inj found
    obtain ⟨arguments,inputEqual,length⟩ := first_argument_constructor_of_match "ProjectItemsInto"
      "dl-src:items-more" [.fvar "head",.fvar "gap",.fvar "rest"] [.fvar "tail"]
      (by simpa [rule_left,lhs,more] using matched)
    obtain ⟨head,gap,rest,rfl⟩ := List.length_eq_three.mp length
    subst input
    change bindings ∈ matchPattern (rule 1).left (call (more head gap rest) tail) at matched
    have initialEqual : bindings = initial head gap rest tail := by simpa only [match_more,List.mem_singleton] using matched
    subst bindings
    rw [more_premises,ReferenceStep.premises_cons_iff] at holds
    obtain ⟨middle,child,later⟩ := holds
    rw [tailPremise,ReferenceStep.congruence_iff] at child
    obtain ⟨tailResult,extension,tailStep,tailMatched,merged⟩ := child
    change ReferenceStep.Step environment language
      (applyBindingsScoped _ (initial head gap rest tail) 0 tailSource) tailResult at tailStep
    rw [tail_instantiated] at tailStep
    have tailObserved := reference_of_step environment rest tailResult tail tailStep
    obtain ⟨afterTail,tailProjected,rfl⟩ := Option.map_eq_some_iff.mp tailObserved
    simp only [matchPattern,List.mem_singleton] at tailMatched
    subst extension
    simp [initial,mergeBindings] at merged
    cases merged
    rw [ReferenceStep.premises_cons_iff] at later
    obtain ⟨last,child,remaining⟩ := later
    have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
    subst final
    rw [headPremise,ReferenceStep.congruence_iff] at child
    obtain ⟨result,extension,headStep,resultMatched,merged⟩ := child
    change ReferenceStep.Step environment language
      (applyBindingsScoped _ (withTail (initial head gap rest tail) afterTail) 0 headSource) result at headStep
    rw [head_instantiated,Items.reference_exact] at headStep
    obtain ⟨statements,headProjected,rfl⟩ := Option.map_eq_some_iff.mp headStep
    simp only [matchPattern,List.mem_singleton] at resultMatched
    subst extension
    simp [mergeBindings] at merged
    cases merged
    change applyBindingsScoped _ (extended (initial head gap rest tail) afterTail statements) 0 (rule 1).right = target
      at output
    rw [result_instantiated] at output
    rw [← output]
    change ((Reference.itemsInto? rest tail).bind (fun afterTail => Reference.itemInto? head afterTail)).map program = _
    rw [tailProjected]
    simp only [Option.bind_some,headProjected]
    rfl
termination_by sizeOf input
decreasing_by simp_all; omega

theorem step_of_reference (environment : Engine.RelationEnv) (input : Pattern) (tail result : List Pattern)
    (projected : Reference.itemsInto? input tail = some result) :
    ReferenceStep.Step environment language (call input tail) (program result) := by
  unfold Reference.itemsInto? at projected
  split at projected
  · cases Option.some.inj projected
    exact empty_step environment tail
  · rename_i head gap rest
    cases tailProjected : Reference.itemsInto? rest tail with
    | none => simp [tailProjected,Option.bind_eq_bind] at projected
    | some afterTail =>
      simp only [tailProjected,Option.bind_eq_bind,Option.bind_some] at projected
      exact more_step environment head gap rest tail afterTail result
        (step_of_reference environment rest tail afterTail tailProjected)
        (Items.step_of_reference environment head afterTail result projected)
  · cases projected
termination_by sizeOf input
decreasing_by simp_all; omega

theorem reference_exact (environment : Engine.RelationEnv) (input target : Pattern) (tail : List Pattern) :
    ReferenceStep.Step environment language (call input tail) target ↔
      (Reference.itemsInto? input tail).map program = some target :=
  ⟨reference_of_step environment input target tail,fun projected => by
    obtain ⟨result,child,rfl⟩ := Option.map_eq_some_iff.mp projected
    exact step_of_reference environment input tail result child⟩

#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ProgramItems
