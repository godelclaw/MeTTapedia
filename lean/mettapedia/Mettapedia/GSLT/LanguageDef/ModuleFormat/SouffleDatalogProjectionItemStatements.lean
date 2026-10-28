import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionFacts
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionClauses

/-! Fact and rule statements prepend exactly one child result to an arbitrary
statement suffix. The selected actual rule is retained in the readback theorem. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ItemStatements

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Reference (vector program)

def rule (kind : Fin 2) : RewriteRule :=
  language.rewrites[6 + kind.val]'(by rw [authored_rule_count]; have := kind.isLt; omega)
def sourceHead (kind : Fin 2) : String := if kind.val = 0 then "dl-src:item-fact" else "dl-src:item-rule"
def childHead (kind : Fin 2) : String := if kind.val = 0 then "ProjectFact" else "ProjectRule"
def source (kind : Fin 2) (input : Pattern) : Pattern := .apply (sourceHead kind) [input]
def call (input : Pattern) (tail : List Pattern) : Pattern := .apply "ProjectItemInto" [input,program tail]
def childCall (kind : Fin 2) (input : Pattern) : Pattern := .apply (childHead kind) [input]
def childMeaning (kind : Fin 2) (input : Pattern) : Option Pattern :=
  if kind.val = 0 then Reference.fact? input else Reference.rule? input

def initial (input : Pattern) (tail : List Pattern) : Bindings := [("rest",vector tail),("source",input)]
def extended (input : Pattern) (tail : List Pattern) (result : Pattern) : Bindings :=
  ("result",result) :: initial input tail
def childSource (kind : Fin 2) : Pattern := childCall kind (.fvar "source")
def premise (kind : Fin 2) : Premise := .congruence (childSource kind) (.fvar "result")
def rhs : Pattern := .apply "Program" [.collection .vec [.fvar "result"] (some "rest")]

theorem rule_at (kind : Fin 2) : language.rewrites[6 + kind.val]? = some (rule kind) := by simp [rule]
theorem rule_left (kind : Fin 2) : (rule kind).left = .apply "ProjectItemInto"
    [source kind (.fvar "source"),.apply "Program" [.collection .vec [] (some "rest")]] := by
  fin_cases kind <;> decide +kernel
theorem rule_right (kind : Fin 2) : (rule kind).right = rhs := by fin_cases kind <;> decide +kernel
theorem rule_premises (kind : Fin 2) : (rule kind).premises = [premise kind] := by
  fin_cases kind <;> decide +kernel

theorem match_call (kind : Fin 2) (input : Pattern) (tail : List Pattern) :
    matchPattern (rule kind).left (call (source kind input) tail) = [initial input tail] := by
  rw [rule_left]
  simp [call,source,program,vector,initial,matchPattern,matchArgs,mergeBindings]

theorem child_instantiated (sites : Pattern) (kind : Fin 2) (input : Pattern) (tail : List Pattern) :
    applyBindingsScoped sites (initial input tail) 0 (childSource kind) = childCall kind input := by
  simp [childSource,childCall,initial,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem result_instantiated (sites : Pattern) (kind : Fin 2) (input result : Pattern) (tail : List Pattern) :
    applyBindingsScoped sites (extended input tail result) 0 (rule kind).right = program (result :: tail) := by
  rw [rule_right]
  have plain : binderFree rhs = true := by decide +kernel
  rw [applyBindingsScoped_zero_of_binderFree _ _ _ plain]
  simp [rhs,extended,initial,program,vector,applyBindings]

theorem child_exact (environment : Engine.RelationEnv) (kind : Fin 2) (input result : Pattern) :
    ReferenceStep.Step environment language (childCall kind input) result ↔ childMeaning kind input = some result := by
  fin_cases kind
  · exact Facts.reference_exact environment input result
  · exact Clauses.reference_exact environment input result

theorem meaning (kind : Fin 2) (input : Pattern) (tail : List Pattern) :
    Reference.itemInto? (source kind input) tail = (childMeaning kind input).map (· :: tail) := by
  fin_cases kind <;> rfl

theorem step (environment : Engine.RelationEnv) (kind : Fin 2) (input result : Pattern) (tail : List Pattern)
    (projected : childMeaning kind input = some result) :
    ReferenceStep.Step environment language (call (source kind input) tail) (program (result :: tail)) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨6 + kind.val,rule kind,rule_at kind,initial input tail,?_,extended input tail result,?_,
    result_instantiated _ _ _ _ _⟩
  · rw [match_call]
    exact List.mem_singleton_self _
  · rw [rule_premises,ReferenceStep.premises_cons_iff]
    refine ⟨extended input tail result,?_,⟨[],.nil _⟩⟩
    rw [premise,ReferenceStep.congruence_iff]
    refine ⟨result,[("result",result)],?_,by simp [matchPattern],?_⟩
    · change ReferenceStep.Step environment language
        (applyBindingsScoped _ (initial input tail) 0 (childSource kind)) result
      rw [child_instantiated,child_exact]
      exact projected
    · simp [initial,extended,mergeBindings]

theorem readback (environment : Engine.RelationEnv) (kind : Fin 2) (input target : Pattern)
    (tail : List Pattern) (bindings final : Bindings)
    (matched : bindings ∈ matchPattern (rule kind).left (call input tail))
    (holds : ∃ witnesses, ReferenceStep.PremisesValid environment language
      (ReferenceStep.captureSites (rule kind)) bindings (rule kind).premises witnesses final)
    (output : applyBindingsScoped (ReferenceStep.captureSites (rule kind)) final 0 (rule kind).right = target) :
    (Reference.itemInto? input tail).map program = some target := by
  obtain ⟨arguments,inputEqual,length⟩ := first_argument_constructor_of_match "ProjectItemInto" (sourceHead kind)
    [.fvar "source"] [.apply "Program" [.collection .vec [] (some "rest")]]
    (by simpa only [rule_left,source,call] using matched)
  obtain ⟨childInput,rfl⟩ := List.length_eq_one_iff.mp length
  subst input
  change bindings ∈ matchPattern (rule kind).left (call (source kind childInput) tail) at matched
  have initialEqual : bindings = initial childInput tail := by
    simpa only [match_call,List.mem_singleton] using matched
  subst bindings
  rw [rule_premises,ReferenceStep.premises_cons_iff] at holds
  obtain ⟨middle,child,remaining⟩ := holds
  have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
  subst final
  rw [premise,ReferenceStep.congruence_iff] at child
  obtain ⟨result,extension,childStep,resultMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (initial childInput tail) 0 (childSource kind)) result at childStep
  rw [child_instantiated,child_exact] at childStep
  simp only [matchPattern,List.mem_singleton] at resultMatched
  subst extension
  simp [initial,mergeBindings] at merged
  cases merged
  change applyBindingsScoped _ (extended childInput tail result) 0 (rule kind).right = target at output
  rw [result_instantiated] at output
  rw [← output]
  change (Reference.itemInto? (source kind childInput) tail).map program = _
  rw [meaning,childStep]
  rfl

#print axioms step
#print axioms readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ItemStatements
