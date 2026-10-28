import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionReference
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionRules

/-! Input and output directives retain their relation syntax and prepend one
statement to the supplied program suffix. Layout fields have no output effect. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ItemDirectives

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Reference (vector program)

def rule (kind : Fin 2) : RewriteRule :=
  language.rewrites[8 + kind.val]'(by rw [authored_rule_count]; have := kind.isLt; omega)
def outerHead (kind : Fin 2) : String := if kind.val = 0 then "dl-src:item-input" else "dl-src:item-output"
def innerHead (kind : Fin 2) : String := if kind.val = 0 then "dl-src:input" else "dl-src:output"
def targetHead (kind : Fin 2) : String := if kind.val = 0 then "InputRelation" else "OutputRelation"
def source (kind : Fin 2) (space relation : Pattern) : Pattern :=
  .apply (outerHead kind) [.apply (innerHead kind) [space,relation]]
def call (input : Pattern) (tail : List Pattern) : Pattern := .apply "ProjectItemInto" [input,program tail]
def statement (kind : Fin 2) (relation : Pattern) : Pattern := .apply (targetHead kind) [Reference.relation relation]
def initial (space relation : Pattern) (tail : List Pattern) : Bindings :=
  [("rest",vector tail),("relation",relation),("space",space)]
def rhs (kind : Fin 2) : Pattern := .apply "Program"
  [.collection .vec [statement kind (.fvar "relation")] (some "rest")]

theorem rule_at (kind : Fin 2) : language.rewrites[8 + kind.val]? = some (rule kind) := by simp [rule]
theorem rule_left (kind : Fin 2) : (rule kind).left = .apply "ProjectItemInto"
    [source kind (.fvar "space") (.fvar "relation"),.apply "Program" [.collection .vec [] (some "rest")]] := by
  fin_cases kind <;> decide +kernel
theorem rule_right (kind : Fin 2) : (rule kind).right = rhs kind := by fin_cases kind <;> decide +kernel
theorem rule_premises (kind : Fin 2) : (rule kind).premises = [] := by fin_cases kind <;> decide +kernel

theorem match_call (kind : Fin 2) (space relation : Pattern) (tail : List Pattern) :
    matchPattern (rule kind).left (call (source kind space relation) tail) = [initial space relation tail] := by
  rw [rule_left]
  simp [call,source,program,vector,initial,matchPattern,matchArgs,mergeBindings]

theorem result_instantiated (sites : Pattern) (kind : Fin 2) (space relation : Pattern) (tail : List Pattern) :
    applyBindingsScoped sites (initial space relation tail) 0 (rule kind).right =
      program (statement kind relation :: tail) := by
  rw [rule_right]
  have plain : binderFree (rhs kind) = true := by fin_cases kind <;> decide +kernel
  rw [applyBindingsScoped_zero_of_binderFree _ _ _ plain]
  simp [rhs,statement,Reference.relation,initial,program,vector,applyBindings]

theorem meaning (kind : Fin 2) (space relation : Pattern) (tail : List Pattern) :
    Reference.itemInto? (source kind space relation) tail = some (statement kind relation :: tail) := by
  fin_cases kind <;> rfl

theorem step (environment : Engine.RelationEnv) (kind : Fin 2) (space relation : Pattern) (tail : List Pattern) :
    ReferenceStep.Step environment language (call (source kind space relation) tail)
      (program (statement kind relation :: tail)) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨8 + kind.val,rule kind,rule_at kind,initial space relation tail,?_,initial space relation tail,?_,
    result_instantiated _ _ _ _ _⟩
  · rw [match_call]
    exact List.mem_singleton_self _
  · rw [rule_premises]
    exact ⟨[],.nil _⟩

theorem readback (environment : Engine.RelationEnv) (kind : Fin 2) (input target : Pattern)
    (tail : List Pattern) (bindings final : Bindings)
    (matched : bindings ∈ matchPattern (rule kind).left (call input tail))
    (holds : ∃ witnesses, ReferenceStep.PremisesValid environment language
      (ReferenceStep.captureSites (rule kind)) bindings (rule kind).premises witnesses final)
    (output : applyBindingsScoped (ReferenceStep.captureSites (rule kind)) final 0 (rule kind).right = target) :
    (Reference.itemInto? input tail).map program = some target := by
  obtain ⟨arguments,inputEqual,length⟩ := nested_first_argument_constructor_of_match
    "ProjectItemInto" (outerHead kind) (innerHead kind) [.fvar "space",.fvar "relation"]
    [.apply "Program" [.collection .vec [] (some "rest")]]
    (by simpa only [rule_left,source,call] using matched)
  obtain ⟨space,relation,rfl⟩ := List.length_eq_two.mp length
  subst input
  change bindings ∈ matchPattern (rule kind).left (call (source kind space relation) tail) at matched
  have initialEqual : bindings = initial space relation tail := by
    simpa only [match_call,List.mem_singleton] using matched
  subst bindings
  rw [rule_premises] at holds
  have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp holds
  subst final
  rw [result_instantiated] at output
  rw [← output]
  change (Reference.itemInto? (source kind space relation) tail).map program = _
  rw [meaning]
  rfl

#print axioms step
#print axioms readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ItemDirectives
