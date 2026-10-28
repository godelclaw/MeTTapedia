import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionProgramItems

/-! Whole structural program projection agrees in both directions with the
actual authored rules. Unsupported shapes cannot acquire a successful result.
This theorem does not interpret literals or grant full Datalog admission. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Program

open Mettapedia.OSLF.MeTTaIL Syntax Match

def rule : RewriteRule := language.rewrites[2]'(by rw [authored_rule_count]; decide)
def source (leading items : Pattern) : Pattern := .apply "dl-src:program" [leading,items]
def call (input : Pattern) : Pattern := .apply "ProjectProgram" [input]
def initial (leading items : Pattern) : Bindings := [("items",items),("leading",leading)]
def extended (leading items target : Pattern) : Bindings := ("out",target) :: initial leading items

def childSource : Pattern := .apply "ProjectItemsInto" [.fvar "items",Reference.program []]
def premise : Premise := .congruence childSource (.fvar "out")

theorem rule_at : language.rewrites[2]? = some rule := by simp [rule]
theorem rule_left : rule.left = .apply "ProjectProgram" [.apply "dl-src:program" [.fvar "leading",.fvar "items"]] := by
  decide +kernel
theorem rule_right : rule.right = .fvar "out" := by decide +kernel
theorem rule_premises : rule.premises = [premise] := by decide +kernel

theorem match_source (leading items : Pattern) :
    matchPattern rule.left (call (source leading items)) = [initial leading items] := by
  rw [rule_left]
  simp [call,source,initial,matchPattern,matchArgs,mergeBindings]

theorem child_instantiated (sites leading items : Pattern) :
    applyBindingsScoped sites (initial leading items) 0 childSource = ProgramItems.call items [] := by
  have plain : binderFree childSource = true := by decide +kernel
  rw [applyBindingsScoped_zero_of_binderFree _ _ _ plain]
  simp [childSource,initial,ProgramItems.call,Reference.program,Reference.vector,applyBindings]

theorem result_instantiated (sites leading items target : Pattern) :
    applyBindingsScoped sites (extended leading items target) 0 rule.right = target := by
  rw [rule_right]
  simp [extended,applyBindingsScoped_fvar_zero,applyBindings]

theorem step (environment : Engine.RelationEnv) (leading items : Pattern) (statements : List Pattern)
    (projected : Reference.itemsInto? items [] = some statements) :
    ReferenceStep.Step environment language (call (source leading items)) (Reference.program statements) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨2,rule,rule_at,initial leading items,?_,extended leading items (Reference.program statements),?_,
    result_instantiated _ _ _ _⟩
  · rw [match_source]
    exact List.mem_singleton_self _
  · rw [rule_premises,ReferenceStep.premises_cons_iff]
    refine ⟨extended leading items (Reference.program statements),?_,⟨[],.nil _⟩⟩
    rw [premise,ReferenceStep.congruence_iff]
    refine ⟨Reference.program statements,[("out",Reference.program statements)],?_,by simp [matchPattern],?_⟩
    · change ReferenceStep.Step environment language
        (applyBindingsScoped _ (initial leading items) 0 childSource) _
      rw [child_instantiated,ProgramItems.reference_exact,projected]
      rfl
    · simp [initial,extended,mergeBindings]

theorem reference_of_step (environment : Engine.RelationEnv) (input target : Pattern)
    (stepped : ReferenceStep.Step environment language (call input) target) :
    Reference.projectProgram? input = some target := by
  obtain ⟨index,candidate,selected,found,bindings,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectProgram" [input] target).mp stepped
  rw [program_candidates] at candidate
  have same : index = 2 := List.mem_singleton.mp candidate
  subst index
  rw [rule_at] at found
  cases Option.some.inj found
  obtain ⟨arguments,inputEqual,length⟩ := source_constructor_of_match "ProjectProgram" "dl-src:program"
    [.fvar "leading",.fvar "items"] (by simpa only [rule_left] using matched)
  obtain ⟨leading,items,rfl⟩ := List.length_eq_two.mp length
  subst input
  change bindings ∈ matchPattern rule.left (call (source leading items)) at matched
  have initialEqual : bindings = initial leading items := by simpa only [match_source,List.mem_singleton] using matched
  subst bindings
  rw [rule_premises,ReferenceStep.premises_cons_iff] at holds
  obtain ⟨middle,child,remaining⟩ := holds
  have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
  subst final
  rw [premise,ReferenceStep.congruence_iff] at child
  obtain ⟨result,extension,childStep,resultMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (initial leading items) 0 childSource) result at childStep
  rw [child_instantiated,ProgramItems.reference_exact] at childStep
  simp only [matchPattern,List.mem_singleton] at resultMatched
  subst extension
  simp [initial,mergeBindings] at merged
  cases merged
  change applyBindingsScoped _ (extended leading items result) 0 rule.right = target at output
  rw [result_instantiated] at output
  rw [← output]
  exact childStep

theorem step_of_reference (environment : Engine.RelationEnv) (input target : Pattern)
    (projected : Reference.projectProgram? input = some target) :
    ReferenceStep.Step environment language (call input) target := by
  unfold Reference.projectProgram? at projected
  split at projected
  · rename_i leading items
    obtain ⟨statements,child,rfl⟩ := Option.map_eq_some_iff.mp projected
    exact step environment leading items statements child
  · cases projected

theorem reference_exact (environment : Engine.RelationEnv) (input target : Pattern) :
    ReferenceStep.Step environment language (call input) target ↔ Reference.projectProgram? input = some target :=
  ⟨reference_of_step environment input target,step_of_reference environment input target⟩

theorem functional (environment : Engine.RelationEnv) (input first second : Pattern)
    (left : ReferenceStep.Step environment language (call input) first)
    (right : ReferenceStep.Step environment language (call input) second) : first = second :=
  Option.some.inj ((reference_of_step environment input first left).symm.trans
    (reference_of_step environment input second right))

#print axioms reference_exact
#print axioms functional

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Program
