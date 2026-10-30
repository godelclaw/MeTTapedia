import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionAtoms
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionComparisons

/-! The two positive-literal rules retain the actual atom or comparison child.
The atom result is returned unchanged; a comparison receives its declared wrapper. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.PositiveLiterals

open Mettapedia.OSLF.MeTTaIL Syntax Match

def rule (kind : Fin 2) : RewriteRule :=
  language.rewrites[24 + kind.val]'(by rw [authored_rule_count]; have := kind.isLt; omega)
def sourceHead (kind : Fin 2) : String :=
  if kind.val = 0 then "dl-src:positive-atom" else "dl-src:positive-comparison"
def key (kind : Fin 2) : String := if kind.val = 0 then "atom" else "comparison"
def childHead (kind : Fin 2) : String := if kind.val = 0 then "ProjectAtom" else "ProjectComparison"
def source (kind : Fin 2) (input : Pattern) : Pattern := .apply (sourceHead kind) [input]
def call (input : Pattern) : Pattern := .apply "ProjectPositiveLiteral" [input]
def childCall (kind : Fin 2) (input : Pattern) : Pattern := .apply (childHead kind) [input]
def initial (kind : Fin 2) (input : Pattern) : Bindings := [(key kind,input)]
def extended (kind : Fin 2) (input result : Pattern) : Bindings := ("result",result) :: initial kind input

def output (kind : Fin 2) (result : Pattern) : Pattern :=
  if kind.val = 0 then result else .apply "Comparison" [result]
def childMeaning (kind : Fin 2) (input : Pattern) : Option Pattern :=
  if kind.val = 0 then (Reference.atom? input).map Atoms.wrap else Reference.comparison? input

def childSource (kind : Fin 2) : Pattern := childCall kind (.fvar (key kind))
def premise (kind : Fin 2) : Premise := .congruence (childSource kind) (.fvar "result")

theorem rule_at (kind : Fin 2) : language.rewrites[24 + kind.val]? = some (rule kind) := by simp [rule]
theorem rule_left (kind : Fin 2) : (rule kind).left = call (source kind (.fvar (key kind))) := by
  fin_cases kind <;> decide +kernel
theorem rule_right (kind : Fin 2) : (rule kind).right = output kind (.fvar "result") := by
  fin_cases kind <;> decide +kernel
theorem rule_premises (kind : Fin 2) : (rule kind).premises = [premise kind] := by
  fin_cases kind <;> decide +kernel

theorem match_call (kind : Fin 2) (input : Pattern) :
    matchPattern (rule kind).left (call (source kind input)) = [initial kind input] := by
  rw [rule_left]
  simp [call,source,initial,matchPattern,matchArgs,mergeBindings]

theorem merge_result (kind : Fin 2) (input result : Pattern) :
    mergeBindings (initial kind input) [("result",result)] = some (extended kind input result) := by
  fin_cases kind <;> simp [initial,extended,key,mergeBindings]

theorem child_instantiated (sites : Pattern) (kind : Fin 2) (input : Pattern) :
    applyBindingsScoped sites (initial kind input) 0 (childSource kind) = childCall kind input := by
  simp [childSource,childCall,initial,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem result_instantiated (sites : Pattern) (kind : Fin 2) (input result : Pattern) :
    applyBindingsScoped sites (extended kind input result) 0 (rule kind).right = output kind result := by
  rw [rule_right]
  fin_cases kind <;> simp [output,extended,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem child_exact (environment : Engine.RelationEnv) (kind : Fin 2) (input result : Pattern) :
    ReferenceStep.Step environment language (childCall kind input) result ↔ childMeaning kind input = some result := by
  fin_cases kind
  · exact Atoms.reference_exact environment input result
  · exact Comparisons.reference_exact environment input result

theorem meaning (kind : Fin 2) (input : Pattern) :
    Reference.positiveLiteral? (source kind input) = (childMeaning kind input).map (output kind) := by
  fin_cases kind
  · change (Reference.atom? input).map (fun atom => .apply "PositiveAtom" [atom.1,atom.2]) =
      ((Reference.atom? input).map Atoms.wrap).map (output 0)
    cases Reference.atom? input with
    | none => rfl
    | some atom => cases atom; rfl
  · rfl

theorem step (environment : Engine.RelationEnv) (kind : Fin 2) (input result : Pattern)
    (projected : childMeaning kind input = some result) :
    ReferenceStep.Step environment language (call (source kind input)) (output kind result) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨24 + kind.val,rule kind,rule_at kind,initial kind input,?_,extended kind input result,?_,
    result_instantiated _ _ _ _⟩
  · rw [match_call]
    exact List.mem_singleton_self _
  · rw [rule_premises,ReferenceStep.premises_cons_iff]
    refine ⟨extended kind input result,?_,⟨[],.nil _⟩⟩
    rw [premise,ReferenceStep.congruence_iff]
    refine ⟨result,[("result",result)],?_,by simp [matchPattern],merge_result _ _ _⟩
    change ReferenceStep.Step environment language
      (applyBindingsScoped _ (initial kind input) 0 (childSource kind)) result
    rw [child_instantiated,child_exact]
    exact projected

theorem reference_of_step (environment : Engine.RelationEnv) (input target : Pattern)
    (stepped : ReferenceStep.Step environment language (call input) target) :
    Reference.positiveLiteral? input = some target := by
  obtain ⟨index,candidate,selected,found,bindings,matched,final,holds,outputEqual⟩ :=
    (step_candidates_iff environment "ProjectPositiveLiteral" [input] target).mp stepped
  rw [positive_literal_candidates] at candidate
  have represented : ∃ kind : Fin 2, index = 24 + kind.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at candidate
    rcases candidate with rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  obtain ⟨kind,rfl⟩ := represented
  rw [rule_at] at found
  cases Option.some.inj found
  obtain ⟨arguments,inputEqual,length⟩ := source_constructor_of_match "ProjectPositiveLiteral" (sourceHead kind)
    [.fvar (key kind)] (by simpa only [rule_left,call,source] using matched)
  obtain ⟨childInput,rfl⟩ := List.length_eq_one_iff.mp length
  subst input
  change bindings ∈ matchPattern (rule kind).left (call (source kind childInput)) at matched
  have initialEqual : bindings = initial kind childInput := by
    simpa only [match_call,List.mem_singleton] using matched
  subst bindings
  rw [rule_premises,ReferenceStep.premises_cons_iff] at holds
  obtain ⟨middle,child,remaining⟩ := holds
  have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
  subst final
  rw [premise,ReferenceStep.congruence_iff] at child
  obtain ⟨result,extension,childStep,resultMatched,merged⟩ := child
  change ReferenceStep.Step environment language
    (applyBindingsScoped _ (initial kind childInput) 0 (childSource kind)) result at childStep
  rw [child_instantiated,child_exact] at childStep
  simp only [matchPattern,List.mem_singleton] at resultMatched
  subst extension
  rw [merge_result] at merged
  cases Option.some.inj merged
  rw [result_instantiated] at outputEqual
  rw [← outputEqual]
  change Reference.positiveLiteral? (source kind childInput) = _
  rw [meaning,childStep]
  rfl

theorem step_of_reference (environment : Engine.RelationEnv) (input target : Pattern)
    (projected : Reference.positiveLiteral? input = some target) :
    ReferenceStep.Step environment language (call input) target := by
  unfold Reference.positiveLiteral? at projected
  split at projected
  · rename_i childInput
    exact step environment 0 childInput target projected
  · rename_i childInput
    obtain ⟨result,child,rfl⟩ := Option.map_eq_some_iff.mp projected
    exact step environment 1 childInput result child
  · cases projected

theorem reference_exact (environment : Engine.RelationEnv) (input target : Pattern) :
    ReferenceStep.Step environment language (call input) target ↔ Reference.positiveLiteral? input = some target :=
  ⟨reference_of_step environment input target,step_of_reference environment input target⟩

#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.PositiveLiterals
