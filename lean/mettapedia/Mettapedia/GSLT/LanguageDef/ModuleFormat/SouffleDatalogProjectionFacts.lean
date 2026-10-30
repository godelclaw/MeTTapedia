import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionGroundAtoms

/-! The source fact wrapper erases only its trailing layout and uses the
actual authored ground-atom child step. Finite tuples and literal subtrees
remain governed by the recursively proved ground-atom compiler. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Facts

open Mettapedia.OSLF.MeTTaIL Syntax Match

def rule : RewriteRule := language.rewrites[20]'(by rw [authored_rule_count]; decide)
def call (source : Pattern) : Pattern := .apply "ProjectFact" [source]
def source (atom gap : Pattern) : Pattern := .apply "dl-src:fact" [atom,gap]
def initial (atom gap : Pattern) : Bindings := [("gap",gap),("source",atom)]
def extended (atom gap result : Pattern) : Bindings := ("result",result) :: initial atom gap
def childSource : Pattern := .apply "ProjectGroundAtom" [.fvar "source"]
def premise : Premise := .congruence childSource (.fvar "result")

theorem rule_at : language.rewrites[20]? = some rule := by simp [rule]
theorem rule_left : rule.left = .apply "ProjectFact" [.apply "dl-src:fact"
    [.fvar "source",.fvar "gap"]] := by decide +kernel
theorem rule_right : rule.right = .fvar "result" := by decide +kernel
theorem rule_premises : rule.premises = [premise] := by decide +kernel

theorem match_source (atom gap : Pattern) :
    matchPattern rule.left (call (source atom gap)) = [initial atom gap] := by
  rw [rule_left]
  simp [call,source,initial,matchPattern,matchArgs,mergeBindings]

theorem child_instantiated (sites atom gap : Pattern) :
    applyBindingsScoped sites (initial atom gap) 0 childSource = GroundAtoms.call atom := by
  simp [childSource,initial,GroundAtoms.call,applyBindingsScoped_apply,applyBindingsScoped_fvar_zero,applyBindings]

theorem result_instantiated (sites atom gap result : Pattern) :
    applyBindingsScoped sites (extended atom gap result) 0 rule.right = result := by
  rw [rule_right]
  simp [extended,initial,applyBindingsScoped_fvar_zero,applyBindings]

theorem step (environment : Engine.RelationEnv) (atom gap result : Pattern)
    (projected : Reference.groundAtom? atom = some result) :
    ReferenceStep.Step environment language (call (source atom gap)) result := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨20,rule,rule_at,initial atom gap,?_,extended atom gap result,?_,result_instantiated _ _ _ _⟩
  · rw [match_source]
    exact List.mem_singleton_self _
  · rw [rule_premises,ReferenceStep.premises_cons_iff]
    refine ⟨extended atom gap result,?_,⟨[],.nil _⟩⟩
    rw [premise,ReferenceStep.congruence_iff]
    refine ⟨result,[("result",result)],?_,by simp [matchPattern],?_⟩
    · change ReferenceStep.Step environment language (applyBindingsScoped _ (initial atom gap) 0 childSource) result
      rw [child_instantiated,GroundAtoms.reference_exact]
      exact projected
    · simp [initial,extended,mergeBindings]

theorem reference_of_step (environment : Engine.RelationEnv) (input target : Pattern)
    (stepped : ReferenceStep.Step environment language (call input) target) :
    Reference.fact? input = some target := by
  obtain ⟨index,candidate,selected,found,bindings,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectFact" [input] target).mp stepped
  rw [fact_candidates] at candidate
  have same : index = 20 := List.mem_singleton.mp candidate
  subst index
  rw [rule_at] at found
  cases Option.some.inj found
  obtain ⟨arguments,inputEqual,length⟩ := source_constructor_of_match "ProjectFact" "dl-src:fact"
    [.fvar "source",.fvar "gap"] (by simpa only [rule_left] using matched)
  obtain ⟨atom,gap,rfl⟩ := List.length_eq_two.mp length
  subst input
  change bindings ∈ matchPattern rule.left (call (source atom gap)) at matched
  have initialEqual : bindings = initial atom gap := by simpa only [match_source,List.mem_singleton] using matched
  subst bindings
  rw [rule_premises,ReferenceStep.premises_cons_iff] at holds
  obtain ⟨middle,child,remaining⟩ := holds
  have finalEqual := (ReferenceStep.premises_nil_iff environment language _ _ _).mp remaining
  subst final
  rw [premise,ReferenceStep.congruence_iff] at child
  obtain ⟨result,extension,childStep,resultMatched,merged⟩ := child
  change ReferenceStep.Step environment language (applyBindingsScoped _ (initial atom gap) 0 childSource) result at childStep
  rw [child_instantiated,GroundAtoms.reference_exact] at childStep
  simp only [matchPattern,List.mem_singleton] at resultMatched
  subst extension
  simp [initial,mergeBindings] at merged
  cases merged
  change applyBindingsScoped _ (extended atom gap result) 0 rule.right = target at output
  rw [result_instantiated] at output
  rw [← output]
  exact childStep

theorem reference_exact (environment : Engine.RelationEnv) (input target : Pattern) :
    ReferenceStep.Step environment language (call input) target ↔ Reference.fact? input = some target := by
  constructor
  · exact reference_of_step environment input target
  · intro projected
    unfold Reference.fact? at projected
    split at projected
    · exact step environment _ _ target projected
    · cases projected

#print axioms step
#print axioms reference_of_step
#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Facts
