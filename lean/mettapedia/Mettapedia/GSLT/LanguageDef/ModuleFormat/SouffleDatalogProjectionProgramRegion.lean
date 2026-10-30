import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionNative

/-! The whole-program compiler has a closed source-rule region: its initial
request and completed program values. Rule-selection agreement therefore
extends to every finite raw reference prefix in that region. This is not a
claim about arbitrary helper requests or normalized native class receipts. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ProgramRegion

open Mettapedia.OSLF.MeTTaIL Syntax Match

private def headChecked (rule : RewriteRule) : Bool :=
  match rule.left with
  | .apply head _ => decide (head ∈ NativeSlice.heads)
  | _ => false

private theorem heads_checked : NativeSlice.language.rewrites.all headChecked = true := by decide +kernel

private theorem calls_of_match {index : Nat} {rule : RewriteRule} {source : Pattern} {bindings : Bindings}
    (found : NativeSlice.language.rewrites[index]? = some rule)
    (matched : bindings ∈ matchPattern rule.left source) : NativeSlice.Calls source := by
  have checked := List.all_eq_true.mp heads_checked rule (List.mem_of_getElem? found)
  cases left : rule.left with
  | apply head arguments =>
    have inside : head ∈ NativeSlice.heads := of_decide_eq_true (by simpa only [headChecked,left] using checked)
    have related := MatchSpec.matchPattern_sound (by simpa only [left] using matched)
    cases related with
    | apply _ _ => exact ⟨head,_,rfl,inside⟩
  | _ => simp [headChecked,left] at checked

theorem native_source (environment : Engine.RelationEnv) {source target : Pattern}
    (stepped : ReferenceStep.Step environment NativeSlice.language source target) :
    ReferenceStep.Step environment language source target := by
  obtain ⟨index,rule,found,bindings,matched,rest⟩ :=
    (ReferenceStep.step_rule_iff environment NativeSlice.language source target).mp stepped
  exact (NativeSlice.reference_exact environment (calls_of_match found matched)).mp stepped

theorem source_target_shape (environment : Engine.RelationEnv) {input target : Pattern}
    (stepped : ReferenceStep.Step environment language (Program.call input) target) :
    ∃ statements, target = Reference.program statements := by
  have projected := (Program.reference_exact environment input target).mp stepped
  unfold Reference.projectProgram? at projected
  split at projected
  · obtain ⟨statements,_,equal⟩ := Option.map_eq_some_iff.mp projected
    exact ⟨statements,equal.symm⟩
  · cases projected

theorem source_result_terminal (environment : Engine.RelationEnv) (statements : List Pattern) (target : Pattern) :
    ¬ReferenceStep.Step environment language (Reference.program statements) target := by
  intro stepped
  obtain ⟨index,missing,rest⟩ := (step_candidates_iff environment "Program" [Reference.vector statements] target).mp stepped
  have absent : candidates "Program" = [] := by decide +kernel
  rw [absent] at missing
  cases missing

theorem native_result_terminal (environment : Engine.RelationEnv) (statements : List Pattern) (target : Pattern) :
    ¬ReferenceStep.Step environment NativeSlice.language (Reference.program statements) target := by
  intro stepped
  exact source_result_terminal environment statements target (native_source environment stepped)

def Region (input state : Pattern) : Prop :=
  state = Program.call input ∨ ∃ statements, state = Reference.program statements

theorem source_closed (environment : Engine.RelationEnv) {input source target : Pattern}
    (inside : Region input source) (stepped : ReferenceStep.Step environment language source target) :
    Region input target := by
  rcases inside with rfl | ⟨statements,rfl⟩
  · exact Or.inr (source_target_shape environment stepped)
  · exact False.elim (source_result_terminal environment statements target stepped)

theorem native_closed (environment : Engine.RelationEnv) {input source target : Pattern}
    (inside : Region input source) (stepped : ReferenceStep.Step environment NativeSlice.language source target) :
    Region input target := source_closed environment inside (native_source environment stepped)

theorem steps_exact (environment : Engine.RelationEnv) {input source target : Pattern}
    (inside : Region input source) :
    ReferenceStep.Step environment NativeSlice.language source target ↔ ReferenceStep.Step environment language source target := by
  rcases inside with rfl | ⟨statements,rfl⟩
  · exact NativeSlice.reference_exact environment ⟨"ProjectProgram",[input],rfl,by decide +kernel⟩
  · exact ⟨fun step => False.elim (native_result_terminal environment statements target step),
      fun step => False.elim (source_result_terminal environment statements target step)⟩

theorem source_path_region (environment : Engine.RelationEnv) {input target : Pattern}
    (path : Relation.ReflTransGen (ReferenceStep.Step environment language) (Program.call input) target) :
    Region input target := by
  induction path with
  | refl => exact Or.inl rfl
  | tail path last ih => exact source_closed environment ih last

theorem native_path_to_source (environment : Engine.RelationEnv) {source target : Pattern}
    (path : Relation.ReflTransGen (ReferenceStep.Step environment NativeSlice.language) source target) :
    Relation.ReflTransGen (ReferenceStep.Step environment language) source target := by
  induction path with
  | refl => exact .refl
  | tail path last ih => exact .tail ih (native_source environment last)

theorem source_path_to_native (environment : Engine.RelationEnv) {input target : Pattern}
    (path : Relation.ReflTransGen (ReferenceStep.Step environment language) (Program.call input) target) :
    Relation.ReflTransGen (ReferenceStep.Step environment NativeSlice.language) (Program.call input) target := by
  induction path with
  | refl => exact .refl
  | tail path last ih => exact .tail ih ((steps_exact environment (source_path_region environment path)).mpr last)

theorem finite_prefixes_exact (environment : Engine.RelationEnv) (input target : Pattern) :
    Relation.ReflTransGen (ReferenceStep.Step environment NativeSlice.language) (Program.call input) target ↔
      Relation.ReflTransGen (ReferenceStep.Step environment language) (Program.call input) target :=
  ⟨native_path_to_source environment,source_path_to_native environment⟩

#print axioms source_closed
#print axioms finite_prefixes_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.ProgramRegion
