import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionItemDeclarations
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionItemStatements
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionItemDirectives

/-! Exhaustive statement compilation over the five authored item rules.
Every source item is read against an explicit, ordered program suffix. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Items

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Reference (program)

def call (input : Pattern) (tail : List Pattern) : Pattern := .apply "ProjectItemInto" [input,program tail]

theorem reference_of_step (environment : Engine.RelationEnv) (input target : Pattern) (tail : List Pattern)
    (stepped : ReferenceStep.Step environment language (call input tail) target) :
    (Reference.itemInto? input tail).map program = some target := by
  obtain ⟨index,candidate,selected,found,bindings,matched,final,holds,output⟩ :=
    (step_candidates_iff environment "ProjectItemInto" [input,program tail] target).mp stepped
  rw [item_candidates] at candidate
  simp only [List.mem_cons,List.not_mem_nil,or_false] at candidate
  rcases candidate with rfl | rfl | rfl | rfl | rfl
  · rw [ItemDeclarations.rule_at] at found
    cases Option.some.inj found
    exact ItemDeclarations.readback environment input target tail bindings final matched holds output
  · have atRule : language.rewrites[6]? = some (ItemStatements.rule 0) := ItemStatements.rule_at 0
    rw [atRule] at found
    cases Option.some.inj found
    exact ItemStatements.readback environment 0 input target tail bindings final matched holds output
  · have atRule : language.rewrites[7]? = some (ItemStatements.rule 1) := ItemStatements.rule_at 1
    rw [atRule] at found
    cases Option.some.inj found
    exact ItemStatements.readback environment 1 input target tail bindings final matched holds output
  · have atRule : language.rewrites[8]? = some (ItemDirectives.rule 0) := ItemDirectives.rule_at 0
    rw [atRule] at found
    cases Option.some.inj found
    exact ItemDirectives.readback environment 0 input target tail bindings final matched holds output
  · have atRule : language.rewrites[9]? = some (ItemDirectives.rule 1) := ItemDirectives.rule_at 1
    rw [atRule] at found
    cases Option.some.inj found
    exact ItemDirectives.readback environment 1 input target tail bindings final matched holds output

theorem step_of_reference (environment : Engine.RelationEnv) (input : Pattern) (tail result : List Pattern)
    (projected : Reference.itemInto? input tail = some result) :
    ReferenceStep.Step environment language (call input tail) (program result) := by
  unfold Reference.itemInto? at projected
  split at projected
  · rename_i space relations before start attributes
    cases fieldsProjected : Reference.attributes? attributes with
    | none => simp [fieldsProjected,Option.bind_eq_bind] at projected
    | some fields =>
      simp only [fieldsProjected,Option.bind_eq_bind,Option.bind_some] at projected
      exact ItemDeclarations.step environment space relations before start attributes tail fields result
        fieldsProjected projected
  · rename_i source
    obtain ⟨value,child,rfl⟩ := Option.map_eq_some_iff.mp projected
    exact ItemStatements.step environment 0 source value tail child
  · rename_i source
    obtain ⟨value,child,rfl⟩ := Option.map_eq_some_iff.mp projected
    exact ItemStatements.step environment 1 source value tail child
  · rename_i space relation
    cases Option.some.inj projected
    exact ItemDirectives.step environment 0 space relation tail
  · rename_i space relation
    cases Option.some.inj projected
    exact ItemDirectives.step environment 1 space relation tail
  · cases projected

theorem reference_exact (environment : Engine.RelationEnv) (input target : Pattern) (tail : List Pattern) :
    ReferenceStep.Step environment language (call input tail) target ↔
      (Reference.itemInto? input tail).map program = some target := by
  constructor
  · exact reference_of_step environment input target tail
  · intro projected
    obtain ⟨result,child,rfl⟩ := Option.map_eq_some_iff.mp projected
    exact step_of_reference environment input tail result child

#print axioms reference_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Items
