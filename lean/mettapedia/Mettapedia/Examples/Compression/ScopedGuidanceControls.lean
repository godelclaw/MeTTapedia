import Mettapedia.Algorithms.Compression.ScopedChoices
import Mettapedia.Examples.Compression.ScopedTemplateControls

/-! Concrete generated binder patterns, depth boundaries and refused spines. -/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.ScopedGuidanceControls

open Mettapedia.OSLF.Binding
open Mettapedia.Algorithms.Compression

namespace Binder

abbrev rows : List (ScopedTemplateWire.Declaration String) :=
  [⟨"lambda", "T", [(["T"], "T")]⟩, ⟨"zero", "T", []⟩]
abbrev signature := ScopedTemplateWire.signature rows
abbrev parameters : List (MetaArity signature) := [(["T"], "T")]

def binder : signature.Op "T" := ⟨⟨0, by decide⟩, rfl⟩
def sourceArguments : Args signature [(["T"], "T")] [] := .cons (.var .zero) .nil
def source : Term signature [] "T" := .op binder sourceArguments
def bodyPattern : Term (withMetas signature parameters) ["T"] "T" :=
  .op (.inr (.mk ⟨0, by decide⟩)) (.cons (.var .zero) .nil)
def pattern : Term (withMetas signature parameters) [] "T" :=
  .op (.inl binder) (.cons bodyPattern .nil)
def captures : MAcc signature parameters [] := setMeta emptyMAcc ⟨0, by decide⟩ (.var .zero)

theorem body_present : bodyPattern ∈ ScopedChoices.leaves (M := parameters) [] ["T"] "T" := by
  apply ScopedChoices.parameter_present (S := signature) (M := parameters) [] ["T"] ⟨0, by decide⟩
  simp [ScopedChoices.spines, ScopedChoices.positions, parameters]
  rfl

theorem body_match :
    smatchAtT (S := signature) (M := parameters) ["T"] emptyMAcc bodyPattern (Term.var .zero) = some captures := by
  unfold bodyPattern
  rw [smatchAtT.eq_2 (S := signature)]
  have recovered : recoverBoundVariableBody (S := signature) (M := parameters)
      (dependencies := ["T"]) (bs := ["T"]) (Γ := []) (.cons (bs := []) (.var .zero) .nil) (Term.var .zero) =
        some (Term.var .zero) := by
    have returned := recoverBoundVariableBody_prefix (S := signature) (M := parameters)
      (Γ := []) (bs := ["T"]) (Term.var .zero)
    have same : unScope (S := signature) ["T"] (Term.var .zero) = Term.var .zero := rfl
    rw [same] at returned
    exact returned
  rw [recovered]
  rfl

theorem pattern_match : smatchAtT (S := signature) (M := parameters) [] emptyMAcc pattern source = some captures := by
  unfold pattern source binder
  rw [smatchAtT.eq_3 (S := signature), dif_pos rfl]
  change smatchA (S := signature) (M := parameters) emptyMAcc
    (.cons (bs := ["T"]) bodyPattern .nil) sourceArguments = some captures
  rw [sourceArguments, smatchA_cons (S := signature), body_match]
  exact smatchAtA_nil [] captures

theorem generated_contextual_pattern :
    pattern ∈ (ScopedGuidance.terms (ScopedChoices.leaves (M := parameters) []) 1 []
      emptyMAcc source).map Prod.fst := by
  apply List.mem_map.mpr
  refine ⟨(pattern, captures), ?_, rfl⟩
  apply (ScopedGuidance.terms_mem_iff _ 1 [] emptyMAcc captures source pattern).mpr
  refine ⟨?_, pattern_match⟩
  change pattern ∈ ScopedChoices.leaves (M := parameters) [] [] "T" ++ _
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨Args.cons bodyPattern Args.nil, ?_, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨bodyPattern, body_present, ?_⟩
  exact List.mem_map.mpr ⟨Args.nil, List.mem_singleton_self _, rfl⟩

theorem generated_pattern_reconstructs :
    ∃ captures : MAcc signature parameters [],
      (pattern, captures) ∈ ScopedGuidance.terms (ScopedChoices.leaves (M := parameters) []) 1 [] emptyMAcc source ∧
        ScopedTemplates.expandAtT [] captures pattern = some source := by
  obtain ⟨⟨candidate, captures⟩, present, same⟩ := List.mem_map.mp generated_contextual_pattern
  change candidate = pattern at same
  subst candidate
  exact ⟨captures, present, ScopedGuidance.terms_reconstruct _ _ [] _ _ source pattern present⟩

theorem depth_zero_exhausted :
    ScopedGuidance.terms (ScopedChoices.leaves (M := parameters) []) 0 [] emptyMAcc source = [] := by decide

abbrev repeatedParameters : List (MetaArity signature) := [(["T", "T"], "T")]

/-- The finite choices contain the repeated-variable application, but the
shared recognizer refuses it. Only the literal binder pattern survives. -/
theorem repeated_spine_refused :
    (ScopedGuidance.terms (ScopedChoices.leaves (M := repeatedParameters) [])
      1 [] emptyMAcc source).length = 1 := by
  let literal : Term (withMetas signature repeatedParameters) [] "T" :=
    .op (.inl binder) (.cons (.var .zero) .nil)
  let repeated : Term (withMetas signature repeatedParameters) [] "T" :=
    .op (.inl binder) (.cons (.op (.inr (.mk ⟨0, by decide⟩))
      (.cons (.var .zero) (.cons (.var .zero) .nil))) .nil)
  have region : ScopedGuidance.shapes (ScopedChoices.leaves (M := repeatedParameters) []) 1 [] source =
      [literal, repeated] := by
    simp [ScopedGuidance.shapes, ScopedGuidance.shapeArguments, ScopedChoices.leaves,
      ScopedChoices.parameterChoices, ScopedChoices.spines, ScopedChoices.positions,
      List.finRange_succ, source, sourceArguments, binder, rows, repeatedParameters, literal, repeated,
      castTermCtx]
    rfl
  have accepted : smatchAtT (S := signature) (M := repeatedParameters) [] emptyMAcc literal source = some emptyMAcc := by
    dsimp only [literal, source, binder]
    rw [smatchAtT.eq_3 (S := signature), dif_pos rfl]
    change smatchA (S := signature) (M := repeatedParameters) emptyMAcc
      (.cons (bs := ["T"]) (.var .zero) .nil) sourceArguments = some emptyMAcc
    have rigid : smatchAtT (S := signature) (M := repeatedParameters) (Γ := [])
        ["T"] emptyMAcc (.var .zero) (.var .zero) = some emptyMAcc := by
      rw [smatchAtT.eq_1 (S := signature)]
      have split : splitVar (S := signature) (Γ := []) ["T"] (.zero : Var ["T"] "T") = .inl .zero := rfl
      rw [split]
      rfl
    rw [sourceArguments, smatchA_cons (S := signature), rigid]
    exact smatchAtA_nil [] emptyMAcc
  have refused : smatchAtT (S := signature) (M := repeatedParameters) [] emptyMAcc repeated source = none := by
    dsimp only [repeated, source, binder]
    rw [smatchAtT.eq_3 (S := signature), dif_pos rfl]
    change smatchA (S := signature) (M := repeatedParameters) emptyMAcc
      (.cons (bs := ["T"]) (.op (.inr (.mk ⟨0, by decide⟩)) (.cons (bs := []) (.var .zero) (.cons (bs := []) (.var .zero) .nil))) .nil)
      sourceArguments = none
    rw [sourceArguments, smatchA_cons (S := signature), smatchAtT.eq_def (S := signature)]
    rfl
  rw [ScopedGuidance.terms_eq_late (S := signature), region]
  simp only [List.filterMap_cons, accepted, refused, Option.map_some, Option.map_none,
    List.filterMap_nil, List.length_cons, List.length_nil]

end Binder

theorem absent_unused_parameters_do_not_block_generation :
    ScopedTemplateControls.Unused.pattern ∈
      (ScopedGuidance.terms
        (ScopedChoices.leaves (M := ScopedTemplateControls.Unused.parameters) ["absent"])
        1 [] emptyMAcc ScopedTemplateControls.Unused.source).map Prod.fst := by decide

end Mettapedia.Examples.Compression.ScopedGuidanceControls
