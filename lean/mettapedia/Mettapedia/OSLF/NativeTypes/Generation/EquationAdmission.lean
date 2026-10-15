import Mettapedia.OSLF.NativeTypes.Generation.Core

open Mettapedia.OSLF.Framework

/-!
# Exact admission of the generator's selected source laws

Language selection is applied to the original law indices before the finite
center test. The specification uses independent formation stability of each
selected authored law, including its encoding diagnostics. Directed reduction
preservation is checked separately from equation conversion.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.SortProfiles.Derived (CubeVertex)

theorem generated_equation_admission_exact (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language) :
    (generate snapshot language logic vertex).equationAdmission = some true ↔
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws (selectedSnapshot snapshot language).language
        (selectedEquationLaws (selectedSnapshot snapshot language).language language.operational)).diagnostics = [] ∧
      ∀ law ∈ selectedEquationLaws (selectedSnapshot snapshot language).language language.operational,
        Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.SourceEquationStable (selectedSnapshot snapshot language).language law vertex.2 :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.compiled_stable_check_exact_source _ _ _

theorem generated_rewrite_admission_exact (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language) :
    (generate snapshot language logic vertex).rewriteAdmission = some true ↔
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws (selectedSnapshot snapshot language).language
        (selectedRewriteLaws (selectedSnapshot snapshot language).language language.operational)).diagnostics = [] ∧
      ∀ law ∈ selectedRewriteLaws (selectedSnapshot snapshot language).language language.operational,
        Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.SourceEquationStable (selectedSnapshot snapshot language).language law vertex.2 :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.compiled_stable_check_exact_source _ _ _

theorem no_authored_equations_generate_every_vertex (snapshot : Snapshot)
    (language : LanguageFragment) (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language)
    (empty : snapshot.language.equations = []) :
    (generate snapshot language logic vertex).equationAdmission = some true := by
  simp [generate, selectedEquationLaws, selectedSnapshot, selectedLanguage,
    Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.equationLaws, empty, Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws,
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?, Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStable]

theorem inadmissible_vertex_has_no_formers (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language)
    (rejected : (generate snapshot language logic vertex).equationAdmission = some false) :
    (generate snapshot language logic vertex).modalCatalogue = [] ∧
      (generate snapshot language logic vertex).structuralCatalogue = [] := by
  change Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws (selectedSnapshot snapshot language).language
      (selectedEquationLaws (selectedSnapshot snapshot language).language language.operational)) vertex.2 =
        some false at rejected
  simp only [generate, rejected, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false, and_self]

end Mettapedia.OSLF.NativeTypes.Generation
