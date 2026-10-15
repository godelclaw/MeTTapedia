import Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables
import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.CompilerOrigins

open Mettapedia.OSLF.Framework

/-!
# A proper authored equational center and a directed-law separator

The same declared unary constructors generate an equation-restricted center
and an equation-free directed system. Their distinction refutes the reading
that every rewrite is already a sort equation while every equation-free
presentation admits its entire cube.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler

def carrier : TypeExpr := .base "Term"

def declaredFormers : List GrammarRule :=
  [ { label := "F", category := "Term", params := [.simple "x" carrier], syntaxPattern := [] },
    { label := "G", category := "Term", params := [.simple "x" carrier], syntaxPattern := [] } ]

def equation : Equation where
  name := "F-equals-G"
  typeContext := [("x", carrier)]
  premises := []
  left := .apply "F" [.fvar "x"]
  right := .apply "G" [.fvar "x"]

def directedRule : RewriteRule where
  name := "F-to-G"
  typeContext := [("x", carrier)]
  premises := []
  left := .apply "F" [.fvar "x"]
  right := .apply "G" [.fvar "x"]

def theory : LanguageDef where
  name := "ProperEquationalCenter"
  types := ["Term"]
  terms := declaredFormers
  equations := [equation]
  rewrites := []

def directedTheory : LanguageDef where
  name := "DirectedIsNotConversion"
  types := ["Term"]
  terms := declaredFormers
  equations := []
  rewrites := [directedRule]

def allStar (language : LanguageDef) : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language) :=
  fun _ => .star

def separatedOutputs (language : LanguageDef) : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language) :=
  fun entry => if entry.1.val = Key.constructor "F" 1 then .star else .box

def acceptedVertex : CubeVertex theory := (fun _ => .star, allStar theory)
def rejectedVertex : CubeVertex theory := (fun _ => .star, separatedOutputs theory)

theorem equation_compile_complete : (equations theory).diagnostics = [] := by decide +kernel

theorem exact_original_equation_is_checked :
    (equations theory).check? (allStar theory) = some true := by decide +kernel

theorem actual_equation_separates_outputs :
    (equations theory).check? (separatedOutputs theory) = some false := by decide +kernel

theorem accepted_in_actual_center : acceptedVertex ∈ center theory := by
  simp only [center, Finset.mem_filter, Finset.mem_univ, true_and]
  exact exact_original_equation_is_checked

theorem rejected_from_actual_center : rejectedVertex ∉ center theory := by
  simp only [center, Finset.mem_filter, Finset.mem_univ, true_and]
  change ¬ (equations theory).check? (separatedOutputs theory) = some true
  rw [actual_equation_separates_outputs]
  decide

/-- The computed center is inhabited and strictly smaller than its raw
computed cube. No cardinality or admission predicate is supplied. -/
theorem proper_nonempty_center : (center theory).Nonempty ∧ center theory ≠ Finset.univ := by
  refine ⟨⟨acceptedVertex, accepted_in_actual_center⟩, ?_⟩
  intro full
  apply rejected_from_actual_center
  rw [full]
  exact Finset.mem_univ _

theorem original_source_law_holds :
    SourceLawHolds theory (equationLaw equation 0) (allStar theory) := by
  apply (equation_source_check_exact theory _).mp exact_original_equation_is_checked |>.2
  exact List.mk_mem_zipIdx_iff_getElem?.mpr rfl

theorem entire_directed_cube_survives : center directedTheory = Finset.univ :=
  no_equations_whole_cube directedTheory rfl

theorem directed_law_compile_complete : (rewrites directedTheory).diagnostics = [] := by decide +kernel

theorem directed_equality_fails :
    (rewrites directedTheory).check? (separatedOutputs directedTheory) = some false := by decide +kernel

theorem no_equations_do_not_force_rewrite_sort_equality :
    ∃ language : LanguageDef, ∃ vertex : CubeVertex language,
      language.equations = [] ∧ vertex ∈ center language ∧
        (rewrites language).check? vertex.2 = some false := by
  refine ⟨directedTheory, (fun _ => .star, separatedOutputs directedTheory), rfl, ?_,
    directed_equality_fails⟩
  rw [entire_directed_cube_survives]
  exact Finset.mem_univ _

theorem corrected_equation_and_directed_contract (language : LanguageDef)
    (vertex : CubeVertex language) :
    (vertex ∈ center language ∧ (rewrites language).check? vertex.2 = some true) ↔
      ((equations language).diagnostics = [] ∧
        ∀ law ∈ equationLaws language, SourceLawHolds language law vertex.2) ∧
      ((rewrites language).diagnostics = [] ∧
        ∀ law ∈ rewriteLaws language, SourceLawHolds language law vertex.2) := by
  rw [mem_center_iff]
  exact and_congr Iff.rfl (compiled_check_exact_source language (rewriteLaws language) vertex.2)

def conditionalTheory : LanguageDef :=
  { theory with equations :=
      [{ equation with premises := [.relationQuery "enabled" [.fvar "x"]] }] }

theorem conditional_equation_stays_unknown :
    (equations conditionalTheory).check? (allStar conditionalTheory) = none := by decide +kernel

theorem conditional_diagnostic_retained :
    Diagnostic.conditionalPremises .equation 0 [.relationQuery "enabled" [.fvar "x"]] ∈
      (equations conditionalTheory).diagnostics := by decide +kernel

/-- The head and arity come from the first actual declared constructor. -/
def originalF : GrammarRule := directedTheory.terms[0]'(by decide +kernel)

def originalFOperation : (signature directedTheory).Operation :=
  ⟨.constructor originalF.label originalF.params.length, by decide +kernel⟩

theorem originalF_is_non_nullary : 0 < (signature directedTheory).arity originalFOperation := by
  decide +kernel

theorem input_projection_respects_the_actual_directed_law :
    (rewrites directedTheory).check? (firstInputTable directedTheory) = some true := by
  decide +kernel

/-- A genuinely input-dependent table belongs to the actual equation-free
center and satisfies the authored directed comparison. Reading just a local
profile's output slot cannot recover it. -/
theorem lawful_source_table_is_not_a_constant_output_profile :
    (fun _ => HSort.star, firstInputTable directedTheory) ∈ center directedTheory ∧
      (rewrites directedTheory).check? (firstInputTable directedTheory) = some true ∧
      ¬ ∃ profile, constantTable directedTheory profile = firstInputTable directedTheory := by
  refine ⟨?_, input_projection_respects_the_actual_directed_law, ?_⟩
  · rw [entire_directed_cube_survives]
    exact Finset.mem_univ _
  · exact firstInputTable_not_constant directedTheory originalFOperation originalF_is_non_nullary

end Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls
