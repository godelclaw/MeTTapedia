import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.CompilerSemantics
import Mettapedia.OSLF.NativeTypes.SortProfiles.Slots

open Mettapedia.OSLF.Framework

/-!
# Complete operation tables and the generated local profile cube

The two coordinates retain their distinct meanings: local profiles classify
the generated input/output slots, while complete operation tables supply the
algebra needed to test the authored equations. The center is computed by the
source compiler and has exactly its independently proved source meaning.

The constant-output reading of the display is a separate construction. It
cannot represent every operation table, even when the source has no equations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler

abbrev CubeVertex (language : LanguageDef) :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Slots.GlobalVertex language × Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)

def center (language : LanguageDef) : Finset (CubeVertex language) :=
  Finset.univ.filter fun vertex => (equations language).check? vertex.2 = some true

theorem mem_center_iff (language : LanguageDef) (vertex : CubeVertex language) :
    vertex ∈ center language ↔
      (equations language).diagnostics = [] ∧
        ∀ law ∈ equationLaws language, SourceLawHolds language law vertex.2 := by
  simp only [center, Finset.mem_filter, Finset.mem_univ, true_and]
  exact compiled_check_exact_source language (equationLaws language) vertex.2

theorem mem_center_stable_iff (language : LanguageDef) (vertex : CubeVertex language) :
    vertex ∈ center language ↔ (equations language).diagnostics = [] ∧
      Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Stable (equations language).system vertex.2 := by
  simp only [center, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Compilation.check?_true_iff _ _

theorem no_equations_complete (language : LanguageDef) (empty : language.equations = []) :
    (equations language).diagnostics = [] ∧ (equations language).system.equations = [] := by
  simp [equations, compileLaws, equationLaws, empty]

/-- Remark 19.5 at the equation-only source meaning: directed reduction is
not silently promoted to an equation. -/
theorem no_equations_whole_cube (language : LanguageDef) (empty : language.equations = []) :
    center language = Finset.univ := by
  obtain ⟨diagnostics, system⟩ := no_equations_complete language empty
  simp [center, Compilation.check?, diagnostics, Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.check, system]

theorem local_profile_independent (language : LanguageDef)
    (first second : Mettapedia.OSLF.NativeTypes.SortProfiles.Slots.GlobalVertex language)
    (table : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)) :
    (first, table) ∈ center language ↔ (second, table) ∈ center language := by
  simp only [center, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A variable permutation preserves the exact solution set of the compiled
system, with local generated profiles retained separately. -/
def renamedCenter (language : LanguageDef) (permutation : Nat ≃ Nat) :
    Finset (CubeVertex language) :=
  Finset.univ.filter fun vertex => (equations language).diagnostics = [] ∧
    vertex.2 ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.center
      (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.rename permutation (equations language).system)

theorem center_rename (language : LanguageDef) (permutation : Nat ≃ Nat) :
    renamedCenter language permutation = center language := by
  ext vertex
  simp only [renamedCenter, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.center_rename, Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.mem_center_iff]
  exact (mem_center_stable_iff language vertex).symm

/-- Literal one-input/output profile slots for each actual operation head. -/
abbrev LiteralSlot (language : LanguageDef) :=
  Σ operation : (signature language).Operation, Fin ((signature language).arity operation + 1)

abbrev LiteralVertex (language : LanguageDef) := LiteralSlot language → HSort

def constantTable (language : LanguageDef) (profile : LiteralVertex language) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language) :=
  fun entry => profile ⟨entry.1, ⟨(signature language).arity entry.1, Nat.lt_succ_self _⟩⟩

theorem constantTable_input_independent (language : LanguageDef) (profile : LiteralVertex language)
    (operation : (signature language).Operation)
    (first second : Fin ((signature language).arity operation) → HSort) :
    constantTable language profile ⟨operation, first⟩ =
      constantTable language profile ⟨operation, second⟩ := rfl

def literalCenter (language : LanguageDef) : Finset (LiteralVertex language) :=
  Finset.univ.filter fun profile =>
    (equations language).check? (constantTable language profile) = some true

theorem literal_center_source_iff (language : LanguageDef) (profile : LiteralVertex language) :
    profile ∈ literalCenter language ↔ (equations language).diagnostics = [] ∧
      ∀ law ∈ equationLaws language, SourceLawHolds language law (constantTable language profile) := by
  simp only [literalCenter, Finset.mem_filter, Finset.mem_univ, true_and]
  exact compiled_check_exact_source language (equationLaws language) _

def firstInputTable (language : LanguageDef) : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language) :=
  fun entry => if positive : 0 < (signature language).arity entry.1 then
    entry.2 ⟨0, positive⟩ else .star

/-- The constant-output display cannot encode all lawful operation tables.
The counterexample depends on an actual non-nullary authored operation. -/
theorem firstInputTable_not_constant (language : LanguageDef)
    (operation : (signature language).Operation)
    (positive : 0 < (signature language).arity operation) :
    ¬ ∃ profile, constantTable language profile = firstInputTable language := by
  rintro ⟨profile, same⟩
  have first := congrFun same ⟨operation, fun _ => HSort.star⟩
  have second := congrFun same ⟨operation, fun _ => HSort.box⟩
  have different : HSort.star = HSort.box := by
    exact ((by simpa [firstInputTable, positive] using first) :
      constantTable language profile ⟨operation, fun _ => HSort.star⟩ = HSort.star).symm.trans
      ((constantTable_input_independent language profile operation _ _).trans
        (by simpa [firstInputTable, positive] using second))
  cases different

end Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables
