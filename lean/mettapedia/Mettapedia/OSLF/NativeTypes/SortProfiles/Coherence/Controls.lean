import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Source
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.GraphLaws
import Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTablesControls

open Mettapedia.OSLF.Framework

/-!
# Actual authored controls for typed profile coherence

The original unary F/G equation couples its actual result slots. A binary
commutativity equation couples its actual argument slots. The corresponding
directed F/G system keeps the equation-only raw cube and exposes its separate
directed-law formation failure. Unsupported premises remain unknown.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler
open Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls

def allStar (language : LanguageDef) : Profile (signature language) := fun _ => .star

def separatedOutput (language : LanguageDef) : Profile (signature language) :=
  fun slot => if slot.1.val = Key.constructor "G" 1 && slot.2.val = 1 then .box else .star

theorem equal_profiles_admitted : checkLanguage? theory (allStar theory) = some true := by
  decide +kernel

theorem original_equation_couples_output_slots :
    checkLanguage? theory (separatedOutput theory) = some false := by
  decide +kernel

theorem proper_nonempty_profile_center :
    (languageCenter theory).Nonempty ∧ languageCenter theory ≠ Finset.univ := by
  have first : allStar theory ∈ languageCenter theory := by
    simp only [languageCenter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact equal_profiles_admitted
  have second : separatedOutput theory ∉ languageCenter theory := by
    simp only [languageCenter, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [original_equation_couples_output_slots]
    decide
  refine ⟨⟨allStar theory, first⟩, ?_⟩
  intro full
  apply second
  rw [full]
  exact Finset.mem_univ _

def binaryTheory : LanguageDef where
  name := "TypedCommutativeProfile"
  types := ["Proc"]
  terms := [{ label := "Parallel", category := "Proc", params := [.simple "first" (.base "Proc"), .simple "second" (.base "Proc")], syntaxPattern := [] }]
  equations := [{ name := "parallel-commutative", typeContext := [("P", .base "Proc"), ("Q", .base "Proc")], premises := [], left := .apply "Parallel" [.fvar "P", .fvar "Q"], right := .apply "Parallel" [.fvar "Q", .fvar "P"] }]
  rewrites := []

def unequalInputs : Profile (signature binaryTheory) :=
  fun slot => if slot.2.val = 1 then .box else .star

theorem original_commutativity_rejects_unequal_inputs :
    checkLanguage? binaryTheory unequalInputs = some false := by
  decide +kernel

theorem original_commutativity_accepts_equal_inputs :
    checkLanguage? binaryTheory (allStar binaryTheory) = some true := by
  decide +kernel

/-- An equation-free directed theory has its full equation center, while its
explicitly separate directed formation check can fail. -/
theorem directed_law_is_separate :
    languageCenter directedTheory = Finset.univ ∧
      checkDirected? directedTheory (separatedOutput directedTheory) = some false := by
  exact ⟨no_authored_equations_whole_cube directedTheory rfl, by decide +kernel⟩

theorem conditional_equation_not_discarded :
    checkLanguage? conditionalTheory (allStar conditionalTheory) = none := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls
