import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.StableSource
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls

open Mettapedia.OSLF.Framework

/-!
# Independent controls for the strengthened profile center

Stable profiles constrain the actual input and output slots used by the
formation rules. A variable equation separates mere shared-context formation
from preservation of formation in every context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler
open Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls

theorem stable_equal_profiles_admitted :
    checkStableLanguage? theory (allStar theory) = some true := by
  decide +kernel

theorem stable_original_equation_couples_output_slots :
    checkStableLanguage? theory (separatedOutput theory) = some false := by
  decide +kernel

theorem proper_nonempty_stable_profile_center :
    (stableLanguageCenter theory).Nonempty ∧ stableLanguageCenter theory ≠ Finset.univ := by
  have first : allStar theory ∈ stableLanguageCenter theory := by
    simp only [stableLanguageCenter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact stable_equal_profiles_admitted
  have second : separatedOutput theory ∉ stableLanguageCenter theory := by
    simp only [stableLanguageCenter, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [stable_original_equation_couples_output_slots]
    decide
  refine ⟨⟨allStar theory, first⟩, ?_⟩
  intro full
  apply second
  rw [full]
  exact Finset.mem_univ _

theorem stable_original_commutativity_rejects_unequal_inputs :
    checkStableLanguage? binaryTheory unequalInputs = some false := by
  decide +kernel

theorem stable_original_commutativity_accepts_equal_inputs :
    checkStableLanguage? binaryTheory (allStar binaryTheory) = some true := by
  decide +kernel

theorem stable_directed_law_is_separate :
    stableLanguageCenter directedTheory = Finset.univ ∧
      checkStableDirected? directedTheory (separatedOutput directedTheory) = some false := by
  exact ⟨no_authored_equations_stable_whole_cube directedTheory rfl, by decide +kernel⟩

theorem stable_conditional_equation_not_discarded :
    checkStableLanguage? conditionalTheory (allStar conditionalTheory) = none := by
  decide +kernel

def variableTheory : LanguageDef where
  name := "IncompatibleVariableSorts"
  types := ["Term"]
  terms := []
  equations := [{ name := "all-terms-equal", typeContext := [("x", .base "Term"), ("y", .base "Term")], premises := [], left := .fvar "x", right := .fvar "y" }]
  rewrites := []

theorem variable_equation_context_is_coherent :
    checkLanguage? variableTheory (allStar variableTheory) = some true := by
  decide +kernel

/-- All profiles are rejected. The displayed equation has a coherent context,
but an arbitrary valuation can give its two variables different sorts. -/
theorem variable_equation_stable_center_empty : stableLanguageCenter variableTheory = ∅ := by
  ext profile
  simp only [stableLanguageCenter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false]
  intro accepted
  obtain ⟨_, stable⟩ := (original_stable_equation_check_exact variableTheory profile).mp accepted
  have original := stable (variableTheory.equations[0]'(by decide)) 0 (by simp [variableTheory])
  have encoded : encodeLaw variableTheory
      (equationLaw (variableTheory.equations[0]'(by decide)) 0) = some (.var 0, .var 1) := by
    rfl
  exact variable_equation_never_stable profile
    ((encoded_source_stable_iff _ _ _ encoded profile).mp original)

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls
