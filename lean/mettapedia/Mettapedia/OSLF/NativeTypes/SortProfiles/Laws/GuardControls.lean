import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardedSource
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls

open Mettapedia.OSLF.Framework

/-!
# Provider guards change the computed equation center

An admitted nullary query enables the original F/G law. A complete empty
provider disables it. Missing declarations remain unknown. The controls keep
duplicate provider rows and ordered duplicate premise origins.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardedSource

def guardedTheory : LanguageDef :=
  {Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.theory with
    equations := [{Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.equation with
      premises := [.relationQuery "enabled" []]}]}

def active : ProviderSnapshot := ⟨[⟨"enabled", [], []⟩], [⟨"enabled", []⟩]⟩
def inactive : ProviderSnapshot := ⟨[⟨"enabled", [], []⟩], []⟩
def missing : ProviderSnapshot := ⟨[], []⟩

def separated : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature guardedTheory) :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls.separatedOutput guardedTheory

theorem enabled_guard_checks_actual_law : checkLanguage? guardedTheory active separated = some false := by
  decide +kernel

theorem complete_empty_guard_disables_actual_law : checkLanguage? guardedTheory inactive separated = some true := by
  decide +kernel

theorem undeclared_guard_stays_unresolved : checkLanguage? guardedTheory missing separated = none := by
  decide +kernel

theorem provider_changes_the_actual_center :
    separated ∈ center guardedTheory inactive ∧ separated ∉ center guardedTheory active := by
  constructor
  · simp only [center, Finset.mem_filter, Finset.mem_univ, true_and]
    exact complete_empty_guard_disables_actual_law
  · simp only [center, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [enabled_guard_checks_actual_law]
    decide

def duplicateProvider : ProviderSnapshot :=
  ⟨[⟨"enabled", [], []⟩], [⟨"enabled", []⟩, ⟨"enabled", []⟩]⟩

theorem duplicate_premise_and_provider_origins :
    guards? duplicateProvider [.relationQuery "enabled" [], .relationQuery "enabled" []] =
      some [⟨0, "enabled", [0, 1]⟩, ⟨1, "enabled", [0, 1]⟩] := by
  decide +kernel

def environment : Environment where
  language := guardedTheory
  free := fun _ => none
  provider := duplicateProvider
  specifications := []
def rule : RewriteRule :=
  {name := "GuardWitness", typeContext := [], premises := [],
    left := .apply "F" [], right := .apply "G" [], bindings := some ⟨[], []⟩}
def context : Context := ⟨0, rule, ⟨[], []⟩, [], 0, 0⟩

theorem empty_capture_is_independently_typed : TypedAssignment environment context [] := by
  constructor
  · intro name value found
    cases found
  · intro name value found
    cases found

theorem actual_nullary_query_keeps_each_provider_origin (index : Fin 2) :
    QueryHolds environment context "enabled" [] [] index.val [] := by
  apply (nullary_query_exact environment context "enabled" [] empty_capture_is_independently_typed _).mpr
  refine ⟨⟨⟨"enabled", [], []⟩, by decide +kernel⟩, ?_⟩
  have below := index.isLt
  change index.val ∈ [0, 1]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- This is the guarded source law, not an erased unconditional F/G equation. -/
theorem disabled_source_law_is_vacuously_stable :
    SourceAdmitted guardedTheory inactive separated
      (equationLaw (guardedTheory.equations[0]'(by decide +kernel)) 0) := by
  apply (original_equation_check_exact _ _ _).mp complete_empty_guard_disables_actual_law
  exact List.mk_mem_zipIdx_iff_getElem?.mpr rfl

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardControls
