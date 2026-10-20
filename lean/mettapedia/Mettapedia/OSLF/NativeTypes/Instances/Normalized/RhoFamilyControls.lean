import Mettapedia.OSLF.MeTTaIL.Complete.RhoQuoteDrop
import Mettapedia.OSLF.Syntax.RhoAuthoredDropProfile

/-!
# Boundaries between authored rho profiles

The name equation `@(*n) = n` is distinct from the process rule
`*(@P) ~> P`. The latter is present in a separately authored extension.
The controls below use that actual language and its independently specified
contextual firing relation. Normalizing its source can erase a genuine Drop
event, even though the equality normalizer itself remains correct.

Global raw normalization also need not reflect an expected sort. Public
admission therefore checks the original term instead of accepting any raw
term whose normal form happens to have the requested sort.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoFamilyControls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Binding.RhoSchema.Authored

abbrev presentation := Complete.RhoQuoteDrop.presentation

def zero : Pattern := .apply "PZero" []

def illSortedPresentation : Pattern :=
  .apply "NQuote" [.apply "PDrop" [zero]]

abbrev closedProc (term : Pattern) : Prop :=
  OpenPatternWellSorted rhoCalc (fun _ => none) [] (.base "Proc") term

theorem illSorted_normal : QuoteDrop.normal presentation illSortedPresentation = zero := by
  decide +kernel

theorem zero_admitted : closedProc zero :=
  checkOpenPatternWellSorted_sound (by decide +kernel)

theorem illSorted_rejected : ¬ closedProc illSortedPresentation := by
  intro admitted
  have checked := checkOpenPatternWellSorted_complete admitted
  have rejected : checkOpenPatternWellSorted rhoCalc (fun _ => none) [] (.base "Proc")
      illSortedPresentation = false := by decide +kernel
  rw [rejected] at checked
  cases checked

theorem raw_sort_reflection_fails :
    ¬ (∀ source, closedProc (QuoteDrop.normal presentation source) → closedProc source) := by
  intro reflects
  apply illSorted_rejected
  apply reflects illSortedPresentation
  rw [illSorted_normal]
  exact zero_admitted

/-- A name supplied by the open free-name context. -/
def channel : Pattern := .fvar "n"

def free : FreeTypeContext := fun name => if name = "n" then some (.base "Name") else none

def eventTarget : Pattern := .apply "PDrop" [channel]

def eventSource : Pattern := .apply "PDrop" [.apply "NQuote" [eventTarget]]

abbrev openProc (term : Pattern) : Prop :=
  OpenPatternWellSorted rhoCalcWithDrop free [] (.base "Proc") term

theorem event_source_admitted : openProc eventSource :=
  checkOpenPatternWellSorted_sound (by decide +kernel)

theorem event_target_admitted : openProc eventTarget :=
  checkOpenPatternWellSorted_sound (by decide +kernel)

theorem event_source_distinct : eventSource ≠ eventTarget := by decide +kernel

theorem event_normal : QuoteDrop.normal presentation eventSource = eventTarget := by
  decide +kernel

theorem event_target_normal : QuoteDrop.normal presentation eventTarget = eventTarget := by
  decide +kernel

/-- The source's separately authored Drop rule executes this event. -/
theorem authored_drop_event :
    Step (engineBasePremises Engine.RelationEnv.empty) rhoCalcWithDrop eventSource eventTarget := by
  apply exists_mem_rewriteAt_iff_step.mp
  exact ⟨1, by decide +kernel⟩

/-- The COMM-only authored profile has no event from the same source. -/
theorem comm_only_event_absent (target : Pattern) :
    ¬ Step (engineBasePremises Engine.RelationEnv.empty) rhoCalc eventSource target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  change rule ∈ [rhoCommRewrite, rhoParCongRewrite] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

/-- At the normal source, neither COMM, ParCong nor Drop can fire. -/
theorem normal_event_absent (target : Pattern) :
    ¬ Step (engineBasePremises Engine.RelationEnv.empty) rhoCalcWithDrop eventTarget target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  change rule ∈ [rhoCommRewrite, rhoParCongRewrite, rhoDropRewrite] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide +kernel

theorem drop_event_endpoints_equal : QuoteDrop.QuoteDropSame presentation eventSource eventTarget := by
  have sound := QuoteDrop.quoteDrop_sound (declaration := presentation) eventSource
  rw [event_normal] at sound
  exact sound

/-- Equality normalization alone cannot justify replacing this authored
event relation by raw firings at normal sources. -/
theorem drop_normalize_firing_impossible :
    ¬ (∀ source target,
      Step (engineBasePremises Engine.RelationEnv.empty) rhoCalcWithDrop source target →
      ∃ next, Step (engineBasePremises Engine.RelationEnv.empty) rhoCalcWithDrop
        (QuoteDrop.normal presentation source) next ∧
        QuoteDrop.QuoteDropSame presentation target next) := by
  intro normalizes
  obtain ⟨next, firing, _⟩ := normalizes eventSource eventTarget authored_drop_event
  rw [event_normal] at firing
  exact normal_event_absent next firing

theorem pure_and_drop_are_distinct :
    Step (engineBasePremises Engine.RelationEnv.empty) rhoCalcWithDrop eventSource eventTarget ∧
      ¬ Step (engineBasePremises Engine.RelationEnv.empty) rhoCalc eventSource eventTarget :=
  ⟨authored_drop_event, comm_only_event_absent eventTarget⟩

end Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoFamilyControls
