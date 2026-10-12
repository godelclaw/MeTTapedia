import Mettapedia.Languages.MeTTa.HE.TypedApplyDataExecution
import Mettapedia.Languages.MeTTa.HE.TypedApplyReflectionControls

/-!
# Data execution and exact resumption controls

These controls execute the decoder and structural admission on each step.
Saved data retains both the selected environment and pending alternatives;
restarting the initial data repeats the prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypedApplyDataExecution.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedApplyEncoding
open TypedApplyStreaming.Controls
open TypedApplyReflection
open TypedApplyReflection.Controls

theorem encoded_pause_after_first_occurrence :
    (dataMachine services).run 4 (configurationData (.initial shared)) =
      ([firstResult], .exhausted (configurationData saved)) := by
  rw [run_representation services 4 (.initial shared) shared_initial_admitted,
    pause_after_first_occurrence]
  rfl

theorem encoded_sibling_is_the_remaining_occurrence :
    ((dataMachine services).run 5 (configurationData saved)).1 = [secondResult] := by
  rw [run_representation services 5 saved saved_residual_admitted]
  exact saved_sibling_is_the_remaining_occurrence

theorem encoded_prefix_and_resumption_agree :
    (dataMachine services).run 9 (configurationData (.initial shared)) =
      ([firstResult] ++ ((dataMachine services).run 5 (configurationData saved)).1,
        ((dataMachine services).run 5 (configurationData saved)).2) :=
  resume_after_prefix services 4 5 (.initial shared) saved [firstResult]
    shared_initial_admitted pause_after_first_occurrence

theorem encoded_history_is_not_emitted_again :
    firstResult ∉ ((dataMachine services).run 5 (configurationData saved)).1 := by
  rw [encoded_sibling_is_the_remaining_occurrence]
  decide

theorem encoded_restart_repeats_the_prefix :
    ((dataMachine services).run 4 (configurationData (.initial shared))).1 ++
        ((dataMachine services).run 5 (configurationData (.initial shared))).1 ≠ results shared := by
  rw [run_representation services 4 (.initial shared) shared_initial_admitted,
    run_representation services 5 (.initial shared) shared_initial_admitted]
  exact restart_repeats_the_prefix

theorem arbitrary_raw_tree_is_retained_in_data_execution (argument : Atom) :
    ((dataMachine services).run 20 (configurationData
      (.initial (.initial (.symbol "f") [argument] [Atom.atomType] Bindings.empty)))).1 =
      [(.expression [.symbol "f", argument], Bindings.empty)] := by
  have valid : WellFormed
      (.initial (.initial (.symbol "f") [argument] [Atom.atomType] Bindings.empty)) := by
    apply initial_wellFormed
    exact TypedApplyState.initial_wellFormed _ _ _ _ rfl
  rw [run_representation services 20 _ valid]
  exact arbitrary_raw_tree_retained argument

theorem malformed_data_is_stuck_and_has_no_answer :
    (dataMachine services).run 5 (.symbol "missing-state") =
      ([], .stuck (.symbol "missing-state")) := rfl

theorem structurally_invalid_data_is_stuck_and_has_no_answer :
    (dataMachine services).run 5 (configurationData missingPrefix) =
      ([], .stuck (configurationData missingPrefix)) := rfl

theorem omitted_encoded_sibling_loses_an_answer :
    ((dataMachine services).run 5
      (configurationData (⟨[], [firstResult]⟩ : TypedApplyConfig))).1 ≠
        ((dataMachine services).run 5 (configurationData saved)).1 := by decide

theorem encoded_binding_splice_changes_the_answer :
    ((dataMachine services).run 5 (configurationData splicedBindings)).1 ≠
      ((dataMachine services).run 5 (configurationData saved)).1 := by decide

end Mettapedia.Languages.MeTTa.HE.TypedApplyDataExecution.Controls
