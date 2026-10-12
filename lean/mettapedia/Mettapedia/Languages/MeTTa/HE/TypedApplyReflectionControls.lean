import Mettapedia.Languages.MeTTa.HE.TypedApplyReflection
import Mettapedia.Languages.MeTTa.HE.TypedApplyStreamingControls

/-!
# Represented typed argument states: admission and retention controls

Structural admission is distinct from evidence that a saved state belongs to
a particular execution. These controls reject malformed frame structure and
show that omitted bindings, equalities or pending occurrences change the
representation or its resumed observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypedApplyReflection.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedApplyStreaming (Configuration machine)
open TypedApplyStreaming.Controls
open TypedApplyEncoding

theorem shared_initial_admitted : WellFormed (.initial shared) := by decide

theorem saved_residual_admitted : WellFormed saved := by decide

theorem source_budget_retains_admission (budget : Nat) (returned : Configuration)
    (readback : TypedApplyStreaming.readback
      ((machine services).run budget (.initial shared)).2 = some returned) :
    WellFormed returned :=
  run_preserves_wellFormed services budget (.initial shared) returned
    shared_initial_admitted readback

def requested : Configuration :=
  ⟨[.argConsumer [(a, environmentA), (b, environmentB)] boundPick valueType shared], []⟩

theorem initial_data_requests_one_choice :
    stepData services (configurationData (.initial shared)) =
      some (actionData (.silent requested)) := by decide

theorem request_matches_independent_rules :
    ObservedStep services (.initial shared) (.silent requested) :=
  (stepData_iff services (.initial shared) (.silent requested)).mp
    initial_data_requests_one_choice |>.2

def selectedSibling : Configuration :=
  ⟨[.apply (shared.advance b environmentB), .argConsumer [] boundPick valueType shared],
    [firstResult]⟩

theorem data_step_retains_selected_binding_and_sibling :
    stepData services (configurationData saved) =
      some (actionData (.silent selectedSibling)) := by decide

def readyToPublish : Configuration :=
  ⟨[.apply (shared.advance a environmentA |>.advance a environmentA),
      .argConsumer [(b, environmentB)] boundPick valueType shared], []⟩

theorem data_step_publishes_only_new_occurrence :
    stepData services (configurationData readyToPublish) =
      some (actionData (.publish [firstResult] saved)) := by decide

theorem published_transition_has_independent_witness :
    ObservedStep services readyToPublish (.publish [firstResult] saved) :=
  (stepData_iff services readyToPublish (.publish [firstResult] saved)).mp
    data_step_publishes_only_new_occurrence |>.2

theorem completed_history_is_retained_without_publication :
    stepData services (configurationData (⟨[], [firstResult, secondResult]⟩ : Configuration)) =
      some (actionData (.finish ⟨[], [firstResult, secondResult]⟩)) := by decide

theorem malformed_configuration_rejected :
    stepData services (.expression [.symbol "he-typed-configuration-v1",
      .expression [], .symbol "omitted-history"]) = none := by decide

theorem renamed_configuration_tag_rejected :
    stepData services (.expression [.symbol "he-typed-configuration",
      .expression [], .expression []]) = none := by decide

theorem negative_position_rejected :
    readState (.expression [.symbol "he-typed-state-v1", .symbol "f",
      .expression [pick], .expression [valueType], .grounded (.int (-1)),
      .expression [], bindingsData Bindings.empty]) = none := by decide

theorem variable_binding_name_rejected :
    readBindings (.expression [.symbol "he-typed-bindings-v1",
      .expression [.expression [.var "selected", a]], .expression []]) = none := by decide

def missingPrefix : Configuration :=
  ⟨[.apply { shared with idx := 1 }], []⟩

theorem decodable_structure_can_still_be_invalid :
    readConfiguration (configurationData missingPrefix) = some missingPrefix :=
  readConfiguration_configurationData missingPrefix

theorem missing_selected_prefix_rejected :
    stepData services (configurationData missingPrefix) = none := by decide

def missingDomain : Configuration :=
  ⟨[.apply { shared with argTypes := [valueType] }], []⟩

theorem incomplete_domain_list_rejected :
    stepData services (configurationData missingDomain) = none := by decide

def pastEnd : Configuration :=
  ⟨[.argConsumer [(a, Bindings.empty)] pick valueType
      (.initial (.symbol "f") [] [] Bindings.empty)], []⟩

theorem completed_position_cannot_consume_an_argument :
    stepData services (configurationData pastEnd) = none := by decide

def selectedWithEquality : Configuration :=
  ⟨[.apply (shared.advance a ⟨environmentA.assignments, [("selected", "alias")]⟩)], []⟩

theorem equalities_are_reconstructed :
    readConfiguration (configurationData selectedWithEquality) = some selectedWithEquality :=
  readConfiguration_configurationData selectedWithEquality

theorem erasing_equalities_changes_the_representation :
    configurationData selectedWithEquality ≠
      configurationData (⟨[.apply (shared.advance a environmentA)], []⟩ : Configuration) := by
  decide

theorem duplicate_history_is_reconstructed :
    readConfiguration (configurationData (⟨[], [firstResult, firstResult]⟩ : Configuration)) =
      some ⟨[], [firstResult, firstResult]⟩ :=
  readConfiguration_configurationData _

theorem deduplicating_history_changes_the_representation :
    configurationData (⟨[], [firstResult, firstResult]⟩ : Configuration) ≠
      configurationData (⟨[], [firstResult]⟩ : Configuration) := by decide

/-- Frame structure alone cannot authenticate which earlier run supplied it. -/
theorem spliced_bindings_are_structurally_admitted : WellFormed splicedBindings := by decide

theorem structurally_admitted_splice_changes_resumption :
    ((machine services).run 5 splicedBindings).1 ≠
      ((machine services).run 5 saved).1 := spliced_state_is_not_the_residual

theorem omitted_pending_sibling_changes_representation :
    configurationData saved ≠
      configurationData (⟨[], [firstResult]⟩ : Configuration) := by decide

theorem result_tuple_does_not_become_an_error :
    readResults (resultsData [(.symbol "Error", Bindings.empty),
      (.symbol "y", Bindings.empty)]) =
      some [(.symbol "Error", Bindings.empty), (.symbol "y", Bindings.empty)] :=
  readResults_resultsData _

end Mettapedia.Languages.MeTTa.HE.TypedApplyReflection.Controls
