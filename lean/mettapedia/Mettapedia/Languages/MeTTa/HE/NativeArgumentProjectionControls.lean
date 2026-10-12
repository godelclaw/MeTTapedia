import Mettapedia.Languages.MeTTa.HE.NativeArgumentProjection
import Mettapedia.Languages.MeTTa.HE.NativeSelectedTypeScan

/-!
# Retained native-argument projection controls

The controls distinguish raw demand from evaluation, retained child selection
from parent traversal, ordered duplicate alternatives from support, merge
failure from emitted failure, and first-success type selection from overload
enumeration. The general correspondence laws live in the imported modules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeArgumentProjectionControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeArgumentProjection
open NativeSelectedTypeScan

private def a : Atom := .symbol "a"
private def b : Atom := .symbol "b"
private def choice : Atom := .symbol "Choice"
private def pick : Atom := .expression [.symbol "pick"]
private def rawError : Atom := .expression [.symbol "Error", .symbol "held"]
private def nested : Atom := .expression [.symbol "let", .var "x", pick,
  .expression [.symbol "quote", .expression [.symbol "Pair", .var "x", .var "x"]]]
private def empty : Bindings := ⟨[], []⟩
private def selectedA : Bindings := ⟨[("x", a)], []⟩
private def selectedB : Bindings := ⟨[("x", b)], []⟩
private def state : TypedApplyState := ⟨.symbol "same", [pick], [choice], 0, [], empty⟩
private def saved : Snapshot := ⟨state, pick, choice,
  [(a, selectedA), (a, selectedA), (b, selectedB)], 0, .iterate, none, none⟩
private def merge : Bindings → Bindings → Option Bindings := fun _ evaluated => some evaluated
private def extend : Bindings → Atom → Atom → Option Bindings := fun environment _ _ => some environment

theorem arbitrary_nested_atom_demand_is_raw :
    rawDemand false false Atom.atomType nested = true := rfl

theorem error_shaped_atom_demand_is_raw :
    rawDemand false false Atom.atomType rawError = true := rfl

theorem unbound_variable_is_raw :
    rawDemand false false choice (.var "x") = true := rfl

theorem substituted_variable_call_is_not_raw :
    rawDemand false false choice pick = false := rfl

theorem normalization_overrides_atom_demand :
    rawDemand true false Atom.atomType nested = false := rfl

theorem normalization_overrides_explicit_data :
    rawDemand true true choice pick = false := rfl

theorem explicit_data_preserves_call_syntax :
    rawDemand false true choice pick = true := rfl

theorem duplicate_outcome_occurrences_are_retained :
    saved.pending = [(a, selectedA), (a, selectedA), (b, selectedB)] := rfl

theorem first_selection_retains_its_child_and_next_duplicate :
    consume merge extend saved = .child (a, selectedA)
      {saved with nextOutcome := 1, phase := .afterChild, activeValue := some a, activeBindings := some selectedA} := rfl

theorem projected_child_uses_selected_value_once :
    actionConfiguration saved [] [] (consume merge extend saved) =
      ⟨[.apply ⟨.symbol "same", [pick], [choice], 1, [a], selectedA⟩,
        .argConsumer [(a, selectedA), (b, selectedB)] pick choice state], []⟩ := rfl

theorem selected_child_blocks_parent_advance :
    step merge extend {saved with nextOutcome := 1, phase := .afterChild, activeValue := some a, activeBindings := some selectedA} = none := rfl

theorem borrowed_selection_blocks_even_iterate_phase :
    step merge extend {saved with activeValue := some a, activeBindings := some selectedA} = none := rfl

theorem returned_child_resumes_at_the_next_occurrence :
    returnedChild {saved with nextOutcome := 1, phase := .afterChild, activeValue := some a, activeBindings := some selectedA} =
      some {saved with nextOutcome := 1} := rfl

theorem returned_child_keeps_duplicate_before_distinct_choice :
    ({saved with nextOutcome := 1} : Snapshot).pending = [(a, selectedA), (b, selectedB)] := rfl

theorem ordinary_consumer_cannot_fake_child_return : returnedChild saved = none := rfl

theorem exhausted_cursor_releases_consumer :
    consume merge extend {saved with nextOutcome := 3} = .exhausted := rfl

theorem merge_failure_consumes_one_occurrence_without_a_child :
    consume (fun _ _ => none) extend saved = .skipped {saved with nextOutcome := 1} := rfl

theorem binder_failure_consumes_one_occurrence_without_a_child :
    consume merge (fun _ _ _ => none) saved = .skipped {saved with nextOutcome := 1} := rfl

theorem changed_error_is_emitted_before_binder_extension :
    consume merge (fun _ _ _ => none) {saved with outcomes := [(rawError, selectedA)]} =
      .failure (rawError, selectedA)
        {saved with outcomes := [(rawError, selectedA)], nextOutcome := 1} := rfl

theorem unchanged_error_source_remains_argument_data :
    consume merge extend {saved with original := rawError, outcomes := [(rawError, selectedA)]} =
      .child (rawError, selectedA)
        {saved with original := rawError, outcomes := [(rawError, selectedA)], nextOutcome := 1, phase := .afterChild, activeValue := some rawError, activeBindings := some selectedA} := rfl

theorem failed_merge_cannot_emit_the_reply_error :
    actionConfiguration {saved with outcomes := [(rawError, selectedA)]} [] []
      (consume (fun _ _ => none) extend {saved with outcomes := [(rawError, selectedA)]}) =
      ⟨[.argConsumer [] pick choice state], []⟩ := rfl

theorem changed_error_preserves_prior_answer_history :
    actionConfiguration {saved with outcomes := [(rawError, selectedA)]} [] [(b, selectedB)]
      (consume merge extend {saved with outcomes := [(rawError, selectedA)]}) =
      ⟨[.argConsumer [] pick choice state], [(b, selectedB), (rawError, selectedA)]⟩ := rfl

theorem saved_child_round_trip :
    readSnapshot (snapshotData {saved with original := nested, nextOutcome := 1, phase := .afterChild, activeValue := some a, activeBindings := some selectedA}) =
      some {saved with original := nested, nextOutcome := 1, phase := .afterChild, activeValue := some a, activeBindings := some selectedA} := by simp

theorem changed_cursor_changes_representation :
    snapshotData saved ≠ snapshotData {saved with nextOutcome := 1} := by decide

theorem lost_active_binding_changes_representation :
    snapshotData {saved with phase := .afterChild, activeValue := some a, activeBindings := some selectedA} ≠
      snapshotData {saved with phase := .afterChild, activeValue := some a, activeBindings := some selectedB} := by decide

theorem removed_duplicate_changes_representation :
    snapshotData saved ≠ snapshotData {saved with outcomes := [(a, selectedA), (b, selectedB)]} := by decide

theorem malformed_snapshot_tag_is_rejected :
    readSnapshot (.expression [.symbol "he-native-argument-snapshot-v1"]) = none := rfl

theorem unknown_phase_is_rejected : readPhase (.symbol "he-native-args-wait-v1") = none := rfl

theorem malformed_optional_selection_is_rejected :
    readOptionalAtom (.expression [.symbol "he-native-some-v1"]) = none := rfl

theorem negative_outcome_cursor_is_rejected :
    TypedApplyEncoding.readIndex (.grounded (.int (-1))) = none := rfl

private def policyA : Spec.Eval.SelectedTypePolicy :=
  ⟨.expression [.symbol "->", choice, Atom.atomType], [choice], Atom.atomType, rfl⟩
private def policyB : Spec.Eval.SelectedTypePolicy :=
  ⟨.expression [.symbol "->", Atom.undefinedType, Atom.atomType],
    [Atom.undefinedType], Atom.atomType, rfl⟩

theorem first_applicable_type_prevents_duplicate_overload_branch :
    scan [⟨policyA.functionType, .success policyA selectedA⟩,
      ⟨policyB.functionType, .success policyB selectedB⟩] =
      some (.success policyA selectedA) := rfl

theorem selected_type_does_not_request_suffix_reply :
    scan [⟨policyA.functionType, .success policyA selectedA⟩,
      ⟨policyB.functionType, .unresolved⟩] = some (.success policyA selectedA) := rfl

theorem unresolved_first_type_does_not_skip_to_later_success :
    scan [⟨policyA.functionType, .unresolved⟩,
      ⟨policyB.functionType, .success policyB selectedB⟩] = none := rfl

theorem failed_candidate_errors_are_discarded_upon_later_selection :
    scan [⟨policyA.functionType, .error [rawError]⟩,
      ⟨policyB.functionType, .success policyB selectedB⟩] =
      some (.success policyB selectedB) := rfl

theorem exhausted_candidate_errors_keep_source_order :
    scan [⟨policyA.functionType, .error [a, a]⟩,
      ⟨policyB.functionType, .error [b]⟩] = some (.exhausted [a, a, b] false) := rfl

theorem non_function_candidate_enables_tuple_fallback_after_exhaustion :
    scan [⟨choice, .nonFunction⟩,
      ⟨policyA.functionType, .error [rawError]⟩] = some (.exhausted [rawError] true) := rfl

theorem non_function_candidate_does_not_delay_selected_type :
    scan [⟨choice, .nonFunction⟩, ⟨policyA.functionType, .success policyA selectedA⟩,
      ⟨policyB.functionType, .unresolved⟩] = some (.success policyA selectedA) := rfl

theorem scanner_retains_unvisited_source_types :
    sourceTypes (⟨policyA.functionType, .success policyA selectedA⟩ ::
      unresolved [policyB.functionType, choice]) =
      [policyA.functionType, policyB.functionType, choice] := rfl

theorem empty_argument_history_cannot_change_binding_endpoint
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) :
    ¬RetainedArgumentSpecification.HistoryRel space dispatch live typing [] []
      selectedA [] selectedB := by
  have endpoints : ∀ (incoming outgoing : Bindings),
      RetainedArgumentSpecification.HistoryRel space dispatch live typing [] [] incoming [] outgoing →
      incoming = outgoing := by
    intro incoming outgoing history
    cases history
    rfl
  intro history
  have unequal : selectedA ≠ selectedB := by decide
  exact unequal (endpoints _ _ history)

end Mettapedia.Languages.MeTTa.HE.NativeArgumentProjectionControls
