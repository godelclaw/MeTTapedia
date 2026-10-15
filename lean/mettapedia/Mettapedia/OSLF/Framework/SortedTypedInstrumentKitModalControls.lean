import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitModalComparison
import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitObservationControls

/-!
# Finite modal assays retain full typed data and proper original firings

An actual compiled modal test accepts the unit-padded complete value and
rejects a changed channel. Its independently root-only variant accepts both,
showing why the child assays matter. A retained proper original identity
firing also separates values beyond the empty current structural fragment.
Missing administrative origins reject the actual ask diamond, while supplied
receipt origins remain distinct even when their modal value reading agrees.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentKitModalControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.GSLT.InterfaceModalLogic
open SortedTypedInstruments SortedTypedInstrumentControls SortedTypedStructuralObservationControls

abbrev opened := SortedTypedInstrumentKitObservationControls.opened
abbrev originalRules := SortedTypedInstrumentKitObservationControls.originalRules

def completeProcessTest : Formula (Kit.Object opened) (Kit.interface opened (.original .process)) :=
  Kit.Modal.characteristic opened (sourcePayload 7) the_whole_typed_send_is_supported

theorem the_actual_finite_modal_test_reads_every_supported_native_right
    (right : ValueClass (source := sourceSignature) (Parallel := sourceParallel) (.original .process))
    (supported : Kit.ClassSupported opened right) :
    Holds (Kit.categoryRules (NativeOrigins := Nat) originalRules opened) completeProcessTest
      (Kit.value right supported) ↔ classOf (embed (sourcePayload 7)) = right :=
  Kit.Modal.characteristic_iff opened originalRules ⟨24⟩ _ the_whole_typed_send_is_supported right supported

theorem the_modal_assay_accepts_the_actual_unit_padding :
    Holds (Kit.categoryRules (NativeOrigins := Nat) originalRules opened) completeProcessTest
      (Kit.value (classEmbedding (classOf padded)) (Kit.classEmbedding_supported opened _)) :=
  (the_actual_finite_modal_test_reads_every_supported_native_right _ _).mpr
    (congrArg classEmbedding actual_unit_padding_changes_the_raw_root_but_not_the_class.symm)

theorem the_complete_child_assays_reject_the_changed_channel :
    ¬Holds (Kit.categoryRules (NativeOrigins := Nat) originalRules opened) completeProcessTest
      (Kit.value (classEmbedding (classOf (sourcePayload 11))) (Kit.classEmbedding_supported opened _)) := by
  intro accepted
  have completeRead := (the_actual_finite_modal_test_reads_every_supported_native_right _ _).mp accepted
  change classEmbedding (classOf (sourcePayload 7)) =
    classEmbedding (classOf (sourcePayload 11)) at completeRead
  have same := classEmbedding_injective completeRead
  have structural := (StructuralObservations.characteristic_holds_iff (sourcePayload 7) _).mpr same.symm
  exact changing_the_complete_channel_rejects_the_structural_test structural

def rootOnlyTest : Formula (Kit.Object opened) (Kit.interface opened (.original .process)) :=
  .diamond (Kit.probeArrow opened (.ask (.ordinary Symbol.send)) (Or.inl rfl)) .top

theorem the_independent_root_only_test_accepts_every_complete_channel (channel : Nat) :
    Holds (Kit.categoryRules (NativeOrigins := Nat) originalRules opened) rootOnlyTest
      (Kit.value (classEmbedding (classOf (sourcePayload channel))) (Kit.classEmbedding_supported opened _)) := by
  let arguments := sendArguments channel (.zero rfl)
  have children : ∀ position, Kit.Supported opened (arguments position) := by
    intro position
    fin_cases position
    · exact Kit.embed_supported opened (sourceName channel)
    · exact Kit.embed_supported opened (.zero rfl : SourceValue .process)
  have inputRead : classEmbedding (classOf (sourcePayload channel)) =
      classOf (sourceNode (source := sourceSignature) (Parallel := sourceParallel)
        (.ordinary Symbol.send) arguments) := by
    change classOf (embed (sourcePayload channel)) = _
    apply congrArg classOf
    rw [sourcePayload, embed_node]
    apply congrArg (sourceNode (source := sourceSignature) (Parallel := sourceParallel)
      (.ordinary Symbol.send))
    funext position
    fin_cases position <;> rfl
  exact ⟨Kit.value (classOf (bundle (source := sourceSignature) (Parallel := sourceParallel)
      (.ordinary Symbol.send) arguments))
    ⟨_, (Kit.bundle_supported_iff opened _ _).mpr ⟨Or.inl rfl, children⟩, rfl⟩,
    by simpa only [inputRead] using
      Kit.ask_step opened originalRules 24 (.ordinary Symbol.send) arguments (Or.inl rfl) children,
    True.intro⟩

theorem omitting_the_child_assays_loses_a_real_distinction :
    Holds (Kit.categoryRules (NativeOrigins := Nat) originalRules opened) rootOnlyTest
        (Kit.value (classEmbedding (classOf (sourcePayload 11))) (Kit.classEmbedding_supported opened _)) ∧
      ¬Holds (Kit.categoryRules (NativeOrigins := Nat) originalRules opened) completeProcessTest
        (Kit.value (classEmbedding (classOf (sourcePayload 11))) (Kit.classEmbedding_supported opened _)) :=
  ⟨the_independent_root_only_test_accepts_every_complete_channel 11,
    the_complete_child_assays_reject_the_changed_channel⟩

theorem full_modal_observation_and_the_actual_payload_fixed_point_agree
    (right : ValueClass (source := sourceSignature) (Parallel := sourceParallel) (.original .process))
    (supported : Kit.ClassSupported opened right) :
    (Kit.payloadSystem (NativeOrigins := Nat) opened originalRules).Bisimilar (.original .process)
      (classEmbedding (classOf padded)) right ↔
        LogicallyEquivalent (Kit.categoryRules (NativeOrigins := Nat) originalRules opened)
          (Kit.value (classEmbedding (classOf padded)) (Kit.classEmbedding_supported opened _))
          (Kit.value right supported) :=
  Kit.Modal.actual_same_fixed_point_iff_modal_observation_of_generated opened originalRules ⟨24⟩ _
    its_actual_equation_class_is_nevertheless_generated right supported

theorem a_retained_proper_original_firing_is_seen_by_the_actual_identity_diamond :
    Holds (Kit.categoryRules (NativeOrigins := Nat)
        SortedTypedInstrumentKitObservationControls.activeOriginalRules
        SortedTypedInstrumentKitTransitionControls.emptyKit)
      (.diamond (𝟙 _) .top) SortedTypedInstrumentKitObservationControls.activeFirst :=
  ⟨SortedTypedInstrumentKitObservationControls.activeFiring.result,
    SortedTypedInstrumentKitObservationControls.activeFiring.step, True.intro⟩

theorem the_inactive_unit_fails_the_same_actual_identity_diamond :
    ¬Holds (Kit.categoryRules (NativeOrigins := Nat)
        SortedTypedInstrumentKitObservationControls.activeOriginalRules
        SortedTypedInstrumentKitTransitionControls.emptyKit)
      (.diamond (𝟙 _) .top) SortedTypedInstrumentKitObservationControls.inactiveFirst := by
  rintro ⟨next, actual, _holds⟩
  exact SortedTypedInstrumentKitObservationControls.an_inactive_unit_cannot_match_the_actual_original_identity_firing
    next actual

theorem current_structural_equivalence_cannot_replace_the_full_modal_relation :
    StructuralObservations.PartialLogicalEquivalent SortedTypedInstrumentKitTransitionControls.emptyKit
      (classOf (.cut (signature := sourceSignature) (Parallel := sourceParallel)
        (sort := .process) rfl (sourcePayload 7) (.zero rfl)))
      (classOf (.zero (signature := sourceSignature) (Parallel := sourceParallel) (sort := .process) rfl)) ∧
      ¬LogicallyEquivalent (Kit.categoryRules (NativeOrigins := Nat)
        SortedTypedInstrumentKitObservationControls.activeOriginalRules
        SortedTypedInstrumentKitTransitionControls.emptyKit)
        SortedTypedInstrumentKitObservationControls.activeFirst SortedTypedInstrumentKitObservationControls.inactiveFirst := by
  refine ⟨SortedTypedInstrumentKitObservationControls.current_partial_structural_tests_do_not_supply_unrestricted_interactive_adequacy.1,
    ?_⟩
  intro compared
  exact the_inactive_unit_fails_the_same_actual_identity_diamond
    ((compared _).mp a_retained_proper_original_firing_is_seen_by_the_actual_identity_diamond)

theorem administrative_origin_emptiness_rejects_the_actual_root_diamond :
    ¬Holds (Kit.categoryRules (NativeOrigins := Empty)
      SortedTypedInstrumentKitObservationControls.noOriginalRules opened) rootOnlyTest
      (Kit.value (classEmbedding (classOf (sourcePayload 7))) (Kit.classEmbedding_supported opened _)) := by
  rintro ⟨next, actual, _holds⟩
  exact SortedTypedInstrumentKitObservationControls.no_firing_without_either_origin_family _ _ _ actual

theorem supplied_receipt_origins_remain_independent_of_the_modal_value_reading :
    ¬HEq (SortedTypedInstrumentKitObservationControls.askReceipt 24)
      (SortedTypedInstrumentKitObservationControls.askReceipt 25) :=
  SortedTypedInstrumentKitObservationControls.duplicate_supplied_origins_remain_distinct

end Mettapedia.OSLF.Framework.SortedTypedInstrumentKitModalControls
