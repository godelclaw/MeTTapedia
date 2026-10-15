import Mettapedia.Languages.C11.ObjectStepData

/-!
# Byte/object execution controls

These controls distinguish representation copying from initialized-value
reads, array bounds from allocation bounds, and pointer formation from
dereference. Negative cases remain in the semantic model; native probes do
not execute invalid C accesses or overflowing pointer differences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ObjectControls

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open ByteRanges
open ByteStorageData

def byte8 : Profile := ⟨8, by decide⟩
def byte16 : Profile := ⟨16, by decide⟩
def difference64 : ArrayPointers.DifferenceProfile := ⟨63, by decide, by decide, .twosComplement true⟩
def difference32 : ArrayPointers.DifferenceProfile := ⟨31, by decide, by decide, .twosComplement true⟩
def difference17 : ArrayPointers.DifferenceProfile := ⟨16, by decide, by decide, .twosComplement true⟩
def differenceOnes64 : ArrayPointers.DifferenceProfile := ⟨63, by decide, by decide, .onesComplement⟩

def b (value : Nat) : Byte byte8 := BitVec.ofNat 8 value
def contents : List (Option (Byte byte8)) :=
  [some (b 10), none, some (b 30), some (b 40), some (b 50), some (b 60), some (b 70), some (b 80)]
def storage : Storage.State (Byte byte8) := [(7, ⟨true, contents⟩)]
def dead : Storage.State (Byte byte8) := [(7, ⟨false, contents⟩)]

def observeCopy (source : Range) (target : Address) : Option (List (Option (Byte byte8))) := do
  let saved ← copyBytes storage source target
  readBytes saved ⟨⟨7, 0⟩, 8⟩

theorem raw_read_retains_indeterminate : readBytes storage ⟨⟨7, 0⟩, 3⟩ =
    some [some (b 10), none, some (b 30)] := by decide

theorem one_past_empty_range : readBytes storage ⟨⟨7, 8⟩, 0⟩ = some [] := by decide
theorem one_past_nonempty_range_refused : readBytes storage ⟨⟨7, 8⟩, 1⟩ = none := by decide
theorem beyond_one_past_empty_refused : readBytes storage ⟨⟨7, 9⟩, 0⟩ = none := by decide
theorem dead_raw_read_refused : readBytes dead ⟨⟨7, 0⟩, 1⟩ = none := by decide
theorem dead_empty_read_refused : readBytes dead ⟨⟨7, 0⟩, 0⟩ = none := by decide
theorem absent_allocation_refused : readBytes storage ⟨⟨8, 0⟩, 0⟩ = none := by decide

theorem overlapping_copy_uses_snapshot : observeCopy ⟨⟨7, 0⟩, 4⟩ ⟨7, 2⟩ =
    some [some (b 10), none, some (b 10), none, some (b 30), some (b 40), some (b 70), some (b 80)] := by decide

theorem backward_overlapping_copy_uses_snapshot : observeCopy ⟨⟨7, 2⟩, 4⟩ ⟨7, 0⟩ =
    some [some (b 30), some (b 40), some (b 50), some (b 60), some (b 50), some (b 60), some (b 70), some (b 80)] := by decide

theorem indeterminate_copy_is_not_initialized :
    (copyBytes storage ⟨⟨7, 1⟩, 1⟩ ⟨7, 4⟩).bind
      (fun saved => ExecutableStorage.load saved ⟨7, 4⟩) = none := by decide

theorem overflowing_destination_refused : copyBytes storage ⟨⟨7, 0⟩, 2⟩ ⟨7, 7⟩ = none := by decide
theorem overflowing_source_refused : copyBytes storage ⟨⟨7, 7⟩, 2⟩ ⟨7, 0⟩ = none := by decide
theorem crossing_write_refused : writeBytes storage ⟨7, 7⟩ [some (b 1), some (b 2)] = none := by decide
theorem dead_write_refused : writeBytes dead ⟨7, 0⟩ [some (b 1)] = none := by decide

theorem empty_range_disjoint_inside_nonempty :
    Range.Disjoint ⟨⟨7, 3⟩, 0⟩ ⟨⟨7, 0⟩, 8⟩ := by decide
theorem adjacent_ranges_disjoint : Range.Disjoint ⟨⟨7, 0⟩, 4⟩ ⟨⟨7, 4⟩, 4⟩ := by decide
theorem overlapping_ranges_not_disjoint : ¬ Range.Disjoint ⟨⟨7, 0⟩, 4⟩ ⟨⟨7, 3⟩, 4⟩ := by decide

theorem conflicting_writes_do_not_commute :
    updateRange (updateRange (ByteRanges.heap storage) ⟨7, 0⟩ [some (b 1)]) ⟨7, 0⟩ [some (b 2)] ≠
      updateRange (updateRange (ByteRanges.heap storage) ⟨7, 0⟩ [some (b 2)]) ⟨7, 0⟩ [some (b 1)] := by
  intro equal
  have observed := congrArg (fun memory => (memory 7).2 0) equal
  simp [updateRange] at observed
  exact (by decide : b 2 ≠ b 1) observed

def catalog : ArrayPointers.Catalog :=
  [(101, ⟨7, 0, 2, 4⟩), (202, ⟨7, 4, 1, 4⟩)]

theorem stride_is_in_bytes : ArrayPointers.resolve storage catalog ⟨101, 2⟩ = some ⟨7, 4⟩ := by decide
theorem one_past_pointer_forms : ArrayPointers.add storage catalog ⟨101, 0⟩ 4 = some ⟨101, 4⟩ := by decide
theorem one_past_pointer_resolves : ArrayPointers.resolve storage catalog ⟨101, 4⟩ = some ⟨7, 8⟩ := by decide
theorem one_past_element_refused : ArrayPointers.elementRange storage catalog ⟨101, 4⟩ = none := by decide
theorem last_element_has_complete_bytes :
    ArrayPointers.elementRange storage catalog ⟨101, 3⟩ = some ⟨⟨7, 6⟩, 2⟩ := by decide
theorem one_past_can_return : ArrayPointers.add storage catalog ⟨101, 4⟩ (-1) = some ⟨101, 3⟩ := by decide
theorem negative_position_refused : ArrayPointers.add storage catalog ⟨101, 0⟩ (-1) = none := by decide
theorem past_end_formation_refused : ArrayPointers.add storage catalog ⟨101, 3⟩ 2 = none := by decide
theorem invalid_source_not_repaired_by_addition : ArrayPointers.add storage catalog ⟨101, 5⟩ (-1) = none := by decide
theorem subtraction_uses_indices_not_bytes :
    ArrayPointers.subtract difference64 storage catalog ⟨101, 4⟩ ⟨101, 1⟩ = some 3 := by decide
theorem negative_pointer_difference :
    ArrayPointers.subtract difference64 storage catalog ⟨101, 1⟩ ⟨101, 4⟩ = some (-3) := by decide
theorem different_array_views_can_resolve_same_byte :
    ArrayPointers.resolve storage catalog ⟨101, 2⟩ = ArrayPointers.resolve storage catalog ⟨202, 0⟩ := by decide
theorem different_array_views_cannot_be_subtracted :
    ArrayPointers.subtract difference64 storage catalog ⟨101, 2⟩ ⟨202, 0⟩ = none := by decide
theorem ended_lifetime_invalidates_pointer : ArrayPointers.resolve dead catalog ⟨101, 0⟩ = none := by decide
theorem ended_lifetime_invalidates_one_past : ArrayPointers.resolve dead catalog ⟨101, 4⟩ = none := by decide
theorem zero_stride_refused :
    ArrayPointers.resolve storage [(1, ⟨7, 0, 0, 4⟩)] ⟨1, 0⟩ = none := by decide
theorem array_view_cannot_exceed_allocation :
    ArrayPointers.resolve storage [(1, ⟨7, 0, 4, 4⟩)] ⟨1, 0⟩ = none := by decide

def largeStorage : Storage.State (Byte byte8) := [(9, ⟨true, List.replicate 70000 none⟩)]
def largeCatalog : ArrayPointers.Catalog := [(1, ⟨9, 0, 1, 70000⟩)]

theorem ptrdiff_overflow_refused :
    ArrayPointers.subtract difference17 largeStorage largeCatalog ⟨1, 70000⟩ ⟨1, 0⟩ = none := by
  norm_num [ArrayPointers.subtract, ArrayPointers.descriptor?, largeStorage, largeCatalog,
    difference17, ArrayPointers.DifferenceProfile.format, IntegerFormat.Represents,
    IntegerFormat.lower, IntegerFormat.upper, powerOfTwo]

def charLayout : ObjectLayout.Layout := ⟨0, 1, by decide, by decide⟩
def shortLayout : ObjectLayout.Layout := ⟨1, 2, by decide, by decide⟩
def intLayout : ObjectLayout.Layout := ⟨2, 4, by decide, by decide⟩
def longLayout : ObjectLayout.Layout := ⟨3, 8, by decide, by decide⟩
def fields : List ObjectLayout.Layout := [charLayout, intLayout, shortLayout]
def recordLayout : ObjectLayout.Layout := ObjectLayout.record fields (by decide)
def unionLayout : ObjectLayout.Layout := ObjectLayout.union fields (by decide)

theorem record_member_padding : (ObjectLayout.place fields 0).1.map ObjectLayout.Member.offset = [0, 4, 8] := by decide
theorem record_tail_padding : recordLayout.bytes = 12 := by decide
theorem record_maximum_alignment : recordLayout.alignment = 4 := by decide
theorem union_members_overlap_at_start : unionLayout.bytes = 4 := by decide
theorem record_array_uses_padded_stride : (ObjectLayout.array recordLayout 3 (by decide)).bytes = 36 := by decide
theorem nested_array_uses_row_stride :
    (ObjectLayout.view 7 0 (ObjectLayout.array shortLayout 3 (by decide)) 2).elementBytes = 6 := rfl

theorem invalid_byte_not_truncated : decodeByte byte8 256 = none := rfl
theorem wider_character_profile_retains_value : decodeByte byte16 511 = some (BitVec.ofNat 16 511) := rfl
theorem indeterminate_marker_round_trip : decodeContent byte8 none = some none := rfl
theorem byte_decoder_checks_dead_records : decodeStorage byte8 [(7, ⟨false, [some 256]⟩)] = none := rfl
theorem byte_decoder_checks_shadowed_records :
    decodeStorage byte8 [(7, ⟨true, [some 1]⟩), (7, ⟨false, [some 256]⟩)] = none := rfl
theorem dead_record_retained_by_codec : encodeStorage (profile := byte8) dead = [(7, ⟨false,
    [some 10, none, some 30, some 40, some 50, some 60, some 70, some 80]⟩)] := rfl

def state : ObjectStep.State (Byte byte8) := ⟨storage, catalog⟩
def writeInput : ObjectStep.Input (Byte byte8) :=
  ⟨state, .writeRepresentation ⟨7, 2⟩ [some (b 77), some (b 88)], .failure⟩
def writtenStorage : Storage.State (Byte byte8) := ExecutableStorage.put storage 7
  ⟨true, [some (b 10), none, some (b 77), some (b 88), some (b 50), some (b 60), some (b 70), some (b 80)]⟩
def writtenState : ObjectStep.State (Byte byte8) := ⟨writtenStorage, catalog⟩

theorem object_step_writes_once : ObjectStep.execute difference64 .failure state writeInput.request =
    some (.updated, writtenState) := by decide
theorem pending_step_retains_updated_residual : (ObjectStep.machine difference64).run 1 (.pending writeInput) =
    ([⟨writeInput, .updated, writtenState⟩], .exhausted (.completed .updated writtenState)) :=
  ObjectStep.accepted_residual difference64 writeInput .updated writtenState object_step_writes_once
theorem resumed_completed_state_has_no_more_receipts :
    ((ObjectStep.machine difference64).run 20 (.completed .updated writtenState)).1 = [] := rfl
theorem write_request_charged_once :
    (ObjectStep.machine difference64).spent ObjectStep.requestCharge 2 (.pending writeInput) = 1 := by decide
theorem byte_write_account_is_separate :
    (ObjectStep.machine difference64).spent (ObjectStep.byteWriteCharge difference64) 2 (.pending writeInput) = 2 := by decide

theorem changed_byte_policy_refused : ObjectStepData.decodeConfiguration byte16 difference64
    (ObjectStepData.encodeConfiguration byte8 difference64 (.pending writeInput)) = none := rfl
theorem changed_difference_width_refused : ObjectStepData.decodeConfiguration byte8 difference32
    (ObjectStepData.encodeConfiguration byte8 difference64 (.pending writeInput)) = none := rfl
theorem changed_difference_representation_refused : ObjectStepData.decodeConfiguration byte8 differenceOnes64
    (ObjectStepData.encodeConfiguration byte8 difference64 (.completed .updated writtenState)) = none := rfl
theorem completed_data_advance_does_not_repeat_write : ObjectStepData.advanceData byte8 difference64
    (ObjectStepData.encodeConfiguration byte8 difference64 (.completed .updated writtenState)) =
      some (.returned .updated (encodeState writtenState)) := rfl
theorem invalid_write_byte_has_no_request : ObjectStepData.decodeRequest byte8
    (.writeRepresentation ⟨7, 0⟩ [some 256]) = none := rfl
theorem conflicting_retirement_is_refused : ExecutableStorage.free dead (some ⟨7, 0⟩) = none := rfl
theorem interior_retirement_is_refused : ExecutableStorage.free storage (some ⟨7, 1⟩) = none := rfl
theorem retired_identity_cannot_be_allocated_again : ExecutableStorage.allocate dead 8 (.fresh 7) = none := rfl
theorem allocation_failure_retains_complete_storage : ExecutableStorage.allocate storage 8 .failure = some (none, storage) := rfl

end Mettapedia.Languages.C11.ObjectControls
