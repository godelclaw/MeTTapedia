import Mettapedia.OSLF.NativeTypes.Consumers.MM2Batch
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ResumableControls
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorControls

/-!
# A real two-path MM2 publication query

The existing transitive-join fixture has two physical derivations of one
conclusion. One grant retains one private answer; another retains both answers
without proving exhaustion. Only completion yields a publication receipt.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.GSLT.LanguageDef
open ProgrammableSpaceMM2ReceiptControls ProgrammableSpaceMM2ResumableControls
open MM2Batch

def target : List Atom := context ++ [reachable]
def completeReceipt : ProgrammableSpaceMM2.Receipt := ⟨joinRequest, joinSource, joinRows⟩

theorem complete_receipt_after : after .sinkMajor completeReceipt = target :=
  publication_preserves_support_not_derivation_multiplicity

theorem captured_join : joinSource = checkpoint100.before := rfl

theorem selected_join :
    selectedDirective .leaveInert checkpoint100.before = some checkpoint100.request.directive :=
  (selectedDirective_exact _ _ _).mpr selected

theorem complete_check :
    check .sinkMajor .leaveInert joinSource target checkpoint100 100 = .proved completeReceipt 177 := by
  rw [check_completed .sinkMajor .leaveInert joinSource _ checkpoint100 100 177 finished
    captured_join selected continued_cursor_finishes]
  change (if after .sinkMajor completeReceipt = target then CheckResult.proved completeReceipt 177 else CheckResult.refuted) = _
  rw [if_pos complete_receipt_after]

theorem generated_native_type_holds :
    Inhabits .sinkMajor .leaveInert target (joinSource, .matching checkpoint100) :=
  (check_proved .sinkMajor _ _ _ _ _ _ _ complete_check).1

theorem one_private_answer_is_unknown :
    check .sinkMajor .leaveInert joinSource target checkpoint100 0 = .unknown checkpoint100 := by
  rw [check_paused .sinkMajor .leaveInert joinSource target checkpoint100 0 100 packet100
    captured_join selected (ProgrammableSpaceMM2Resumable.Checkpoint.zero_grant _)]
  rfl

theorem both_answers_still_unknown :
    check .sinkMajor .leaveInert joinSource target checkpoint100 50 = .unknown checkpoint150 := by
  rw [check_paused .sinkMajor .leaveInert joinSource target checkpoint100 50 150 packet150
    captured_join selected (by rfl)]
  rfl

/-- Unknown is not nonmembership: the same retained state has the generated
publication type, while the current grant has not earned a complete receipt. -/
theorem unknown_is_not_refutation :
    check .sinkMajor .leaveInert joinSource target checkpoint100 50 = .unknown checkpoint150 ∧
      Inhabits .sinkMajor .leaveInert target (joinSource, .matching checkpoint100) :=
  ⟨both_answers_still_unknown, generated_native_type_holds⟩

theorem stale_snapshot_refuted :
    check .sinkMajor .leaveInert (.symbol "changed" :: joinSource) target checkpoint100 100 = .refuted := by
  unfold check
  rw [if_neg]
  intro same
  have sizes := congrArg List.length same
  change joinSource.length + 1 = joinSource.length at sizes
  omega

theorem stale_snapshot_lacks_native_type :
    ¬ Inhabits .sinkMajor .leaveInert target (.symbol "changed" :: joinSource, .matching checkpoint100) :=
  check_refuted .sinkMajor _ _ _ _ _ stale_snapshot_refuted

theorem wrong_target_refuted :
    check .sinkMajor .leaveInert joinSource [] checkpoint100 100 = .refuted := by
  rw [check_completed .sinkMajor .leaveInert joinSource _ checkpoint100 100 177 finished
    captured_join selected continued_cursor_finishes]
  change (if after .sinkMajor completeReceipt = [] then CheckResult.proved completeReceipt 177 else CheckResult.refuted) = _
  rw [if_neg]
  rw [complete_receipt_after]
  decide +kernel

theorem wrong_target_lacks_native_type :
    ¬ Inhabits .sinkMajor .leaveInert [] (joinSource, .matching checkpoint100) :=
  check_refuted .sinkMajor _ _ _ _ _ wrong_target_refuted

theorem both_physical_paths_retained :
    completeReceipt.witnessesInSourceOrder.map (List.map Prod.snd) =
      [[0, 1, 2], [0, 3, 4]] := two_paths_retain_physical_positions

theorem one_conclusion_two_receipt_rows :
    joinRows.length = 2 ∧
      joinRows.map (fun row => applySubst row.1 conclusion) = [reachable, reachable] :=
  ⟨by simpa only [List.length_map] using two_paths_have_distinct_substitutions.1,
    two_paths_emit_same_conclusion⟩

def partialReceipt : ProgrammableSpaceMM2.Receipt :=
  ⟨joinRequest, joinSource, joinRows.take 1⟩

theorem partial_receipt_cannot_be_published (spent : Nat) :
    check .sinkMajor .leaveInert joinSource target checkpoint100 100 ≠ .proved partialReceipt spent := by
  rw [complete_check]
  intro same
  have receiptSame := (CheckResult.proved.inj same).1
  have sizes := congrArg (fun receipt : ProgrammableSpaceMM2.Receipt => receipt.rows.length) receiptSame
  change joinRows.length = (joinRows.take 1).length at sizes
  rw [List.length_take, one_conclusion_two_receipt_rows.1] at sizes
  contradiction

abbrev rowSource := ProgrammableSpaceMM2RowMajorControls.source
abbrev rowCheckpoint := ProgrammableSpaceMM2RowMajorControls.checkpoint10
abbrev rowTarget := ProgrammableSpaceMM2RowMajorControls.nativeAfter
abbrev sinkTarget := ProgrammableSpaceMM2RowMajorControls.sourceAfter

def rowReceipt : ProgrammableSpaceMM2.Receipt :=
  ⟨ProgrammableSpaceMM2RowMajorControls.request, rowSource,
    ProgrammableSpaceMM2RowMajorControls.actualRows⟩

theorem captured_row : rowSource = rowCheckpoint.before := rfl

theorem selected_row :
    selectedDirective .leaveInert rowCheckpoint.before = some rowCheckpoint.request.directive :=
  (selectedDirective_exact _ _ _).mpr ProgrammableSpaceMM2RowMajorControls.selected

theorem row_receipt_after : after .rowMajor rowReceipt = rowTarget :=
  ProgrammableSpaceMM2RowMajorControls.native_finalization

theorem sink_receipt_after : after .sinkMajor rowReceipt = sinkTarget :=
  ProgrammableSpaceMM2RowMajorControls.source_finalization

theorem row_target_ne_sink_target : rowTarget ≠ sinkTarget := by
  intro same
  exact ProgrammableSpaceMM2RowMajorControls.support_separation
    (congrArg ProgrammableSpaceMM2RowMajorWrites.support same)

theorem row_major_check :
    check .rowMajor .leaveInert rowSource rowTarget rowCheckpoint 100 = .proved rowReceipt 30 := by
  rw [check_completed .rowMajor .leaveInert rowSource rowTarget rowCheckpoint 100 30
    ProgrammableSpaceMM2RowMajorControls.finished captured_row
    ProgrammableSpaceMM2RowMajorControls.selected
    ProgrammableSpaceMM2RowMajorControls.continued_cursor_finishes]
  change (if after .rowMajor rowReceipt = rowTarget then CheckResult.proved rowReceipt 30 else CheckResult.refuted) = _
  rw [if_pos row_receipt_after]

theorem sink_major_check :
    check .sinkMajor .leaveInert rowSource sinkTarget rowCheckpoint 100 = .proved rowReceipt 30 := by
  rw [check_completed .sinkMajor .leaveInert rowSource sinkTarget rowCheckpoint 100 30
    ProgrammableSpaceMM2RowMajorControls.finished captured_row
    ProgrammableSpaceMM2RowMajorControls.selected
    ProgrammableSpaceMM2RowMajorControls.continued_cursor_finishes]
  change (if after .sinkMajor rowReceipt = sinkTarget then CheckResult.proved rowReceipt 30 else CheckResult.refuted) = _
  rw [if_pos sink_receipt_after]

theorem row_major_rejects_sink_target :
    check .rowMajor .leaveInert rowSource sinkTarget rowCheckpoint 100 = .refuted := by
  rw [check_completed .rowMajor .leaveInert rowSource sinkTarget rowCheckpoint 100 30
    ProgrammableSpaceMM2RowMajorControls.finished captured_row
    ProgrammableSpaceMM2RowMajorControls.selected
    ProgrammableSpaceMM2RowMajorControls.continued_cursor_finishes]
  change (if after .rowMajor rowReceipt = sinkTarget then CheckResult.proved rowReceipt 30 else CheckResult.refuted) = _
  rw [if_neg]
  exact fun same => row_target_ne_sink_target (row_receipt_after.symm.trans same)

theorem sink_major_rejects_row_target :
    check .sinkMajor .leaveInert rowSource rowTarget rowCheckpoint 100 = .refuted := by
  rw [check_completed .sinkMajor .leaveInert rowSource rowTarget rowCheckpoint 100 30
    ProgrammableSpaceMM2RowMajorControls.finished captured_row
    ProgrammableSpaceMM2RowMajorControls.selected
    ProgrammableSpaceMM2RowMajorControls.continued_cursor_finishes]
  change (if after .sinkMajor rowReceipt = rowTarget then CheckResult.proved rowReceipt 30 else CheckResult.refuted) = _
  rw [if_neg]
  exact fun same => row_target_ne_sink_target (same.symm.trans sink_receipt_after)

/-- These are distinct generated native types because the actual public
languages distinguish their effects, despite sharing matcher and receipt. -/
theorem native_profiles_separate :
    Inhabits .rowMajor .leaveInert rowTarget (rowSource, .matching rowCheckpoint) ∧
      ¬ Inhabits .sinkMajor .leaveInert rowTarget (rowSource, .matching rowCheckpoint) ∧
      Inhabits .sinkMajor .leaveInert sinkTarget (rowSource, .matching rowCheckpoint) ∧
      ¬ Inhabits .rowMajor .leaveInert sinkTarget (rowSource, .matching rowCheckpoint) :=
  ⟨(check_proved _ _ _ _ _ _ _ _ row_major_check).1,
    check_refuted _ _ _ _ _ _ sink_major_rejects_row_target,
    (check_proved _ _ _ _ _ _ _ _ sink_major_check).1,
    check_refuted _ _ _ _ _ _ row_major_rejects_sink_target⟩

/-- Runtime measurements expose logical poll charges and receipt size. They
are not physical runtime or C instruction-cost claims. -/
def summary (result : CheckResult) : Verdict × Nat × Nat :=
  match result with
  | .proved receipt spent => (.proved, spent, receipt.rows.length)
  | .refuted => (.refuted, 0, 0)
  | .unknown checkpoint => (.unknown, checkpoint.spent, 0)

#eval summary (check .sinkMajor .leaveInert joinSource target checkpoint100 0)
#eval summary (check .sinkMajor .leaveInert joinSource target checkpoint100 50)
#eval summary (check .sinkMajor .leaveInert joinSource target checkpoint100 100)
#eval summary (check .sinkMajor .leaveInert (.symbol "changed" :: joinSource) target checkpoint100 100)
#eval summary (check .sinkMajor .leaveInert joinSource [] checkpoint100 100)

#eval summary (check .rowMajor .leaveInert rowSource rowTarget rowCheckpoint 100)
#eval summary (check .sinkMajor .leaveInert rowSource sinkTarget rowCheckpoint 100)
#eval summary (check .rowMajor .leaveInert rowSource sinkTarget rowCheckpoint 100)
#eval summary (check .sinkMajor .leaveInert rowSource rowTarget rowCheckpoint 100)

end Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchControls
