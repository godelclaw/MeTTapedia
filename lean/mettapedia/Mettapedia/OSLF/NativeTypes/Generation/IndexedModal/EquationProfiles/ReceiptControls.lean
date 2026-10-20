import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.Controls
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.Receipts

/-!
# Full-receipt native observations over conditional equations

The two requested answers have the same result but different declaration
origins. Their classifiers inspect every rule-receipt payload field. Dropping
the second origin rejects its certificate and leaves its semantic question
unknown; it does not establish nonmembership.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.ReceiptControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralOccurrenceFrontier Complete
open GeneralCompletedFrontierControls

def test (slot : Fin 2) : ReceiptTest (request true) where
  accepts receipt :=
    receipt.job.declaration.declarationIndex == slot.val &&
    receipt.job.site.address == [] && receipt.matcherTrace == [] &&
    receipt.captured == [] && receipt.completed == [] && receipt.premiseHistory == [] &&
    receipt.localTarget == done && receipt.target == done
  transport _ _ move _ fired :=
    (Controls.conditional_law_impossible true move fired).elim

theorem each_origin_checked (slot : Fin 2) : (test slot).check (completed true) = true := by
  obtain ⟨answer, retained, _, payload⟩ := certified_physical_occurrence (admitted true)
    (completed_certificate true) two equation_exposes_two (reductionReceipt slot)
    (reduction_receipt_valid slot)
  apply List.any_eq_true.mpr
  refine ⟨answer, retained, ?_⟩
  rw [payload]
  have alternatives : slot.val = 0 ∨ slot.val = 1 := by omega
  rcases alternatives with index | index <;> simp [test, reductionReceipt, reductionJob,
    declaration, GeneralCompletedFrontierControls.binding, GeneralTypedSites.SiteData.here, index, done]

theorem full_receipt_family :
    [⟨0, by decide⟩, ⟨1, by decide⟩].all (fun slot : Fin 2 => (test slot).check (completed true)) = true := by
  apply List.all_eq_true.mpr
  intro slot member
  exact each_origin_checked slot

theorem source_receipt_family : ∀ slot : Fin 2, (test slot).Meaning :=
  fun slot => (test slot).check_sound (each_origin_checked slot)

def firstOnly : State (request true) :=
  {completed true with answers := ((completed true).answers.filter
      (fun answer => answer.val.firing.job.declaration.declarationIndex == 0))}

theorem missing_origin_rejected : (test ⟨1, by decide⟩).check firstOnly = false := by
  apply Bool.eq_false_iff.mpr
  intro checked
  obtain ⟨answer, retained, accepts⟩ := List.any_eq_true.mp checked
  change answer ∈ ((completed true).answers.filter
    (fun answer => answer.val.firing.job.declaration.declarationIndex == 0)) at retained
  have kept := (List.mem_filter.mp retained).2
  simp only [test, Bool.and_eq_true] at accepts
  have different := accepts.1.1.1.1.1.1.1
  simp only [beq_iff_eq] at kept different
  omega

theorem missing_origin_certificate_rejected : checkCertificate (request true) firstOnly = false := by
  apply Bool.eq_false_iff.mpr
  intro covered
  have accepted := ((test ⟨1, by decide⟩).check_exact (Controls.conditionalCertificate true).commute
    (admitted true) covered).mpr (source_receipt_family ⟨1, by decide⟩)
  rw [missing_origin_rejected] at accepted
  cases accepted

theorem rejected_evidence_is_unknown : (test ⟨1, by decide⟩).readout firstOnly = .unknown := by
  rw [ReceiptTest.readout, missing_origin_rejected, missing_origin_certificate_rejected]
  simp

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.ReceiptControls
