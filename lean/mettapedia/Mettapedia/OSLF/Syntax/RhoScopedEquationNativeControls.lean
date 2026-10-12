import Mettapedia.OSLF.Syntax.ScopedBindingEquationNativePossibility
import Mettapedia.OSLF.Syntax.RhoScopedEquationBindingControls

/-!+# Varying native certificates on actual rho binding occurrences

The source-equation output readout determines a genuinely varying finite
family. Substitution can grow its fibres and preserves the supplied finite
witness. An actual communication emits an output and admits two certificate
values; a discarding communication does not admit the second value. Duplicate
rule origins remain distinct in the native dependent-sum receipts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedEquationNativeControls

open _root_.CategoryTheory RhoSchema ScopedEncoding ScopedEquationEvents
open RhoScopedEquationEventControls RhoScopedEquationBindingControls
open ScopedEquationNativePossibility
open Mettapedia.TypeTheory.DisplayedPresheafTransport

local instance : Quiver (Scope sig) := bindingFrameQuiver sig

theorem quotient_count_le_bind {source destination : Ctx sig} (change : Sub sig source destination)
    (value : TermQ rhoSourceE source Srt.pr) :
    RhoSourceOutputPredicate.count value ≤ RhoSourceOutputPredicate.count (bindQ change value) := by
  induction value using Quotient.inductionOn with
  | _ term => exact RhoSourceOutputPredicate.outputCount_le_bind change term

private theorem future_count_le {before after : (values rhoSourceE Srt.pr).Elements}
    (change : before ⟶ after) :
    RhoSourceOutputPredicate.count before.2.down ≤ RhoSourceOutputPredicate.count after.2.down := by
  have same : bindQ change.val.unop before.2.down = after.2.down :=
    congrArg ULift.down change.property
  exact same ▸ quotient_count_le_bind change.val.unop before.2.down

/-- The fibre is determined by a full equation-compatible structural readout. -/
def outputCertificates : DisplayedFamily (values rhoSourceE Srt.pr) where
  obj point := Fin (RhoSourceOutputPredicate.count point.2.down + 1)
  map change := TypeCat.ofHom (fun certificate =>
    ⟨certificate.val, certificate.isLt.trans_le (Nat.add_le_add_right (future_count_le change) 1)⟩)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Fin.ext
    rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Fin.ext
    rfl

def closedWorld : (Syntactic.Ctxt sig)ᵒᵖ := Opposite.op ⟨[]⟩

theorem null_fibre : outputCertificates.obj
    (⟨closedWorld, ULift.up (Quotient.mk _ nilP)⟩ : (values rhoSourceE Srt.pr).Elements) = Fin 1 := rfl

theorem output_fibre : outputCertificates.obj
    (⟨closedWorld, ULift.up (Quotient.mk _ RhoSourceOutputPredicate.output)⟩ :
      (values rhoSourceE Srt.pr).Elements) = Fin 2 := rfl

def emitContinuation : (i : Fin metas.length) → Term sig (metas.get i).1 (metas.get i).2
  | ⟨0, _⟩ => .op Op.out (.cons (.var .zero) (.cons (.op Op.nil .nil) .nil))

def emitRoot : ContextualRootEvents.Instance comm.unpositioned [] where
  body := ContextualAssignment.ofClosed emitContinuation []
  close := closeComm

theorem emit_root_target : emitRoot.target = RhoSourceOutputPredicate.output := rfl

def emitOccurrence (index : Fin 2) : Event rules parallelPermission ([], Srt.pr) where
  index := index
  holeContext := []
  root := emitRoot
  context := .nil
  permitted := .nil _

def emitPoint (index : Fin 2) : (eventPresheaf rules parallelPermission Srt.pr).Elements :=
  ⟨closedWorld, emitOccurrence index⟩

def emitCertificate (index value : Fin 2) :
    (certified rhoSourceE rules parallelPermission Srt.pr outputCertificates).obj (emitPoint index) :=
  value

def emitSourcePoint : (values rhoSourceE Srt.pr).Elements :=
  (sourceNatural rules parallelPermission rhoSourceE Srt.pr).mapElements.obj (emitPoint 0)

def emitReceipt (index value : Fin 2) :
    (possibilities rhoSourceE rules parallelPermission Srt.pr outputCertificates).obj emitSourcePoint :=
  retain outputCertificates (emitPoint index) (emitCertificate index value)

theorem actual_emit_step : RootStep comm emitRoot.source RhoSourceOutputPredicate.output :=
  rootStep_of_instance comm { body := emitContinuation, close := closeComm }

theorem native_receipt_keeps_occurrence (index value : Fin 2) :
    receiptEvent outputCertificates (emitReceipt index value) = emitOccurrence index :=
  retain_event outputCertificates (emitPoint index) (emitCertificate index value)

theorem native_receipt_keeps_certificate (index value : Fin 2) :
    (receiptCertificate outputCertificates (emitReceipt index value)).val = value.val := rfl

theorem duplicate_native_origins_distinct : emitReceipt 0 0 ≠ emitReceipt 1 0 := by
  intro same
  have events := congrArg (receiptEvent outputCertificates) same
  have origins : (0 : Fin 2) = 1 := congrArg Event.index events
  exact (by decide : (0 : Fin 2) ≠ 1) origins

theorem different_native_certificates_distinct : emitReceipt 0 0 ≠ emitReceipt 0 1 := by
  intro same
  have certificates := congrArg (fun receipt =>
    (receiptCertificate outputCertificates receipt).val) same
  change (0 : Nat) = 1 at certificates
  cases certificates

def discardPoint (index : Fin 2) : (eventPresheaf rules parallelPermission Srt.pr).Elements :=
  ⟨closedWorld, occurrence index⟩

theorem discard_rejects_second_certificate (index : Fin 2) :
    ¬ ∃ certificate :
        (certified rhoSourceE rules parallelPermission Srt.pr outputCertificates).obj
          (discardPoint index), certificate.val = 1 := by
  rintro ⟨certificate, same⟩
  have bound : certificate.val < 1 := certificate.isLt
  omega

/-- This continuation returns the caller's process, rather than the received name. -/
def callerProcessContinuation : ContextualAssignment sig metas [Srt.pr]
  | ⟨0, _⟩ => .var (.succ .zero)

def closeCallerProcess : Sub sig G [Srt.pr]
  | _, .zero => weaken chan
  | _, .succ .zero => .op Op.nil .nil

def openProcessRoot : ContextualRootEvents.Instance comm.unpositioned [Srt.pr] where
  body := callerProcessContinuation
  close := closeCallerProcess

def openProcessOccurrence : Event rules parallelPermission ([Srt.pr], Srt.pr) where
  index := 0
  holeContext := [Srt.pr]
  root := openProcessRoot
  context := .nil
  permitted := .nil _

def supplyOutput : Sub sig [Srt.pr] []
  | _, .zero => RhoSourceOutputPredicate.output

def openProcessPoint : (eventPresheaf rules parallelPermission Srt.pr).Elements :=
  ⟨Opposite.op ⟨[Srt.pr]⟩, openProcessOccurrence⟩

def closedProcessPoint : (eventPresheaf rules parallelPermission Srt.pr).Elements :=
  ⟨closedWorld, openProcessOccurrence.map [] supplyOutput⟩

def processChange : openProcessPoint ⟶ closedProcessPoint :=
  CategoryOfElements.homMk _ _ (Quiver.Hom.op supplyOutput) rfl

theorem actual_open_process_target : openProcessOccurrence.target = .var .zero := rfl

theorem actual_future_process_target :
    (openProcessOccurrence.map [] supplyOutput).target = RhoSourceOutputPredicate.output := rfl

def openProcessCertificate :
    (certified rhoSourceE rules parallelPermission Srt.pr outputCertificates).obj openProcessPoint :=
  ⟨0, by decide⟩

def futureProcessCertificate :
    (certified rhoSourceE rules parallelPermission Srt.pr outputCertificates).obj closedProcessPoint :=
  ⟨1, by decide⟩

theorem future_certificate_action_computes :
    ((certified rhoSourceE rules parallelPermission Srt.pr outputCertificates).map
      processChange openProcessCertificate).val = 0 := rfl

/-- A new future certificate exists without being the reindexing of any
old certificate. Naturality preserves witnesses; it does not invent them. -/
theorem new_future_certificate_not_in_image :
    ¬ ∃ old : (certified rhoSourceE rules parallelPermission Srt.pr outputCertificates).obj
        openProcessPoint,
      (certified rhoSourceE rules parallelPermission Srt.pr outputCertificates).map
          processChange old = futureProcessCertificate := by
  rintro ⟨old, same⟩
  have values := congrArg Fin.val same
  change old.val = 1 at values
  have bound : old.val < 1 := old.isLt
  omega

end Mettapedia.OSLF.Binding.RhoScopedEquationNativeControls
