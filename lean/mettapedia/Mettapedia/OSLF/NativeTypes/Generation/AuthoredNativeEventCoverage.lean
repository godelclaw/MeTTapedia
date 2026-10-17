import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeSemantics
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingGeneratedFrameCoverage
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingReceiptSource

/-!
# Installed native operational families cover every actual typed receipt

Successful authored generation stores the mechanically checked semantic
profile. Those earned checks construct a complete native event for every
corresponding scoped firing in every ambient context. Source, target and the
whole ordered operational receipt remain unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise GeneralExecutionAdmission StructuralDescent
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal
open CurriedBindingLanguage
open NativeReceiptRechecking
open NativeBindingEventAction (bound)

variable (installed : AuthoredPipeline.Installed)

abbrev nativePlan := BindingPipeline.plan installed.operational.generated

def semanticHeaderAdmission (index : Fin installed.operational.modal.length) :=
  AuthoredBindingNativeModel.checkedHeaders installed.operational installed.computedMeaningAdmission index

def nativeProgramSort (index : Fin installed.operational.modal.length) : String :=
  NativeBindingModalDiagram.programSort (installed.semanticHeaderAdmission index)

abbrev nativeSchema (index : Fin installed.operational.modal.length) :=
  NativeEventDeclarations.schema installed.nativePlan installed.operational.modal[index].origin

theorem nativeProgramSort_read (index : Fin installed.operational.modal.length) :
    (installed.nativeSchema index).programCarrier = .base (installed.nativeProgramSort index) := by
  have read := (NativeModalHeaders.decode_sound _
    (AuthoredBindingNativeModel.header_decoded installed.operational index)).2.1
  rw [← read, (installed.semanticHeaderAdmission index).program]
  rfl

theorem every_point_has_native_frame (index : Fin installed.operational.modal.length)
    {ambient : List String}
    (point : NativeBindingSchemaCaptures.Selected (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index)) :
    ∃ frame,
      NativeBindingFrameChecking.frame? (installed.nativeSchema index) point = some frame ∧
      frame.point = point :=
  NativeBindingGeneratedFrameCoverage.checker_covers_every_firing _ installed.freeEmpty
    installed.operational.distinctLabels installed.sourceTrees (installed.nativeProgramSort_read index) point

noncomputable def receiptPoint (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal) :
    NativeBindingSchemaCaptures.Selected (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index) :=
  ⟨NativeBindingReceiptSource.point (GeneralPlanEnvironment.grammar installed.nativePlan)
    installed.freeEmpty installed.operational.nativeMeaning_admitted installed.operational.distinctLabels receipt,
    (NativeBindingReceiptSource.point_index (GeneralPlanEnvironment.grammar installed.nativePlan)
      installed.freeEmpty installed.operational.nativeMeaning_admitted installed.operational.distinctLabels receipt).trans selected⟩

theorem receiptPoint_read (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal) :
    read (installed.receiptPoint index receipt selected).val.receipt = read receipt :=
  NativeBindingReceiptSource.point_read _ _ _ _ _

theorem every_receipt_has_native_frame (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal) :
    ∃ frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
        ambient (installed.nativeProgramSort index),
      NativeBindingFrameChecking.frame? (installed.nativeSchema index)
        (installed.receiptPoint index receipt selected) = some frame ∧
      read frame.point.val.receipt = read receipt := by
  obtain ⟨frame, checked, same⟩ := installed.every_point_has_native_frame index
    (installed.receiptPoint index receipt selected)
  exact ⟨frame, checked, same ▸ installed.receiptPoint_read index receipt selected⟩

/-- The event value is in the actual native comprehension interpreted by the
installed common constructor/operational signature. -/
noncomputable def nativeEventValue (index : Fin installed.operational.modal.length)
    {X : Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf.Base
      (algebra installed.nativePlan.snapshot.language)}
    (frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
      X.unop.context (installed.nativeProgramSort index)) :
    (CurriedNativeModalModel.eventScope installed.computedDiagram index).1.obj X :=
  (CurriedNativeModalModel.eventIso installed.computedDiagram index).inv.app X frame

noncomputable def nativeEventRead (index : Fin installed.operational.modal.length)
    {X : Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf.Base
      (algebra installed.nativePlan.snapshot.language)}
    (value : (CurriedNativeModalModel.eventScope installed.computedDiagram index).1.obj X) :
    Payload :=
  read ((CurriedNativeModalModel.eventIso installed.computedDiagram index).hom.app X value).point.val.receipt

theorem nativeEventValue_read (index : Fin installed.operational.modal.length)
    {X : Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf.Base
      (algebra installed.nativePlan.snapshot.language)}
    (frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
      X.unop.context (installed.nativeProgramSort index)) :
    installed.nativeEventRead index (installed.nativeEventValue index frame) = read frame.point.val.receipt := by
  have roundTrip := ConcreteCategory.congr_hom (C := Type)
    (congrArg (fun map => map.app X)
      (CurriedNativeModalModel.eventIso installed.computedDiagram index).inv_hom_id) frame
  exact congrArg (fun event => read event.point.val.receipt) roundTrip

theorem nativeEventValue_decode (index : Fin installed.operational.modal.length)
    {X : Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf.Base
      (algebra installed.nativePlan.snapshot.language)}
    (frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
      X.unop.context (installed.nativeProgramSort index)) :
    (CurriedNativeModalModel.eventIso installed.computedDiagram index).hom.app X
      (installed.nativeEventValue index frame) = frame :=
  ConcreteCategory.congr_hom (C := Type)
    (congrArg (fun map => map.app X)
      (CurriedNativeModalModel.eventIso installed.computedDiagram index).inv_hom_id) frame

theorem every_receipt_has_native_event (index : Fin installed.operational.modal.length)
    {X : Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf.Base
      (algebra installed.nativePlan.snapshot.language)} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound X.unop.context)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal) :
    ∃ value : (CurriedNativeModalModel.eventScope installed.computedDiagram index).1.obj X,
      installed.nativeEventRead index value = read receipt := by
  obtain ⟨frame, _, same⟩ := installed.every_receipt_has_native_frame index receipt selected
  exact ⟨installed.nativeEventValue index frame,
    (installed.nativeEventValue_read index frame).trans same⟩

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed
