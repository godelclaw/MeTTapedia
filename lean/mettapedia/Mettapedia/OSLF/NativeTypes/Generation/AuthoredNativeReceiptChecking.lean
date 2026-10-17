import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeEventCoverage
import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingSourceChecking

/-!
# Executable admission of original receipts into generated native families

The original scoped execution answer is parsed into its actual authored
binding term. The generated schema checker then checks focus, scope, sorting
and source reconstruction. The complete receipt remains unchanged. The
semantic comparison uses the independently constructed common native model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.NativeTypes.Modal
open CurriedBindingLanguage
open NativeReceiptRechecking
open NativeBindingEventAction (bound)

variable (installed : AuthoredPipeline.Installed)

def parsedReceiptPoint (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal)
    (parsed : SourceChecking.Parsed installed.nativePlan.snapshot.language ambient
      (installed.nativeProgramSort index) pattern) :
    NativeBindingSchemaCaptures.Selected (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index) :=
  ⟨⟨parsed.val, NativeBindingEventAction.castReceipt parsed.property.symm receipt⟩,
    (congrArg Payload.index (NativeBindingEventAction.castReceipt_read parsed.property.symm receipt)).trans selected⟩

theorem parsedReceiptPoint_read (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal)
    (parsed : SourceChecking.Parsed installed.nativePlan.snapshot.language ambient
      (installed.nativeProgramSort index) pattern) :
    read (installed.parsedReceiptPoint index receipt selected parsed).val.receipt = read receipt :=
  NativeBindingEventAction.castReceipt_read _ _

theorem parsedReceiptPoint_semantic (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal)
    (parsed : SourceChecking.Parsed installed.nativePlan.snapshot.language ambient
      (installed.nativeProgramSort index) pattern) :
    installed.parsedReceiptPoint index receipt selected parsed =
      installed.receiptPoint index receipt selected := by
  apply Subtype.ext
  apply NativeAuthoredEventAction.point_ext
  · apply toPattern_injective installed.operational.distinctLabels
    exact parsed.property.trans
      (NativeBindingReceiptSource.term_read (GeneralPlanEnvironment.grammar installed.nativePlan)
        installed.freeEmpty installed.operational.nativeMeaning_admitted
        installed.operational.distinctLabels receipt).symm
  · exact (installed.parsedReceiptPoint_read index receipt selected parsed).trans
      (installed.receiptPoint_read index receipt selected).symm

def checkReceiptPoint? (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal) :
    Option (NativeBindingSchemaCaptures.Selected (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index)) :=
  (SourceChecking.parse? installed.operational.nativeMeaning_admitted ambient
    (installed.nativeProgramSort index) pattern).map
      (installed.parsedReceiptPoint index receipt selected)

theorem checkReceiptPoint?_semantic (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal)
    {point : NativeBindingSchemaCaptures.Selected (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index)}
    (checked : installed.checkReceiptPoint? index receipt selected = some point) :
    point = installed.receiptPoint index receipt selected := by
  unfold checkReceiptPoint? at checked
  cases parsedAt : SourceChecking.parse? installed.operational.nativeMeaning_admitted ambient
      (installed.nativeProgramSort index) pattern with
  | none => simp only [parsedAt, Option.map_none] at checked; cases checked
  | some parsed =>
      simp only [parsedAt, Option.map_some, Option.some.injEq] at checked
      exact checked ▸ installed.parsedReceiptPoint_semantic index receipt selected parsed

theorem checkReceiptPoint?_read (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal)
    {point : NativeBindingSchemaCaptures.Selected (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index)}
    (checked : installed.checkReceiptPoint? index receipt selected = some point) :
    read point.val.receipt = read receipt := by
  rw [installed.checkReceiptPoint?_semantic index receipt selected checked]
  exact installed.receiptPoint_read index receipt selected

theorem checkReceiptPoint?_complete (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal) :
    installed.checkReceiptPoint? index receipt selected =
      some (installed.receiptPoint index receipt selected) := by
  obtain ⟨parsed, checked⟩ := SourceChecking.complete installed.operational.nativeMeaning_admitted
    (NativeBindingReceiptSource.source (GeneralPlanEnvironment.grammar installed.nativePlan)
      installed.freeEmpty receipt)
  change SourceChecking.Parsed installed.nativePlan.snapshot.language ambient
    (installed.nativeProgramSort index) pattern at parsed
  change SourceChecking.parse? installed.operational.nativeMeaning_admitted ambient
    (installed.nativeProgramSort index) pattern = some parsed at checked
  unfold checkReceiptPoint?
  rw [checked, Option.map_some, installed.parsedReceiptPoint_semantic index receipt selected parsed]

def checkReceiptFrame? (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal) :
    Option (NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index)) :=
  (installed.checkReceiptPoint? index receipt selected).bind
    (NativeBindingFrameChecking.frame? (installed.nativeSchema index))

theorem checkReceiptFrame?_semantic (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal) :
    installed.checkReceiptFrame? index receipt selected =
      NativeBindingFrameChecking.frame? (installed.nativeSchema index)
        (installed.receiptPoint index receipt selected) := by
  rw [checkReceiptFrame?, installed.checkReceiptPoint?_complete index receipt selected, Option.bind_some]

theorem checkReceiptFrame?_complete (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal) :
    ∃ frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
        ambient (installed.nativeProgramSort index),
      installed.checkReceiptFrame? index receipt selected = some frame ∧
      read frame.point.val.receipt = read receipt := by
  rw [installed.checkReceiptFrame?_semantic index receipt selected]
  exact installed.every_receipt_has_native_frame index receipt selected

theorem checkReceiptFrame?_independent_exact (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal) :
    (∃ frame, installed.checkReceiptFrame? index receipt selected = some frame) ↔
      ∃ frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
        ambient (installed.nativeProgramSort index),
        frame.point = installed.receiptPoint index receipt selected := by
  rw [installed.checkReceiptFrame?_semantic index receipt selected]
  exact NativeBindingFrameChecking.frame?_exact _ _

theorem checkReceiptFrame?_point (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal)
    {frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index)}
    (checked : installed.checkReceiptFrame? index receipt selected = some frame) :
    frame.point = installed.receiptPoint index receipt selected := by
  unfold checkReceiptFrame? at checked
  cases pointChecked : installed.checkReceiptPoint? index receipt selected with
  | none => simp only [pointChecked, Option.bind_none] at checked; cases checked
  | some point =>
      simp only [pointChecked, Option.bind_some] at checked
      exact (NativeBindingFrameChecking.frame?_point _ point checked).trans
        (installed.checkReceiptPoint?_semantic index receipt selected pointChecked)

theorem checkReceiptFrame?_read (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal)
    {frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index)}
    (checked : installed.checkReceiptFrame? index receipt selected = some frame) :
    read frame.point.val.receipt = read receipt := by
  rw [installed.checkReceiptFrame?_point index receipt selected checked]
  exact installed.receiptPoint_read index receipt selected

theorem checkReceiptFrame?_source (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal)
    {frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index)}
    (checked : installed.checkReceiptFrame? index receipt selected = some frame) :
    toPattern frame.point.val.source = pattern := by
  rw [installed.checkReceiptFrame?_point index receipt selected checked]
  exact NativeBindingReceiptSource.term_read (GeneralPlanEnvironment.grammar installed.nativePlan)
    installed.freeEmpty installed.operational.nativeMeaning_admitted
    installed.operational.distinctLabels receipt

theorem checkReceiptFrame?_target (index : Fin installed.operational.modal.length)
    {ambient : List String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal)
    {frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index)}
    (checked : installed.checkReceiptFrame? index receipt selected = some frame) :
    frame.point.val.receipt.target = receipt.target :=
  congrArg Payload.target (installed.checkReceiptFrame?_read index receipt selected checked)

theorem checkReceiptFrame?_native_read (index : Fin installed.operational.modal.length)
    {X : Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf.Base
      (algebra installed.nativePlan.snapshot.language)} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound X.unop.context)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal)
    {frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
      X.unop.context (installed.nativeProgramSort index)}
    (checked : installed.checkReceiptFrame? index receipt selected = some frame) :
    installed.nativeEventRead index (installed.nativeEventValue index frame) = read receipt :=
  (installed.nativeEventValue_read index frame).trans
    (installed.checkReceiptFrame?_read index receipt selected checked)

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed
