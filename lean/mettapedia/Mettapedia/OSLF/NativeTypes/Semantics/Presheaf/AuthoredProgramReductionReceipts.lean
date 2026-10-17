import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredProgramReduction
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeReceiptChecking
import Mettapedia.OSLF.MeTTaIL.StructuralDescentAuthoredOrigins

/-!
# Endpoint-image comparison with the independent scoped execution judgment

The operational relation below uses original scoped firing receipts, not the
native event diagram. Every admitted receipt enters the image through the
computable receipt-to-frame checker. Conversely, an image witness yields an
original valid firing, its selected authored ordinal and its exact endpoints.
The image records endpoint existence; the separate event family retains the
whole receipt and the independently selected native schema view.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredProgramReduction

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Modal
open CurriedBindingLanguage
open NativeBindingEventAction (bound)
open NativeReceiptRechecking

variable (installed : AuthoredPipeline.Installed)

/-- Independent raw source readout of a genuine program-carrier value. -/
def programRead (index : Fin installed.operational.modal.length)
    {X : Base installed}
    (value : (meaning installed.operational.modal[index].program).obj X) : Pattern :=
  toPattern ((NativeBindingModalDiagram.programIso
    (installed.semanticHeaderAdmission index)).hom.app X value)

theorem native_source_read (index : Fin installed.operational.modal.length)
    (X : Base installed) (event : (installed.computedDiagram.events index).obj X) :
    programRead installed index
      ((installed.computedDiagram.projection (.source index)).app X event) =
      toPattern event.point.val.source := by
  apply congrArg toPattern
  exact NativeBindingModalDiagram.source_read installed.operational.modal[index]
    (installed.semanticHeaderAdmission index) installed.freeEmpty
    ((NativeOperationalProfile.check_exact _).mp installed.operationalMeaning) X event

theorem native_target_read (index : Fin installed.operational.modal.length)
    (X : Base installed) (event : (installed.computedDiagram.events index).obj X) :
    programRead installed index
      ((installed.computedDiagram.projection (.target index)).app X event) =
      event.point.val.receipt.target :=
  NativeBindingModalDiagram.target_read installed.operational.modal[index]
    (installed.semanticHeaderAdmission index) installed.freeEmpty
    ((NativeOperationalProfile.check_exact _).mp installed.operationalMeaning)
    installed.operational.nativeMeaning_admitted installed.operational.distinctLabels X event

/-- Original typed scoped execution, with its exact selected declaration
ordinal. No native event family occurs in this definition. -/
def scopedReceiptRelation (X : Base installed)
    (first last : (program installed).obj X) : Prop :=
  ∃ (index : Fin installed.operational.modal.length)
    (before after : (meaning installed.operational.modal[index].program).obj X)
    (receipt : Execution.RootAnswer installed.operational.Environment (bound X.unop.context)
      (.base (installed.nativeProgramSort index)) (programRead installed index before)),
    receipt.index = (installed.nativeSchema index).ordinal ∧
    receipt.target = programRead installed index after ∧
    (carrierInjection installed installed.operational.modal[index].program).app X before = first ∧
    (carrierInjection installed installed.operational.modal[index].program).app X after = last

theorem programRead_injective (index : Fin installed.operational.modal.length)
    (X : Base installed) : Function.Injective (programRead installed index (X := X)) := by
  intro first last same
  have intrinsic := CurriedBindingLanguage.toPattern_injective
    installed.operational.distinctLabels same
  let iso := NativeBindingModalDiagram.programIso (installed.semanticHeaderAdmission index)
  have roundTrip (value : (meaning installed.operational.modal[index].program).obj X) :
      iso.inv.app X (iso.hom.app X value) = value :=
    ConcreteCategory.congr_hom (C := Type) (congrArg (fun map => map.app X) iso.hom_inv_id) value
  exact (roundTrip first).symm.trans
    ((congrArg (iso.inv.app X) intrinsic).trans (roundTrip last))

/-- Every actual typed firing obtains a checked native frame, with the entire
ordered payload unchanged, and a witness in the endpoint image. -/
theorem every_receipt_enters_image (index : Fin installed.operational.modal.length)
    (X : Base installed) {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound X.unop.context)
      (.base (installed.nativeProgramSort index)) pattern)
    (selected : receipt.index = (installed.nativeSchema index).ordinal) :
    ∃ event : (installed.computedDiagram.events index).obj X,
      installed.checkReceiptFrame? index receipt selected = some event ∧
      read event.point.val.receipt = read receipt ∧
      programRead installed index
        ((installed.computedDiagram.projection (.source index)).app X event) = pattern ∧
      programRead installed index
        ((installed.computedDiagram.projection (.target index)).app X event) = receipt.target ∧
      ((source installed).app X ⟨index, event⟩,
        (target installed).app X ⟨index, event⟩) ∈ (endpointImage installed).obj X := by
  obtain ⟨frame, checked, retained⟩ := installed.checkReceiptFrame?_complete index receipt selected
  refine ⟨frame, checked, retained, ?_, ?_, ?_⟩
  · exact (native_source_read installed index X frame).trans
      (installed.checkReceiptFrame?_source index receipt selected checked)
  · exact (native_target_read installed index X frame).trans
      (installed.checkReceiptFrame?_target index receipt selected checked)
  · exact (event_image_iff installed X _ _).mpr ⟨index, frame, rfl, rfl⟩

/-- Endpoint image is exactly the original scoped receipt relation, with
the specified target and selected ordinal retained. -/
theorem image_iff_scoped_receipt (X : Base installed)
    (first last : (program installed).obj X) :
    (first, last) ∈ (endpointImage installed).obj X ↔
      scopedReceiptRelation installed X first last := by
  constructor
  · intro member
    obtain ⟨index, frame, before, after⟩ := (event_image_iff installed X first last).mp member
    let firstValue := (installed.computedDiagram.projection (.source index)).app X frame
    let lastValue := (installed.computedDiagram.projection (.target index)).app X frame
    have sourceRead : programRead installed index firstValue = toPattern frame.point.val.source :=
      native_source_read installed index X frame
    let receipt : Execution.RootAnswer installed.operational.Environment (bound X.unop.context)
        (.base (installed.nativeProgramSort index)) (programRead installed index firstValue) :=
      NativeBindingEventAction.castReceipt sourceRead.symm frame.point.val.receipt
    have retained : read receipt = read frame.point.val.receipt :=
      NativeBindingEventAction.castReceipt_read sourceRead.symm frame.point.val.receipt
    exact ⟨index, firstValue, lastValue, receipt,
      (congrArg Payload.index retained).trans frame.point.property,
      (congrArg Payload.target retained).trans (native_target_read installed index X frame).symm,
      before, after⟩
  · rintro ⟨index, firstValue, lastValue, receipt, selected, targetRead, before, after⟩
    obtain ⟨frame, _, _, sourceRead, actualTarget, _⟩ :=
      every_receipt_enters_image installed index X receipt selected
    have sameSource := programRead_injective installed index X sourceRead
    have sameTarget := programRead_injective installed index X (actualTarget.trans targetRead)
    apply (event_image_iff installed X first last).mpr
    refine ⟨index, frame, ?_, ?_⟩
    · exact (congrArg ((carrierInjection installed installed.operational.modal[index].program).app X)
        sameSource).trans before
    · exact (congrArg ((carrierInjection installed installed.operational.modal[index].program).app X)
        sameTarget).trans after

/-- Decoding an image witness recovers the independently checked scoped
firing judgment, rather than just another endpoint-pair witness. -/
theorem image_recovers_scoped_firing (X : Base installed)
    (first last : (program installed).obj X)
    (member : (first, last) ∈ (endpointImage installed).obj X) :
    ∃ (index : Fin installed.operational.modal.length)
      (before after : (meaning installed.operational.modal[index].program).obj X)
      (receipt : Execution.RootAnswer installed.operational.Environment (bound X.unop.context)
        (.base (installed.nativeProgramSort index)) (programRead installed index before)),
      RootFiring installed.operational.Environment (bound X.unop.context)
        (.base (installed.nativeProgramSort index)) (programRead installed index before)
        receipt.index receipt.trace receipt.captured receipt.completed receipt.history receipt.target ∧
      receipt.index = (installed.nativeSchema index).ordinal ∧
      receipt.target = programRead installed index after ∧
      (carrierInjection installed installed.operational.modal[index].program).app X before = first ∧
      (carrierInjection installed installed.operational.modal[index].program).app X after = last := by
  obtain ⟨index, before, after, receipt, selected, targetRead, firstRead, lastRead⟩ :=
    (image_iff_scoped_receipt installed X first last).mp member
  exact ⟨index, before, after, receipt, receipt.valid, selected, targetRead, firstRead, lastRead⟩

/-- Execution ordinals and original authored declaration indices stay
separate. The selected schema recovers the actual source declaration,
including its original name, both sides and ordered premise list. -/
theorem receipt_original_declaration (index : Fin installed.operational.modal.length)
    (X : Base installed) {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound X.unop.context)
      (.base (installed.nativeProgramSort index)) pattern)
    (selection : receipt.index = (installed.nativeSchema index).ordinal) :
    installed.operational.generated.snapshot.language.rewrites[
      (installed.nativeSchema index).declaration.declarationIndex]? =
        some (installed.nativeSchema index).declaration.authored ∧
    GeneralExecutionAdmission.selected
      installed.operational.generated.languageFragment.operational.ruleIndices
      (installed.nativeSchema index).declaration.declarationIndex = true ∧
    (installed.nativeSchema index).declaration.rule.name =
      (installed.nativeSchema index).declaration.authored.name ∧
    (installed.nativeSchema index).declaration.rule.left =
      (installed.nativeSchema index).declaration.authored.left ∧
    (installed.nativeSchema index).declaration.rule.right =
      (installed.nativeSchema index).declaration.authored.right ∧
    (installed.nativeSchema index).declaration.rule.premises =
      (installed.nativeSchema index).declaration.authored.premises := by
  obtain ⟨declaration, position, original, enabled, retained⟩ :=
    AuthoredOrigins.root_original_declaration installed.operational.generated.snapshot
      installed.operational.generated.languageFragment.operational (bound X.unop.context)
      (.base (installed.nativeProgramSort index)) pattern receipt
  have schemaPosition := List.mk_mem_zipIdx_iff_getElem?.mp (installed.nativeSchema index).declared
  rw [selection] at position
  have equal : declaration = (installed.nativeSchema index).declaration :=
    Option.some.inj (position.symm.trans schemaPosition)
  subst declaration
  exact ⟨original, enabled, retained⟩

/-- Separate generated schema views retain separate tags. This says nothing
about whether the views describe different physical firing occurrences. -/
theorem event_views_distinct (X : Base installed)
    (firstIndex lastIndex : Fin installed.operational.modal.length)
    (first : (installed.computedDiagram.events firstIndex).obj X)
    (last : (installed.computedDiagram.events lastIndex).obj X)
    (distinct : firstIndex ≠ lastIndex) :
    (eventInjection installed firstIndex).app X first ≠
      (eventInjection installed lastIndex).app X last := by
  intro same
  exact distinct (congrArg Sigma.fst same)

/-- An endpoint image can identify separate retained event views. The
separate event presheaf continues to distinguish their catalogue origins. -/
theorem same_endpoints_distinct_views (X : Base installed)
    (firstIndex lastIndex : Fin installed.operational.modal.length)
    (first : (installed.computedDiagram.events firstIndex).obj X)
    (last : (installed.computedDiagram.events lastIndex).obj X)
    (distinct : firstIndex ≠ lastIndex)
    (sameSource : (source installed).app X ⟨firstIndex, first⟩ =
      (source installed).app X ⟨lastIndex, last⟩)
    (sameTarget : (target installed).app X ⟨firstIndex, first⟩ =
      (target installed).app X ⟨lastIndex, last⟩) :
    (eventInjection installed firstIndex).app X first ≠
        (eventInjection installed lastIndex).app X last ∧
      (FreePresheafEventImage.endpointMap (graph installed)).app X
          ((eventInjection installed firstIndex).app X first) =
        (FreePresheafEventImage.endpointMap (graph installed)).app X
          ((eventInjection installed lastIndex).app X last) := by
  exact ⟨event_views_distinct installed X firstIndex lastIndex first last distinct,
    Prod.ext sameSource sameTarget⟩

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredProgramReduction
