import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics
import Mettapedia.GSLT.Core.InteractionEvent
import Mettapedia.TypeTheory.GuardEvidenceComprehension

/-!
# Typed occurrence histories and native receipt families

Complete equation paths and primitive origins are retained beside target
certificates. The interaction event is indexed by original declaration and
typed occurrence address, rather than by a common target alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceNativeReceipts

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission GeneralOccurrenceSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted

variable (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)

abbrev ReceiptFamily (source : Pattern) :=
  {receipt : GeneralOccurrenceSemantics.Receipt // receipt.Valid plan bound type source}

def interaction : Mettapedia.GSLT.Core.InteractionEvent.InteractionPresentation (gslt plan bound type) where
  Site := Nat × List Nat × List GeneralTypedSites.TypingFrame
  Event site source target :=
    {receipt : ReceiptFamily plan bound type source //
      site = (receipt.val.firing.job.declaration.declarationIndex, receipt.val.firing.job.site.address,
        receipt.val.firing.job.site.typingFrames) ∧ receipt.val.target = target}
  sound := by
    intro site source target event
    rw [← event.property.2]
    exact Receipt.semantic_step plan bound type event.val.property

def asInteraction {source : Pattern} (receipt : ReceiptFamily plan bound type source) :
    (interaction plan bound type).Enabled source where
  site := (receipt.val.firing.job.declaration.declarationIndex, receipt.val.firing.job.site.address,
    receipt.val.firing.job.site.typingFrames)
  target := receipt.val.target
  evidence := ⟨receipt, rfl, rfl⟩

def history {source : Pattern} (receipt : ReceiptFamily plan bound type source) :
    (gslt plan bound type).RewritePath source receipt.val.target :=
  .cons (Receipt.semantic_step plan bound type receipt.property) (.nil _)

def administration {source : Pattern} (receipt : ReceiptFamily plan bound type source) : Nat :=
  receipt.val.conversions.length

theorem primitive_count {source : Pattern} (receipt : ReceiptFamily plan bound type source) :
    (history plan bound type receipt).length = 1 := rfl

theorem target_typed {source : Pattern} (receipt : ReceiptFamily plan bound type source) :
    OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound type receipt.val.target :=
  Receipt.target_sorted plan bound type receipt.property

variable (Evidence : Pattern → Type)

abbrev NativeFamily (source : Pattern) :=
  Σ receipt : ReceiptFamily plan bound type source, Evidence receipt.val.target

def introduce {source : Pattern} (receipt : ReceiptFamily plan bound type source)
    (certificate : Evidence receipt.val.target) : NativeFamily plan bound type Evidence source :=
  ⟨receipt, certificate⟩

def targetReadout : Sigma (NativeFamily plan bound type Evidence) → Sigma Evidence
  | ⟨_, receipt, certificate⟩ => ⟨receipt.val.target, certificate⟩

def receiptReadout : Sigma (NativeFamily plan bound type Evidence) → Sigma (ReceiptFamily plan bound type)
  | ⟨source, receipt, _⟩ => ⟨source, receipt⟩

theorem readout_square (point : Sigma (NativeFamily plan bound type Evidence)) :
    (targetReadout plan bound type Evidence point).1 =
      (receiptReadout plan bound type Evidence point).2.val.target := by
  cases point
  rfl

def sortedNative {source : Pattern} (receipt : ReceiptFamily plan bound type source) :
    NativeFamily plan bound type
      (fun target => PLift (OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound type target)) source :=
  ⟨receipt, ⟨target_typed plan bound type receipt⟩⟩

theorem support_projection_injective_iff :
    Function.Injective
      (Mettapedia.TypeTheory.GuardEvidenceComprehension.supportProjection
        (Evidence := NativeFamily plan bound type Evidence)) ↔
      ∀ source, Subsingleton (NativeFamily plan bound type Evidence source) :=
  Mettapedia.TypeTheory.GuardEvidenceComprehension.supportProjection_injective_iff _

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceNativeReceipts
