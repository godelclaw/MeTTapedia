import Mettapedia.OSLF.NativeTypes.Modal.Equations
import Mettapedia.GSLT.Core.InteractionEvent

open Mettapedia.OSLF.Framework

/-!
# Generated modal evidence as native occurrence families

The native target is the actual primitive receipt's target. The specified
contractum remains beside it with the equation comparison and dependent
continuation certificate. An event's origin and ordered premise history are
not replaced by either target readout.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.NativeTypes.Modal.Rules

def _root_.Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome.nativeReceipt {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation}
    (outcome : Outcome schema term assignment B) :
    GeneralOccurrenceNativeReceipts.ReceiptFamily plan schema.bound schema.programCarrier outcome.source :=
  ⟨outcome.receipt, outcome.valid⟩

/-- Existing native comprehension is over actual targets. Its certificate
retains the chosen contractum and the full dependent continuation family. -/
def ContractumFamily {plan : Plan} (schema : Schema plan) (assignment : Assignment)
    (B : Continuation) (actualTarget : Pattern) : Type :=
  Σ specifiedTarget : Pattern,
    PLift (Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan schema.bound schema.programCarrier)
      actualTarget specifiedTarget) × substituteContinuation B assignment specifiedTarget

def _root_.Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome.native {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation}
    (outcome : Outcome schema term assignment B) :
    GeneralOccurrenceNativeReceipts.NativeFamily plan schema.bound schema.programCarrier
      (ContractumFamily schema assignment B) outcome.source :=
  ⟨outcome.nativeReceipt, outcome.target, ⟨outcome.targetConversion⟩, outcome.certificate⟩

/-- The event uses the selected authored index, actual typed occurrence and
actual target from the independent receipt family. -/
def _root_.Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome.event {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation}
    (outcome : Outcome schema term assignment B) :
    (GeneralOccurrenceNativeReceipts.interaction plan schema.bound schema.programCarrier).Enabled outcome.source :=
  GeneralOccurrenceNativeReceipts.asInteraction plan schema.bound schema.programCarrier outcome.nativeReceipt

def _root_.Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome.history {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation}
    (outcome : Outcome schema term assignment B) :
    (GeneralOccurrenceSemantics.gslt plan schema.bound schema.programCarrier).RewritePath
      outcome.source outcome.receipt.target :=
  GeneralOccurrenceNativeReceipts.history plan schema.bound schema.programCarrier outcome.nativeReceipt

theorem primitive_history_count {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation}
    (outcome : Outcome schema term assignment B) : outcome.history.length = 1 :=
  GeneralOccurrenceNativeReceipts.primitive_count plan schema.bound schema.programCarrier outcome.nativeReceipt

theorem native_elimination_target {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation}
    (outcome : Outcome schema term assignment B) :
    schema.rhs? assignment = some outcome.native.2.1 := outcome.rhs

theorem native_actual_target_comparison {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation}
    (outcome : Outcome schema term assignment B) :
    Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan schema.bound schema.programCarrier)
      outcome.event.target outcome.native.2.1 := outcome.targetConversion

theorem native_ordered_origins {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation}
    (outcome : Outcome schema term assignment B) :
    outcome.native.1.val.firing.premiseHistory = outcome.receipt.firing.premiseHistory ∧
      outcome.event.site.1 = outcome.receipt.firing.job.declaration.declarationIndex ∧
      outcome.event.site.2.1 = outcome.receipt.firing.job.site.address ∧
      outcome.event.site.2.2 = outcome.receipt.firing.job.site.typingFrames :=
  ⟨rfl, rfl, rfl, rfl⟩

end Mettapedia.OSLF.NativeTypes.Modal.NativeEvidence
