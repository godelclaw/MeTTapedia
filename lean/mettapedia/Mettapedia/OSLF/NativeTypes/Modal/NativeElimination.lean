import Mettapedia.OSLF.NativeTypes.Modal.NativeEvidence
import Mettapedia.OSLF.NativeTypes.Modal.Formation

open Mettapedia.OSLF.Framework

/-!
# Native elimination of the specified-contractum modality

Elimination reads the substituted continuation at the authored right-hand
side, while its native family remains indexed by the actual primitive target.
The equation comparison, context filling and full assignment are retained.
Both the operational step and sorted continuation readout follow from that
same response; projecting a common target never supplies a new receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeElimination

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.Modal.NativeEvidence

/-- The eliminator keeps the native receipt, even when its specified target
has a different equation representative from the primitive target. -/
structure Elimination {plan : Plan} (schema : Schema plan) (term : Pattern)
    (assignment : Assignment) (B : Continuation) where
  source : Pattern
  native : GeneralOccurrenceNativeReceipts.NativeFamily plan schema.bound schema.programCarrier
    (ContractumFamily schema assignment B) source
  filling : schema.fill? assignment term = some source
  rhs : schema.rhs? assignment = some native.2.1

def eliminate {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation} {term : Pattern}
    (implementation : Evidence schema A B term) (assignment : Assignment)
    (request : TypedRequest schema A implementation.anchor assignment) :
    Elimination schema term assignment B :=
  let response := implementation.respond assignment request
  ⟨response.source, response.native, response.filling, response.rhs⟩

/-- This is the full assignment-indexed continuation family. Its base index
includes matched variables as well as the selected rely variables. -/
def continuationReadout {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation}
    (result : Elimination schema term assignment B) :
    Σ point : Assignment × Pattern, B point.1 point.2 :=
  ⟨(assignment, result.native.2.1), result.native.2.2.2⟩

/-- M-STEP and the substituted M-ELIM are read from one retained occurrence.
The target is the specified RHS; equation conversion does not become a
second directed operational occurrence. -/
theorem elimination_contract {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation}
    (result : Elimination schema term assignment B) :
    schema.fill? assignment term = some result.source ∧
      schema.rhs? assignment = some (continuationReadout result).1.2 ∧
      (GeneralOccurrenceSemantics.gslt plan schema.bound schema.programCarrier).Step
        result.source (continuationReadout result).1.2 ∧
      HasType plan.snapshot.language plan.snapshot.free schema.bound
        (continuationReadout result).1.2 schema.programCarrier := by
  have valid := result.native.1.property
  have targetConversion := result.native.2.2.1.down
  refine ⟨result.filling, result.rhs, ?_, ?_⟩
  · exact ⟨result.native.1.val.representative, result.native.1.val.firing,
      valid.1.equivalent, valid.2, targetConversion⟩
  · have typed := GeneralOccurrenceNativeReceipts.target_typed
      plan schema.bound schema.programCarrier result.native.1
    exact (Mettapedia.OSLF.NativeTypes.Modal.Equations.conversion_sorted_iff targetConversion).mp typed |>.1

/-- The native and direct eliminators have the same specified endpoint. The
native form additionally retains the actual occurrence and conversion. -/
theorem direct_elimination_agrees {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation} {term : Pattern}
    (implementation : Evidence schema A B term) (assignment : Assignment)
    (request : TypedRequest schema A implementation.anchor assignment) :
    (continuationReadout (eliminate implementation assignment request)).1.2 =
      (m_elim implementation assignment request).1 := rfl

theorem elimination_primitive_count {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation}
    (result : Elimination schema term assignment B) :
    (GeneralOccurrenceNativeReceipts.history plan schema.bound schema.programCarrier result.native.1).length = 1 :=
  GeneralOccurrenceNativeReceipts.primitive_count plan schema.bound schema.programCarrier result.native.1

theorem elimination_preserves_origins {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation} {term : Pattern}
    (implementation : Evidence schema A B term) (assignment : Assignment)
    (request : TypedRequest schema A implementation.anchor assignment) :
    (eliminate implementation assignment request).native.1.val.firing.job =
      (implementation.respond assignment request).receipt.firing.job ∧
    (eliminate implementation assignment request).native.1.val.firing.matcherTrace =
      (implementation.respond assignment request).receipt.firing.matcherTrace ∧
    (eliminate implementation assignment request).native.1.val.firing.premiseHistory =
      (implementation.respond assignment request).receipt.firing.premiseHistory ∧
    (eliminate implementation assignment request).native.1.val.conversions =
      (implementation.respond assignment request).receipt.conversions :=
  ⟨rfl, rfl, rfl, rfl⟩

end Mettapedia.OSLF.NativeTypes.Modal.NativeElimination
