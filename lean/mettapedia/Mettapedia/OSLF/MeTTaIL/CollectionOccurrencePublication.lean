import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceReadout
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesFootprint

/-! # Original rule-job readout of retained occurrence publications -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

namespace RecursiveCollectionContinuation

/-- Validation evidence for a completed branch cannot replace the allocation's
ordinary matcher trace. The original matching witness supplies that trace. -/
theorem publication_original_root (request : Request) (state : State request)
    {firing : Complete.DeepRoot.Firing} (member : firing ∈ publication request state) :
    GeneralPremise.RootFiring request.environment request.bound request.type
      request.prepared.source request.index request.prepared.ordinary.trace
      request.prepared.ordinary.assignment firing.completed firing.history firing.target := by
  obtain ⟨valid, captured⟩ := publication_sound request state member
  have sameCapture := captured.trans request.matching.assignment.symm
  cases valid with
  | @fire bound type source target index rule spec trace captured completed events
      declared specified admitted sorted matched capturedTyped premises reduced targetTyped =>
    have ruleSame : rule = request.rule := Option.some.inj (declared.symm.trans request.declared)
    have specSame : spec = request.spec := Option.some.inj (specified.symm.trans request.specified)
    cases ruleSame
    cases specSame
    exact .fire request.declared request.specified admitted request.sourceTyped
      request.matching.matching (sameCapture ▸ capturedTyped)
      (sameCapture ▸ premises) reduced targetTyped

end RecursiveCollectionContinuation

namespace CollectionOccurrenceBatch

open CollectionOccurrenceHandoff

def Publication.FinishReady (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (packet : Publication) : Prop :=
  (packet.job.preparedJob packet.prepared).Valid plan bound expected
      (packet.job.presentedSource packet.prepared) ∧
    GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan)
      packet.job.variant.site.focusBound packet.job.variant.site.focusType
      packet.prepared.source packet.job.origin.ordinal packet.prepared.ordinary.trace
      packet.prepared.ordinary.assignment packet.outcome.completed packet.outcome.history packet.outcome.target

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}

theorem Frame.publication_finish_ready (frame : Frame plan bound expected source)
    {packet : Publication} (member : packet ∈ frame.publication) :
    packet.FinishReady plan bound expected := by
  obtain ⟨outcome, published, rfl⟩ := List.mem_map.mp member
  have root := RecursiveCollectionContinuation.publication_original_root
    frame.allocation.request frame.state published
  rcases frame.allocation.request_fields with
    ⟨_, atBound, atType, _, atIndex, _, _, _⟩
  refine ⟨frame.allocation.job.prepared_valid frame.allocation.licensed frame.allocation.matching, ?_⟩
  simpa only [tag, frame.allocation.request_origin.1,
    frame.allocation.request_origin.2, atBound, atType, atIndex] using root

theorem State.publication_finish_ready (state : State plan bound expected source)
    (balanced : state.Balanced) {packet : Publication} (member : packet ∈ state.log) :
    packet.FinishReady plan bound expected := by
  obtain ⟨frame, _, published⟩ := List.mem_flatMap.mp (balanced.mem_iff.mp member)
  exact frame.publication_finish_ready published

/-- The finite free-context table need only cover declared free names.
Filling a completed local target introduces no third source of free names. -/
theorem Publication.finish_target_free_within (packet : Publication) (footprint : List String)
    (declared : Complete.Footprint.Declared plan footprint)
    (ready : packet.FinishReady plan bound expected) :
    ∀ name ∈ (packet.job.variant.site.context.fill packet.outcome.target).freeFvarNames,
      name ∈ footprint := by
  have localTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free packet.job.variant.site.focusBound packet.job.variant.site.focusType
      packet.outcome.target := by
    cases ready.2 with
    | fire _ _ _ _ _ _ _ _ typed => exact typed
  have localNames := Complete.Footprint.sorted_within declared
    (checkOpenPatternWellSorted_complete localTyped)
  have sourceNames : ∀ name ∈ (packet.job.presentedSource packet.prepared).freeFvarNames,
      name ∈ footprint := by
    intro name member
    obtain ⟨type, found⟩ :=
      ready.1.2.source_typed.freeType_of_mem_freeFvarNames_of_isObjectPattern
        ready.1.2.source_object member
    exact declared name type found
  intro name member
  rcases (GeneralEquationContexts.fill_support_sources packet.job.variant.site.context
    packet.prepared.source packet.outcome.target).2.1 name member with outside | inside
  · exact sourceNames name outside
  · exact localNames name inside

/-- Once the retained premise machine has established the local firing, the
original receipt constructor performs precisely the existing contextual lift.
The matcher trace still comes from the prepared allocation. -/
theorem Publication.finish_eq_lift (packet : Publication)
    (ready : packet.FinishReady plan bound expected) :
    packet.finish? plan bound expected =
      Complete.Step.lift plan bound expected (packet.job.preparedJob packet.prepared)
        ⟨packet.prepared.ordinary.trace, packet.prepared.ordinary.assignment,
          packet.outcome.completed, packet.outcome.history, packet.outcome.target⟩ := by
  obtain ⟨licensed, valid⟩ := ready
  have selected := GeneralRuleJobs.Job.selected_rule licensed
  have specified := GeneralRuleJobs.Job.selected_specification licensed
  cases valid with
  | @fire localBound localType localSource target index rule spec trace captured completed events
      declared specification admitted sourceTyped matching capturedTyped premises reduced targetTyped =>
    have ruleSame : rule = packet.job.origin.declaration.rule := Option.some.inj (declared.symm.trans selected)
    have specSame : spec = packet.job.origin.declaration.binding.spec :=
      Option.some.inj (specification.symm.trans specified)
    cases ruleSame
    cases specSame
    have sourceChecked := checkOpenPatternWellSorted_complete sourceTyped
    have capturesChecked := GeneralPremise.checkTypedAssignment_complete capturedTyped
    have targetChecked := checkOpenPatternWellSorted_complete targetTyped
    simp only [Publication.finish?, CollectionOccurrenceContinuation.finish?, CollectionOccurrenceHandoff.finish?,
      GeneralRuleJobs.finish?, GeneralRuleJobs.finishWith?, Complete.Step.lift,
      GeneralPlanEnvironment.environmentWith_empty, Job.preparedJob, CollectionSelection.refocus,
      GeneralRuleJobs.Job.context] at *
    simp only [admitted, sourceChecked, capturesChecked, targetChecked, reduced,
      Bool.true_and, Option.bind_eq_bind, Option.bind_some, ↓reduceIte]
    rfl

theorem Publication.finished_valid (packet : Publication)
    (ready : packet.FinishReady plan bound expected) {receipt : GeneralRuleJobs.Receipt}
    (finished : packet.finish? plan bound expected = some receipt) :
    receipt.Valid plan bound expected (packet.job.presentedSource packet.prepared) := by
  obtain ⟨licensed, valid⟩ := ready
  have selected := GeneralRuleJobs.Job.selected_rule licensed
  have specified := GeneralRuleJobs.Job.selected_specification licensed
  cases valid with
  | @fire localBound localType localSource target index rule spec trace captured completed events
      declared specification admitted sourceTyped matching capturedTyped premises reduced targetTyped =>
    have ruleSame : rule = packet.job.origin.declaration.rule := Option.some.inj (declared.symm.trans selected)
    have specSame : spec = packet.job.origin.declaration.binding.spec :=
      Option.some.inj (specification.symm.trans specified)
    cases ruleSame
    cases specSame
    exact GeneralRuleJobs.finish_sound licensed matching premises finished

end CollectionOccurrenceBatch

end Mettapedia.OSLF.MeTTaIL
