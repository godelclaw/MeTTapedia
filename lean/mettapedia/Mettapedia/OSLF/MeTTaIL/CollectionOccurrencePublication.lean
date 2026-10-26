import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceReadout
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

namespace RecursiveCollectionContinuation.Canonical

/-- The actual allocation seed, rather than an outcome's validation trace,
licenses the same published completion and full premise history. -/
theorem publication_original_root (request : Request) (state : State request)
    (seed : Seed request)
    {firing : Firing} (member : firing ∈ publication request state) :
    GeneralPremise.Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      request.environment request.bound request.type request.prepared.source request.index
      request.answer.trace request.answer.assignment firing.completed firing.history firing.target := by
  obtain ⟨valid, captured⟩ := publication_sound request state member
  cases valid with
  | @fire bound type source target index rule spec trace captured completed events
      declared specified admitted sorted matched capturedTyped premises reduced targetTyped =>
    have ruleSame : rule = request.rule := Option.some.inj (declared.symm.trans request.declared)
    have specSame : spec = request.spec := Option.some.inj (specified.symm.trans request.specified)
    cases ruleSame
    cases specSame
    exact .fire request.declared request.specified admitted request.sourceTyped seed
      (captured ▸ capturedTyped) (captured ▸ premises) reduced targetTyped

end RecursiveCollectionContinuation.Canonical

namespace CollectionOccurrenceBatch

open CollectionOccurrenceHandoff

def Publication.FinishReadyIn {Choice : Type}
    (meaning : GeneralPremise.MatchingInterpretation Choice) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (trace : List Choice)
    (captured : ScopedRuleMatching.Assignment) (packet : Publication Choice) : Prop :=
  (packet.job.preparedJob packet.prepared).Valid plan bound expected
      (packet.job.presentedSource packet.prepared) ∧
    GeneralPremise.Interpreted.RootFiring meaning (GeneralPlanEnvironment.environment plan)
      packet.job.variant.site.focusBound packet.job.variant.site.focusType
      packet.prepared.source packet.job.origin.ordinal trace captured
      packet.outcome.completed packet.outcome.history packet.outcome.target

def Publication.FinishReady (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (packet : Publication) : Prop :=
  packet.FinishReadyIn GeneralPremise.ordinaryInterpretation plan bound expected
    packet.prepared.ordinary.trace packet.prepared.ordinary.assignment

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}

theorem Frame.publication_finish_ready (frame : Frame plan bound expected source)
    {packet : Publication} (member : packet ∈ frame.publication) :
    packet.FinishReady plan bound expected := by
  rw [Frame.publication_ordinary] at member
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

theorem Frame.publication_canonical_finish_ready
    (frame : Frame plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    {packet : Publication EquationalScopedReceipts.Event} (member : packet ∈ frame.publication) :
    packet.FinishReadyIn RecursiveCollectionHandoff.canonicalMatchingInterpretation plan bound expected
      packet.answer.trace packet.answer.assignment := by
  rw [Frame.canonical_publication] at member
  obtain ⟨outcome, published, rfl⟩ := List.mem_map.mp member
  have root := RecursiveCollectionContinuation.Canonical.publication_original_root
    frame.allocation.request frame.state frame.allocation.canonical_seed published
  rcases frame.allocation.request_fields with
    ⟨_, atBound, atType, _, atIndex, _, _, atAnswer⟩
  refine ⟨frame.allocation.job.prepared_valid frame.allocation.licensed frame.allocation.matching, ?_⟩
  simpa only [tag, frame.allocation.request_origin.1,
    frame.allocation.request_origin.2, atBound, atType, atIndex, atAnswer] using root

theorem State.publication_canonical_finish_ready
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    (balanced : state.Balanced) {packet : Publication EquationalScopedReceipts.Event}
    (member : packet ∈ state.log) :
    packet.FinishReadyIn RecursiveCollectionHandoff.canonicalMatchingInterpretation plan bound expected
      packet.answer.trace packet.answer.assignment := by
  obtain ⟨frame, _, published⟩ := List.mem_flatMap.mp (balanced.mem_iff.mp member)
  exact frame.publication_canonical_finish_ready published

/-- The finite free-context table need only cover declared free names.
Filling a completed local target introduces no third source of free names. -/
theorem Publication.finish_target_free_within_in {Choice : Type}
    (meaning : GeneralPremise.MatchingInterpretation Choice) (trace : List Choice)
    (captured : ScopedRuleMatching.Assignment) (packet : Publication Choice) (footprint : List String)
    (declared : Complete.Footprint.Declared plan footprint)
    (ready : packet.FinishReadyIn meaning plan bound expected trace captured) :
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

theorem Publication.finish_target_free_within (packet : Publication) (footprint : List String)
    (declared : Complete.Footprint.Declared plan footprint)
    (ready : packet.FinishReady plan bound expected) :
    ∀ name ∈ (packet.job.variant.site.context.fill packet.outcome.target).freeFvarNames,
      name ∈ footprint :=
  packet.finish_target_free_within_in GeneralPremise.ordinaryInterpretation
    packet.prepared.ordinary.trace packet.prepared.ordinary.assignment footprint declared ready

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

theorem Publication.finished_valid_in {Choice : Type}
    (meaning : GeneralPremise.MatchingInterpretation Choice) (trace : List Choice)
    (captured : ScopedRuleMatching.Assignment) (packet : Publication Choice)
    (ready : packet.FinishReadyIn meaning plan bound expected trace captured)
    {receipt : GeneralRuleJobs.Receipt Choice}
    (finished : GeneralRuleJobs.finish? plan bound expected (packet.job.preparedJob packet.prepared)
      trace captured packet.outcome.completed packet.outcome.history = some receipt) :
    receipt.ValidInWith meaning GeneralPremise.DynamicProvider.empty plan bound expected
      (packet.job.presentedSource packet.prepared) :=
  GeneralRuleJobs.finishWith_interpreted_root_sound ready.1 ready.2 finished

theorem Publication.finished_valid (packet : Publication)
    (ready : packet.FinishReady plan bound expected) {receipt : GeneralRuleJobs.Receipt}
    (finished : packet.finish? plan bound expected = some receipt) :
    receipt.Valid plan bound expected (packet.job.presentedSource packet.prepared) :=
  packet.finished_valid_in GeneralPremise.ordinaryInterpretation
    packet.prepared.ordinary.trace packet.prepared.ordinary.assignment ready finished

#print axioms RecursiveCollectionContinuation.Canonical.publication_original_root
#print axioms Frame.publication_canonical_finish_ready
#print axioms State.publication_canonical_finish_ready
#print axioms Publication.finish_target_free_within_in
#print axioms Publication.finished_valid_in

end CollectionOccurrenceBatch

end Mettapedia.OSLF.MeTTaIL

/-! Prefix observations retain their complete committed packets.
These readouts make no enumeration-completion assertion. -/

namespace Mettapedia.OSLF.MeTTaIL.CollectionCommittedObservation

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CanonicalBags
open CollectionOccurrenceBatch GeneralPremise

theorem frame_receipt_valid {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (frame : Frame plan bound expected source)
    {packet : Publication} (published : packet ∈ frame.publication)
    {receipt : GeneralRuleJobs.Receipt} (finished : packet.finish? plan bound expected = some receipt) :
    receipt.Valid plan bound expected (packet.job.presentedSource packet.prepared) :=
  packet.finished_valid (frame.publication_finish_ready published) finished

theorem retained_receipt_valid {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {state : State plan bound expected source}
    (balanced : state.Balanced) {committed : Committed}
    (published : committed ∈ retained plan bound expected state.log) :
    committed.2.Valid plan bound expected (committed.1.job.presentedSource committed.1.prepared) := by
  obtain ⟨packet, logged, made⟩ := List.mem_filterMap.mp published
  unfold commit? at made
  cases finished : packet.finish? plan bound expected with
  | none => simp only [finished, Option.map_none] at made; cases made
  | some receipt =>
      simp only [finished, Option.map_some, Option.some.injEq] at made
      cases made
      obtain ⟨frame, _, member⟩ := List.mem_flatMap.mp (balanced.subset logged)
      exact frame_receipt_valid frame member finished

end Mettapedia.OSLF.MeTTaIL.CollectionCommittedObservation
