import Mettapedia.Machines.SourceSchedulingBoundary
import Mettapedia.Machines.Cursor.ProducerOccurrenceLog

/-!
# Scheduling obligations and occurrence receipts

For one consumer, a consumption cites its production. A checked occurrence
receipt also requires each event identity to be fresh. Thus causal order and
at-most-once use are separate consequences, while both batching and
interleaving remain possible.

For multiple consumers, a use is identified by both consumer and row. Erasing
the consumer can identify two legitimate deliveries; global at-most-once use
of a row would be a stronger and generally incorrect obligation. These laws
describe the projected model, not every native effect or scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceSchedulingReceipt

open SourceSchedulingBoundary
open Cursor.ProducerOccurrenceLog

def annotate : OccurrenceEvent → CausalEvent OccurrenceEvent
  | .produced id => ⟨.produced id, []⟩
  | .consumed id => ⟨.consumed id, [.produced id]⟩

@[simp] theorem annotate_event (event : OccurrenceEvent) : (annotate event).event = event := by
  cases event <;> rfl

theorem annotate_events (trace : List OccurrenceEvent) :
    (trace.map annotate).map CausalEvent.event = trace := by
  simp [List.map_map, Function.comp_def]

/-- A checked receipt entails production before consumption for every
observed occurrence. It does not choose an order between independent rows. -/
theorem ordered_implies_causal (trace : List OccurrenceEvent)
    (ordered : CausalReceipt.Ordered [] (trace.map annotate)) :
    productionBeforeConsumption trace := by
  intro event present
  cases event with
  | produced _ => trivial
  | consumed id =>
      have recorded : annotate (.consumed id) ∈ trace.map annotate :=
        List.mem_map.mpr ⟨.consumed id, present, rfl⟩
      have rank := CausalReceipt.ordered_rank [] (trace.map annotate) ordered
        (annotate (.consumed id)) recorded (.produced id) (by simp [annotate])
      simp only [List.nil_append] at rank
      rw [annotate_events] at rank
      simpa [annotate] using rank

/-- Fresh occurrence identities prohibit replay within the one-consumer
projection, independently of the causal-edge obligation. -/
theorem ordered_implies_no_replay (trace : List OccurrenceEvent)
    (ordered : CausalReceipt.Ordered [] (trace.map annotate)) : trace.Nodup := by
  have unique := CausalReceipt.ordered_distinct [] (trace.map annotate) List.nodup_nil ordered
  simp only [List.nil_append] at unique
  rw [annotate_events] at unique
  exact unique

/-- An interrupted prefix retains both obligations; the suffix is not
required to have run before the prefix can be observed. -/
theorem ordered_prefix (earlier later : List OccurrenceEvent)
    (ordered : CausalReceipt.Ordered [] ((earlier ++ later).map annotate)) :
    productionBeforeConsumption earlier ∧ earlier.Nodup := by
  have split := (CausalReceipt.ordered_append [] (earlier.map annotate) (later.map annotate)).mp
    (by simpa only [List.map_append] using ordered)
  exact ⟨ordered_implies_causal earlier split.1, ordered_implies_no_replay earlier split.1⟩

namespace Controls

theorem interleaved_is_ordered :
    CausalReceipt.Ordered []
      ([.produced 1, .consumed 1, .produced 2, .consumed 2].map annotate) := by
  simp [annotate, CausalReceipt.Ordered]

theorem batched_is_ordered :
    CausalReceipt.Ordered []
      ([.produced 1, .produced 2, .consumed 1, .consumed 2].map annotate) := by
  simp [annotate, CausalReceipt.Ordered]

/-- Causality alone does not rule out consuming the same occurrence twice. -/
theorem causal_alone_allows_replay :
    productionBeforeConsumption [.produced 1, .consumed 1, .consumed 1] ∧
      ¬ CausalReceipt.Ordered []
        ([.produced 1, .consumed 1, .consumed 1].map annotate) := by
  simp [productionBeforeConsumption, List.idxOf_cons, annotate, CausalReceipt.Ordered]

def eraseClient {clients : Nat} : HistoryOccurrence clients → OccurrenceEvent
  | .admission position => .produced position
  | .delivery _ position => .consumed position

/-- Distinct consumers may each receive the same row. Erasing their identity
collapses those two valid uses, so this is not the one-consumer replay case. -/
theorem separate_consumers_are_distinct_uses :
    CausalReceipt.WellFormed []
        (sharedAdmissionReceipt (0 : Fin 2) (1 : Fin 2) 7) ∧
      deliveryOccurrence (0 : Fin 2) 7 ≠ deliveryOccurrence (1 : Fin 2) 7 ∧
      eraseClient (deliveryOccurrence (0 : Fin 2) 7) =
        eraseClient (deliveryOccurrence (1 : Fin 2) 7) := by
  refine ⟨shared_row_receipt_wellFormed (0 : Fin 2) (1 : Fin 2) 7 (by decide), ?_, rfl⟩
  decide +kernel

end Controls
end Mettapedia.Machines.SourceSchedulingReceipt
