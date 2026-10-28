import Mettapedia.CognitiveArchitecture.Memory.MemoryRefinement
import Mathlib.Data.Finset.Basic

/-!
# Asynchronous indexing and retrieval coverage

An acknowledged write has queued intent, not necessarily a searchable value.
Successful delivery installs a still-current intent. Retrying forever does not
imply eventual success; the liveness theorem assumes a successful attempt in a
finite prefix, with no intervening edit or forget. Cancellation safety is reused
from `MemoryRefinement`.

Queue emptiness, corpus coverage, view membership and returned results are
different observations. No assertion about embedding relevance is made here.
-/

namespace Mettapedia.CognitiveArchitecture.Memory.Indexing

open MemoryRefinement

/-- A failed attempt retains the intent for another attempt. -/
def attempt (m : Memory) (i : Intent) (succeeded : Bool) : Memory :=
  if succeeded then complete m i else m

def attempts (m : Memory) (i : Intent) : List Bool → Memory
  | [] => m
  | result :: rest => attempts (attempt m i result) i rest

theorem complete_idempotent (m : Memory) (i : Intent) :
    complete (complete m i) i = complete m i := by
  unfold complete
  split <;> simp_all

theorem attempts_after_completion (m : Memory) (i : Intent) (trace : List Bool) :
    attempts (complete m i) i trace = complete m i := by
  induction trace with
  | nil => rfl
  | cons result rest ih =>
    cases result <;> simp [attempts, attempt, complete_idempotent, ih]

theorem attempts_with_success (m : Memory) (i : Intent) (trace : List Bool)
    (success : true ∈ trace) :
    attempts m i trace = complete m i := by
  induction trace generalizing m with
  | nil => simp at success
  | cons result rest ih =>
    cases result
    · exact ih m (by simpa using success)
    · exact attempts_after_completion m i rest

/-- Conditional liveness, not a guarantee that an unavailable provider recovers. -/
theorem indexed_after_success (m : Memory) (i : Intent) (trace : List Bool)
    (success : true ∈ trace) :
    (attempts (edit m i) i trace).current = some i.text ∧
      (attempts (edit m i) i trace).pending = none := by
  rw [attempts_with_success _ _ _ success]
  exact ⟨current_completion_installs_text m i, successful_edit_settles_itself m i⟩

theorem failed_prefix_preserves_intent (m : Memory) (i : Intent) (n : Nat) :
    attempts m i (List.replicate n false) = m := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, attempts, attempt] using ih

theorem queued_need_not_be_indexed :
    ∃ m : Memory, m.pending.isSome = true ∧ m.current = none :=
  ⟨⟨none, some ⟨0, "new note"⟩, []⟩, rfl, rfl⟩

/-- Forgetting can also empty a queue; emptiness alone is not delivery. -/
theorem empty_queue_need_not_mean_indexed :
    ∃ m : Memory, m.pending = none ∧ m.current = none :=
  ⟨forget ⟨none, some ⟨0, "withdrawn"⟩, []⟩, rfl, rfl⟩

structure Retrieval (Id : Type*) where
  indexed : Finset Id
  pending : Finset Id
  encountered : Finset Id
  returned : Finset Id
  returned_indexed : returned ⊆ indexed

/-- A source can have been encountered without ever having been submitted. -/
theorem empty_queue_does_not_imply_source_coverage :
    ∃ r : Retrieval Nat, r.pending = ∅ ∧ ¬ r.encountered ⊆ r.indexed := by
  refine ⟨⟨∅, ∅, {0}, ∅, by simp⟩, rfl, ?_⟩
  simp

/-- Even a sound, nonempty result set need not include every indexed item. -/
theorem indexed_item_can_be_omitted :
    ∃ r : Retrieval Nat, r.pending = ∅ ∧ 1 ∈ r.indexed ∧
      r.returned.Nonempty ∧ 1 ∉ r.returned := by
  refine ⟨⟨{0, 1}, ∅, {0, 1}, {0}, by simp⟩, ?_⟩
  simp

end Mettapedia.CognitiveArchitecture.Memory.Indexing
