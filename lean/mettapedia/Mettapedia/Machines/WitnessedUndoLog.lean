import Mettapedia.Machines.MarkedUndoLog
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Validated positions for online undo-log coalescing

A cached position is only a hint. The current log must contain that slot at
the proposed position, after the latest rollback boundary. This validation
remains meaningful after truncation, compaction and position reuse.

The payload is the complete old slot value. Rollback observes neither the
number of overwritten intermediate values nor their order within one slot.
The online rule preserves every boundary at or before the current floor.
Saving another boundary advances the floor before subsequent writes.

The entry lower bound is for complete-payload journals preserving rollback
for every current store. It does not bound compressed journals, persistent
stacks, native instructions, allocation capacity or whole-runtime space.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.WitnessedUndoLog

open MarkedUndoLog

universe u v
variable {Slot : Type u} {Payload : Type v} [DecidableEq Slot]

theorem rollback_absent (log : List (Slot × Payload)) (slot : Slot)
    (absent : slot ∉ log.map Prod.fst) (store : Slot → Payload) :
    rollback log store slot = store slot := by
  induction log with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simpa [rollback, restore, absent.1] using ih absent.2

theorem rollback_present (log : List (Slot × Payload)) (slot : Slot)
    (present : slot ∈ log.map Prod.fst) :
    ∃ old, ∀ store : Slot → Payload, rollback log store slot = old := by
  induction log with
  | nil => simp at present
  | cons entry rest ih =>
      by_cases same : slot = entry.1
      · exact ⟨entry.2, fun _ => by simp [rollback, restore, same]⟩
      · have inRest : slot ∈ rest.map Prod.fst := by simpa [same] using present
        obtain ⟨old, value⟩ := ih inRest
        exact ⟨old, fun store => by simpa [rollback, restore, same] using value store⟩

/-- A first saved value already determines rollback at this slot. -/
theorem rollback_append_duplicate (log : List (Slot × Payload)) (slot : Slot)
    (old : Payload) (present : slot ∈ log.map Prod.fst) (store : Slot → Payload) :
    rollback (log ++ [(slot, old)]) store = rollback log store := by
  rw [rollback_append]
  funext observed
  by_cases same : observed = slot
  · subst observed
    obtain ⟨value, fixed⟩ := rollback_present log slot present
    exact (fixed _).trans (fixed _).symm
  · apply rollback_congr_at
    simp [rollback, restore, same]

/-- A position before the floor, outside the log, or naming another slot
cannot justify omission of a new complete payload. -/
def witness (log : List (Slot × Payload)) (floor position : Nat) (slot : Slot) : Bool :=
  if floor ≤ position then
    match log[position]? with
    | none => false
    | some entry => decide (entry.1 = slot)
  else false

theorem witness_sound (log : List (Slot × Payload)) (floor position : Nat) (slot : Slot)
    (valid : witness log floor position slot = true) :
    floor ≤ position ∧ position < log.length ∧ slot ∈ (log.drop floor).map Prod.fst := by
  by_cases after : floor ≤ position
  · cases found : log[position]? with
    | none => simp [witness, after, found] at valid
    | some entry =>
        have same : entry.1 = slot := by simpa [witness, after, found] using valid
        have bound := (List.getElem?_eq_some_iff.mp found).1
        refine ⟨after, bound, List.mem_map.mpr ⟨entry, ?_, same⟩⟩
        apply List.mem_iff_getElem?.mpr
        refine ⟨position - floor, ?_⟩
        simpa [List.getElem?_drop, Nat.add_sub_of_le after] using found
  · simp [witness, after] at valid

theorem witness_older_floor (log : List (Slot × Payload)) (floor position mark : Nat)
    (slot : Slot) (older : mark ≤ floor) (valid : witness log floor position slot = true) :
    witness log mark position slot = true := by
  have after := (witness_sound log floor position slot valid).1
  have afterMark := older.trans after
  simpa [witness, after, afterMark] using valid

/-- Appending other slot histories cannot invalidate an existing witness
inside the same interval. No payload equality or cache authority is used. -/
theorem witness_append (log later : List (Slot × Payload)) (floor position : Nat)
    (slot : Slot) (valid : witness log floor position slot = true) :
    witness (log ++ later) floor position slot = true := by
  have bound := (witness_sound log floor position slot valid).2.1
  simpa [witness, List.getElem?_append_left bound] using valid

/-- The newly appended complete payload supplies its own validated cache
position. Future writes of this slot in the interval need no second copy. -/
theorem appended_witness (log : List (Slot × Payload)) (floor : Nat)
    (entry : Slot × Payload) (bound : floor ≤ log.length) :
    witness (log ++ [entry]) floor log.length entry.1 = true := by
  simp [witness, bound]

/-- The cache never supplies the payload or the rollback result: it supplies
an actual interval-local entry whose earlier restoration wins. -/
theorem rollbackAt_append_duplicate (log : List (Slot × Payload))
    (floor position mark : Nat) (slot : Slot) (old : Payload) (store : Slot → Payload)
    (older : mark ≤ floor) (valid : witness log floor position slot = true) :
    rollbackAt (log ++ [(slot, old)]) mark store = rollbackAt log mark store := by
  have validMark := witness_older_floor log floor position mark slot older valid
  obtain ⟨after, bound, present⟩ := witness_sound log mark position slot validMark
  have markBound : mark ≤ log.length := by omega
  simp only [rollbackAt, List.drop_append_of_le_length markBound]
  exact rollback_append_duplicate _ slot old present store

def record (log : List (Slot × Payload)) (floor position : Nat) (entry : Slot × Payload) :
    List (Slot × Payload) :=
  if witness log floor position entry.1 then log else log ++ [entry]

/-- One online write agrees with unconditional logging at every still-live
mark. A false cache hint only costs an extra authoritative log entry. -/
theorem record_preserves_mark (log : List (Slot × Payload)) (floor position mark : Nat)
    (entry : Slot × Payload) (store : Slot → Payload) (older : mark ≤ floor) :
    rollbackAt (record log floor position entry) mark store =
      rollbackAt (log ++ [entry]) mark store := by
  by_cases valid : witness log floor position entry.1 = true
  · simp only [record, valid, ↓reduceIte]
    exact (rollbackAt_append_duplicate log floor position mark entry.1 entry.2 store
      older valid).symm
  · simp [record, valid]

/-- Ordinary alternatives and temporary rollback clients use the same
contract, provided their marks are all fenced by the current write floor. -/
theorem record_preserves_frontier (log : List (Slot × Payload)) (floor position : Nat)
    (entry : Slot × Payload) (marks : List Nat) (store : Slot → Payload)
    (fenced : ∀ mark ∈ marks, mark ≤ floor) :
    marks.map (fun mark => rollbackAt (record log floor position entry) mark store) =
      marks.map (fun mark => rollbackAt (log ++ [entry]) mark store) := by
  apply List.map_congr_left
  intro mark present
  exact record_preserves_mark log floor position mark entry store (fenced mark present)

theorem record_length_le (log : List (Slot × Payload)) (floor position : Nat)
    (entry : Slot × Payload) :
    (record log floor position entry).length ≤ log.length + 1 := by
  unfold record
  split <;> simp

/-- After capturing a new mark, every existing entry lies before the floor. -/
theorem new_checkpoint_requires_save (log : List (Slot × Payload)) (position : Nat)
    (entry : Slot × Payload) :
    record log log.length position entry = log ++ [entry] := by
  by_cases valid : witness log log.length position entry.1 = true
  · obtain ⟨after, bound, _⟩ := witness_sound log log.length position entry.1 valid
    omega
  · simp [record, valid]

/-- Every slot that a journal can restore independently of the current store
must occur in any equivalent complete-payload journal. -/
theorem equivalent_support [Nontrivial Payload]
    (reference candidate : List (Slot × Payload))
    (equivalent : ∀ store, rollback candidate store = rollback reference store) :
    (reference.map Prod.fst).toFinset ⊆ (candidate.map Prod.fst).toFinset := by
  intro slot member
  have present : slot ∈ reference.map Prod.fst := by simpa using member
  by_contra missing
  have absent : slot ∉ candidate.map Prod.fst := by simpa using missing
  obtain ⟨old, fixed⟩ := rollback_present reference slot present
  obtain ⟨different, notOld⟩ := exists_ne old
  have same := congrFun (equivalent (fun _ => different)) slot
  rw [rollback_absent candidate slot absent, fixed] at same
  exact notOld same

/-- One saved complete payload per distinct slot is entry-minimal for one
interval under the stated all-store rollback observer. -/
theorem coalesce_entry_minimal [Nontrivial Payload]
    (reference candidate : List (Slot × Payload))
    (equivalent : ∀ store, rollback candidate store = rollback reference store) :
    (coalesce reference).length ≤ candidate.length := by
  have distinct : ((coalesce reference).map Prod.fst).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact coalesceFrom_distinct_slots reference []
  have same : ∀ store, rollback candidate store = rollback (coalesce reference) store :=
    fun store => (equivalent store).trans (rollback_coalesce reference store).symm
  have included := equivalent_support (coalesce reference) candidate same
  calc
    (coalesce reference).length =
        ((coalesce reference).map Prod.fst).toFinset.card := by
      simpa using (List.toFinset_card_of_nodup distinct).symm
    _ ≤ (candidate.map Prod.fst).toFinset.card := Finset.card_le_card included
    _ ≤ candidate.length := by simpa using (candidate.map Prod.fst).toFinset_card_le

example : record ([(0, 4), (1, 7)] : List (Nat × Nat)) 0 0 (0, 9) =
    [(0, 4), (1, 7)] := by decide

/-- The same valid position is too old for an intervening checkpoint. -/
example : record ([(0, 4), (1, 7)] : List (Nat × Nat)) 1 0 (0, 9) =
    [(0, 4), (1, 7), (0, 9)] := by decide

/-- Position reuse for a different slot is a miss, even inside the interval. -/
example : witness ([(1, 4)] : List (Nat × Nat)) 0 0 0 = false ∧
    witness ([(0, 4)] : List (Nat × Nat)) 0 1 0 = false := by decide

end Mettapedia.Machines.WitnessedUndoLog
