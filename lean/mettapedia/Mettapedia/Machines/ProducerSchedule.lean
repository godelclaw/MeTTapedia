import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Ordered producer notifications

Pending readers belong to the remaining current pass or the next pass. A wake
before the cursor cannot run again in the current pass. Selection serves the
least current reader before considering the next pass. The bitmap's base-64
summary selects the least nonempty bucket and then its least member.

These are independent finite-set semantics and integer-index laws. Native
phase parity, bit operations, ownership and fallible promotion have separate
implementation controls; this file does not assert a theorem about C memory.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProducerSchedule

structure Pending where
  current : Finset Nat
  later : Finset Nat
  cursor : Nat
  deriving DecidableEq

def Valid (pending : Pending) : Prop :=
  (∀ rank ∈ pending.current, pending.cursor ≤ rank) ∧
  (∀ rank ∈ pending.later, rank < pending.cursor)

def wake (pending : Pending) (rank : Nat) : Pending :=
  if rank < pending.cursor then
    {pending with later := insert rank pending.later}
  else {pending with current := insert rank pending.current}

def initial : Pending := ⟨∅, ∅, 0⟩

theorem initial_valid : Valid initial := by simp [Valid, initial]

theorem wake_valid (pending : Pending) (rank : Nat) (valid : Valid pending) :
    Valid (wake pending rank) := by
  rcases valid with ⟨current, later⟩
  by_cases visited : rank < pending.cursor
  · simp only [wake, if_pos visited, Valid]
    refine ⟨current, ?_⟩
    intro other included
    rcases Finset.mem_insert.mp included with rfl | included
    · exact visited
    · exact later other included
  · simp only [wake, if_neg visited, Valid]
    refine ⟨?_, later⟩
    intro other included
    rcases Finset.mem_insert.mp included with rfl | included
    · omega
    · exact current other included

theorem wake_coalesces (pending : Pending) (rank : Nat) :
    wake (wake pending rank) rank = wake pending rank := by
  by_cases visited : rank < pending.cursor <;> simp [wake, visited]

theorem visited_reader_waits (pending : Pending) (rank : Nat)
    (visited : rank < pending.cursor) :
    (wake pending rank).current = pending.current ∧
      rank ∈ (wake pending rank).later := by simp [wake, visited]

theorem unvisited_reader_runs_current (pending : Pending) (rank : Nat)
    (ahead : pending.cursor ≤ rank) :
    rank ∈ (wake pending rank).current ∧
      (wake pending rank).later = pending.later := by
  simp [wake, Nat.not_lt.mpr ahead]

/-- The semantic cursor transition after selecting a current reader. -/
def removeCurrent (pending : Pending) (rank : Nat) : Pending :=
  {pending with current := pending.current.erase rank, cursor := rank + 1}

theorem remove_least_valid (pending : Pending) (nonempty : pending.current.Nonempty)
    (valid : Valid pending) :
    Valid (removeCurrent pending (pending.current.min' nonempty)) := by
  rcases valid with ⟨current, later⟩
  refine ⟨?_, ?_⟩
  · intro rank included
    rcases Finset.mem_erase.mp included with ⟨different, included⟩
    have least := Finset.min'_le pending.current rank included
    simp only [removeCurrent] at *
    omega
  · intro rank included
    have before := later rank included
    have cursor := current _ (Finset.min'_mem pending.current nonempty)
    simp only [removeCurrent] at *
    omega

def advance (pending : Pending) : Pending := ⟨pending.later, ∅, 0⟩

theorem advance_valid (pending : Pending) : Valid (advance pending) := by
  simp [Valid, advance]

def pendingRanks (pending : Pending) : Finset Nat := pending.current ∪ pending.later

theorem remove_current_preserves_other_wakes (pending : Pending) (rank : Nat)
    (notLater : rank ∉ pending.later) :
    pendingRanks (removeCurrent pending rank) = (pendingRanks pending).erase rank := by
  ext other
  simp [pendingRanks, removeCurrent]
  by_cases same : other = rank
  · subst other
    simp [notLater]
  · simp [same]

theorem advance_preserves_pending (pending : Pending) (finished : pending.current = ∅) :
    pendingRanks (advance pending) = pendingRanks pending := by
  simp [pendingRanks, advance, finished]

/-- One step of the native base-64 summary hierarchy. -/
def buckets (keys : Finset Nat) : Finset Nat := keys.image (· / 64)

def selectedBucket (keys : Finset Nat) (nonempty : keys.Nonempty) : Nat :=
  (buckets keys).min' (nonempty.image (· / 64))

def bucketKeys (keys : Finset Nat) (bucket : Nat) : Finset Nat :=
  keys.filter (fun key => key / 64 = bucket)

theorem selected_bucket_nonempty (keys : Finset Nat) (nonempty : keys.Nonempty) :
    (bucketKeys keys (selectedBucket keys nonempty)).Nonempty := by
  have member := Finset.min'_mem (buckets keys) (nonempty.image (· / 64))
  obtain ⟨key, included, equality⟩ := Finset.mem_image.mp member
  exact ⟨key, Finset.mem_filter.mpr ⟨included, equality⟩⟩

def selectedKey (keys : Finset Nat) (nonempty : keys.Nonempty) : Nat :=
  (bucketKeys keys (selectedBucket keys nonempty)).min'
    (selected_bucket_nonempty keys nonempty)

theorem summary_selects_global_minimum (keys : Finset Nat) (nonempty : keys.Nonempty) :
    selectedKey keys nonempty = keys.min' nonempty := by
  have member := Finset.min'_mem (bucketKeys keys (selectedBucket keys nonempty))
    (selected_bucket_nonempty keys nonempty)
  have selected := Finset.mem_filter.mp member
  symm
  apply (Finset.min'_eq_iff keys nonempty (selectedKey keys nonempty)).mpr
  refine ⟨selected.1, ?_⟩
  intro other included
  have bucketLeast := Finset.min'_le (buckets keys) (other / 64)
    (Finset.mem_image.mpr ⟨other, included, rfl⟩)
  by_cases same : other / 64 = selectedBucket keys nonempty
  · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨included, same⟩)
  · have division : selectedKey keys nonempty / 64 = selectedBucket keys nonempty := selected.2
    change selectedBucket keys nonempty ≤ other / 64 at bucketLeast
    omega

theorem bucket_selection_reconstructs_rank (keys : Finset Nat) (nonempty : keys.Nonempty) :
    selectedKey keys nonempty =
      64 * selectedBucket keys nonempty + selectedKey keys nonempty % 64 := by
  have member := Finset.mem_filter.mp
    (Finset.min'_mem (bucketKeys keys (selectedBucket keys nonempty))
      (selected_bucket_nonempty keys nonempty))
  have decomposition := Nat.mod_add_div (selectedKey keys nonempty) 64
  have division : selectedKey keys nonempty / 64 = selectedBucket keys nonempty := member.2
  omega

theorem selected_bit_is_least (keys : Finset Nat) (nonempty : keys.Nonempty) :
    selectedKey keys nonempty % 64 =
      ((bucketKeys keys (selectedBucket keys nonempty)).image (· % 64)).min'
        ((selected_bucket_nonempty keys nonempty).image (· % 64)) := by
  have selected := Finset.mem_filter.mp
    (Finset.min'_mem (bucketKeys keys (selectedBucket keys nonempty))
      (selected_bucket_nonempty keys nonempty))
  symm
  apply (Finset.min'_eq_iff _ _ _).mpr
  refine ⟨Finset.mem_image.mpr ⟨_, Finset.min'_mem _ _, rfl⟩, ?_⟩
  intro bit included
  obtain ⟨key, member, rfl⟩ := Finset.mem_image.mp included
  have keyBucket := (Finset.mem_filter.mp member).2
  have least := Finset.min'_le (bucketKeys keys (selectedBucket keys nonempty)) key member
  have division : selectedKey keys nonempty / 64 = selectedBucket keys nonempty := selected.2
  change selectedKey keys nonempty ≤ key at least
  omega

theorem bucket_member_nonempty (keys : Finset Nat) (bucket : Nat)
    (member : bucket ∈ buckets keys) : (bucketKeys keys bucket).Nonempty := by
  obtain ⟨key, included, equality⟩ := Finset.mem_image.mp member
  exact ⟨key, Finset.mem_filter.mpr ⟨included, equality⟩⟩

/-- Summary selection recurses on bucket identifiers; descent then selects a
member of that bucket. This differs from searching the original key set. -/
def descend : (height : Nat) → (keys : Finset Nat) → keys.Nonempty →
    {rank : Nat // rank ∈ keys}
  | 0, keys, nonempty => ⟨keys.min' nonempty, Finset.min'_mem keys nonempty⟩
  | height + 1, keys, nonempty =>
      let upper := descend height (buckets keys) (nonempty.image (· / 64))
      let members := bucketKeys keys upper.val
      let occupied := bucket_member_nonempty keys upper.val upper.property
      ⟨members.min' occupied, (Finset.mem_filter.mp (Finset.min'_mem members occupied)).1⟩

theorem hierarchy_selects_global_minimum (height : Nat) (keys : Finset Nat)
    (nonempty : keys.Nonempty) : (descend height keys nonempty).val = keys.min' nonempty := by
  induction height generalizing keys with
  | zero => rfl
  | succ height ih =>
      have upper := ih (buckets keys) (nonempty.image (· / 64))
      simpa only [descend, upper, selectedBucket, selectedKey] using
        summary_selects_global_minimum keys nonempty

theorem summary_bucket_bound (keys : Finset Nat) (limit : Nat)
    (bounded : ∀ key ∈ keys, key < 64 * limit) :
    ∀ bucket ∈ buckets keys, bucket < limit := by
  intro bucket member
  obtain ⟨key, included, rfl⟩ := Finset.mem_image.mp member
  have bound := bounded key included
  omega

/-- Moving a visited reader into the current pass changes the admitted order. -/
theorem premature_wake_breaks_cursor :
    ¬ Valid {current := {1}, later := ∅, cursor := 2} := by
  simp [Valid]

end Mettapedia.Machines.ProducerSchedule
