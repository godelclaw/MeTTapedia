import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Base-64 producer bitmap layout

A leaf word holds 64 ranks. Each summary word holds 64 child-word indicators.
The layout stops after the root word; two pass bitmaps use the same offsets.
A single pending rank needs no bitmap payload. The native implementation keeps
an allocated layout for reuse even when its frontier returns to a single rank.

The laws bound initialized words and summary height, including padding. They
account for the layout rather than a host allocator's metadata or page size.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProducerBitmapLayout

def wordsFor (ranks : Nat) : Nat := (ranks + 63) / 64

theorem wordsFor_covers (ranks : Nat) : ranks ≤ 64 * wordsFor ranks := by
  unfold wordsFor
  omega

theorem wordsFor_padding (ranks : Nat) : 64 * wordsFor ranks ≤ ranks + 63 := by
  unfold wordsFor
  omega

theorem wordsFor_positive (ranks : Nat) (positive : 0 < ranks) : 0 < wordsFor ranks := by
  unfold wordsFor
  omega

/-- Fuel is the admitted maximum summary height, not an answer limit. -/
def counts : Nat → Nat → List Nat
  | 0, _ => []
  | height + 1, ranks =>
      if ranks = 0 then [] else
        let words := wordsFor ranks
        words :: if words = 1 then [] else counts height words

theorem counts_length (height ranks : Nat) : (counts height ranks).length ≤ height := by
  induction height generalizing ranks with
  | zero => simp [counts]
  | succ height ih =>
      by_cases empty : ranks = 0
      · simp [counts, empty]
      · by_cases root : wordsFor ranks = 1
        · simp [counts, empty, root]
        · simpa [counts, empty, root] using Nat.succ_le_succ (ih (wordsFor ranks))

/-- All levels, both pass bitmaps and alignment padding are charged. -/
theorem initialized_words_bound (height ranks : Nat) :
    63 * (counts height ranks).sum ≤ ranks + 63 * height := by
  induction height generalizing ranks with
  | zero => simp [counts]
  | succ height ih =>
      by_cases empty : ranks = 0
      · simp [counts, empty]
      · by_cases root : wordsFor ranks = 1
        · simp only [counts, if_neg empty, if_pos root, List.sum_cons, List.sum_nil, add_zero]
          omega
        · have child := ih (wordsFor ranks)
          have padding := wordsFor_padding ranks
          simp only [counts, if_neg empty, if_neg root, List.sum_cons]
          omega

theorem both_pass_payload_bound (height ranks : Nat) :
    63 * (16 * (counts height ranks).sum) ≤ 16 * ranks + 1008 * height := by
  have bound := initialized_words_bound height ranks
  omega

/-- Six levels cover every rank admitted by the native 32-bit local index. -/
theorem six_levels_reach_root (ranks : Nat) (positive : 0 < ranks)
    (admitted : ranks < 4294967295) :
    wordsFor (wordsFor (wordsFor (wordsFor (wordsFor (wordsFor ranks))))) = 1 := by
  unfold wordsFor
  omega

theorem one_word_region (ranks : Nat) (positive : 0 < ranks) (small : ranks ≤ 64) :
    counts 6 ranks = [1] := by
  have root : wordsFor ranks = 1 := by unfold wordsFor; omega
  simp [counts, Nat.ne_of_gt positive, root]

/-- Exactly one pending reader is represented by the inline rank slot. -/
def requiredPayload (ranks pending : Nat) : Nat :=
  if pending ≤ 1 ∨ ranks ≤ 64 then 0 else 16 * (counts 6 ranks).sum

theorem single_reader_needs_no_bitmap (ranks pending : Nat) (single : pending ≤ 1) :
    requiredPayload ranks pending = 0 := by simp [requiredPayload, single]

theorem small_region_needs_no_bitmap (ranks pending : Nat) (small : ranks ≤ 64) :
    requiredPayload ranks pending = 0 := by simp [requiredPayload, small]

theorem promoted_payload_bound (ranks pending : Nat) :
    63 * requiredPayload ranks pending ≤ 16 * ranks + 6048 := by
  by_cases inline : pending ≤ 1 ∨ ranks ≤ 64
  · simp [requiredPayload, inline]
  · simpa [requiredPayload, inline] using both_pass_payload_bound 6 ranks

/-- Large sparse frontiers can use less memory than a per-rank queue. -/
theorem dense_layout_is_compact :
    16 * (counts 6 262145).sum = 66640 ∧ 66640 < 12 * 262145 := by decide

/-- Retained workspace is charged after the pending frontier has drained. -/
def retainedPayload (allocated : Bool) (ranks : Nat) : Nat :=
  if allocated then 16 * (counts 6 ranks).sum else 0

theorem allocated_workspace_remains_charged (ranks : Nat) :
    retainedPayload true ranks = 16 * (counts 6 ranks).sum := by simp [retainedPayload]

theorem pending_count_does_not_bound_retention :
    retainedPayload true 4096 > requiredPayload 4096 0 := by decide

end Mettapedia.Machines.ProducerBitmapLayout
