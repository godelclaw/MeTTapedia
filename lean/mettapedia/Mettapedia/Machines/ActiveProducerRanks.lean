import Mathlib.Data.List.Sort

/-!
# Dense ranks for unfinished producer frames

The reference stack retains globally increasing discovery labels. The compact
stack uses current positions, reusing positions after a completed suffix retires.
All comparisons, lowlink minima and root tests agree on active frames. Metadata
retirement is a separate obligation: a reused position is not a producer identity.
These laws justify the representation change, not the entire native SCC algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ActiveProducerRanks

structure Stack where
  labels : List Nat
  next : Nat
  deriving DecidableEq, Repr

def Valid (stack : Stack) : Prop :=
  stack.labels.Pairwise (· < ·) ∧ ∀ label ∈ stack.labels, label < stack.next

def empty : Stack := ⟨[], 0⟩

def push (stack : Stack) : Stack :=
  ⟨stack.labels ++ [stack.next], stack.next + 1⟩

def retire (keep : Nat) (stack : Stack) : Stack :=
  ⟨stack.labels.take keep, stack.next⟩

theorem empty_valid : Valid empty := by simp [Valid, empty]

theorem push_valid (stack : Stack) (valid : Valid stack) : Valid (push stack) := by
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨valid.1, by simp, ?_⟩
    intro a member b last
    have equal : b = stack.next := by simpa using last
    subst b
    exact valid.2 a member
  · intro label member
    rcases List.mem_append.mp member with old | last
    · exact Nat.lt_trans (valid.2 label old) (Nat.lt_succ_self _)
    · have equal : label = stack.next := by simpa using last
      subst label
      exact Nat.lt_succ_self _

theorem retire_valid (keep : Nat) (stack : Stack) (valid : Valid stack) :
    Valid (retire keep stack) :=
  ⟨valid.1.take, fun label member => valid.2 label (List.mem_of_mem_take member)⟩

def label (stack : Stack) (rank : Fin stack.labels.length) : Nat := stack.labels.get rank

theorem label_strictMono (stack : Stack) (valid : Valid stack) :
    StrictMono (label stack) := List.pairwise_iff_get.mp valid.1

theorem comparison_lt (stack : Stack) (valid : Valid stack)
    (a b : Fin stack.labels.length) : label stack a < label stack b ↔ a < b :=
  (label_strictMono stack valid).lt_iff_lt

theorem comparison_le (stack : Stack) (valid : Valid stack)
    (a b : Fin stack.labels.length) : label stack a ≤ label stack b ↔ a ≤ b :=
  (label_strictMono stack valid).le_iff_le

theorem comparison_eq (stack : Stack) (valid : Valid stack)
    (a b : Fin stack.labels.length) : label stack a = label stack b ↔ a = b :=
  (label_strictMono stack valid).injective.eq_iff

/-- The minimum used by dependency and child-return lowlink updates commutes. -/
theorem lowlink_update (stack : Stack) (valid : Valid stack)
    (low target : Fin stack.labels.length) :
    label stack (min low target) = min (label stack low) (label stack target) := by
  by_cases ordered : low ≤ target
  · rw [min_eq_left ordered, min_eq_left ((comparison_le stack valid low target).mpr ordered)]
  · have reverse : target ≤ low := le_of_not_ge ordered
    rw [min_eq_right reverse, min_eq_right ((comparison_le stack valid target low).mpr reverse)]

theorem root_test (stack : Stack) (valid : Valid stack)
    (low root : Fin stack.labels.length) :
    decide (label stack low = label stack root) = decide (low = root) := by
  simp only [comparison_eq stack valid]

theorem retired_prefix_label (stack : Stack) (keep : Nat)
    (rank : Fin (retire keep stack).labels.length) :
    label (retire keep stack) rank =
      label stack ⟨rank.val, lt_of_lt_of_le rank.isLt (by
        simp only [retire, List.length_take]
        exact Nat.min_le_right _ _)⟩ := by
  unfold label
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact List.getElem_take

theorem push_preserves_old_label (stack : Stack) (rank : Fin stack.labels.length) :
    label (push stack) ⟨rank.val, by simpa [push] using Nat.lt_succ_of_lt rank.isLt⟩ =
      label stack rank := by
  simp [label, push, rank.isLt]

theorem push_new_label (stack : Stack) :
    label (push stack) ⟨stack.labels.length, by simp [push]⟩ = stack.next := by
  simp [label, push]

/-- A reused position denotes the new discovery label, not the old one. -/
theorem reused_positions_keep_comparisons :
    let stack := push (retire 1 (push (push empty)))
    stack.labels = [0, 2] ∧ Valid stack ∧
      label stack ⟨0, by decide⟩ < label stack ⟨1, by decide⟩ := by
  simp [push, retire, empty, Valid, label]

universe u
variable {Certificate : Type u}

def MetadataValid (active : Nat) (metadata : Nat → Option Certificate) : Prop :=
  ∀ slot, active ≤ slot → metadata slot = none

/-- Clear exactly the retired suffix; preserve the still-active prefix. -/
def retireMetadata (keep active : Nat) (metadata : Nat → Option Certificate) :
    Nat → Option Certificate :=
  fun slot => if keep ≤ slot ∧ slot < active then none else metadata slot

theorem retireMetadata_prefix (keep active slot : Nat) (metadata : Nat → Option Certificate)
    (before : slot < keep) : retireMetadata keep active metadata slot = metadata slot := by
  simp [retireMetadata, Nat.not_le_of_gt before]

theorem retireMetadata_valid (keep active : Nat) (metadata : Nat → Option Certificate)
    (valid : MetadataValid active metadata) :
    MetadataValid keep (retireMetadata keep active metadata) := by
  intro slot past
  by_cases inside : slot < active
  · simp [retireMetadata, past, inside]
  · simp [retireMetadata, inside, valid slot (Nat.le_of_not_gt inside)]

theorem reused_position_has_no_certificate (keep active : Nat)
    (metadata : Nat → Option Certificate) (valid : MetadataValid active metadata) :
    retireMetadata keep active metadata keep = none :=
  retireMetadata_valid keep active metadata valid keep (Nat.le_refl _)

theorem push_metadata_valid (active : Nat) (metadata : Nat → Option Certificate)
    (valid : MetadataValid active metadata) : MetadataValid (active + 1) metadata := by
  intro slot beyond
  exact valid slot (by omega)

def staleExample : Nat → Option Nat := fun slot => if slot = 1 then some 7 else none

theorem unretired_position_reuses_stale_certificate :
    MetadataValid 2 staleExample ∧ staleExample 1 = some 7 ∧
      ¬ MetadataValid 1 staleExample := by
  constructor
  · intro slot beyond
    simp [staleExample, show slot ≠ 1 by omega]
  · constructor
    · rfl
    · intro invalid
      have impossible := invalid 1 (Nat.le_refl _)
      simp [staleExample] at impossible

theorem retirement_removes_the_stale_certificate :
    retireMetadata 1 2 staleExample 1 = none := by decide

end Mettapedia.Machines.ActiveProducerRanks
