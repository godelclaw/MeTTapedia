import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# Sorted-key range partition

The native relational index seeks the first row outside an initial segment.
Lower and upper bounds differ only in the predicate: key < target, or
key ≤ target. The same midpoint recursion establishes both partitions, with
one comparison per halving step. These are range-local laws: a column sorted
inside one prefix need not be sorted across the entire relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RelationalKeyRanges

def binaryPartition (before : Nat → Bool) (lo hi : Nat) : Nat × Nat :=
  if lo < hi then
    let mid := lo + (hi - lo) / 2
    let next := if before mid then binaryPartition before (mid + 1) hi
                else binaryPartition before lo mid
    (next.1, next.2 + 1)
  else (lo, 0)
termination_by hi - lo
decreasing_by all_goals omega

def InitialSegment (before : Nat → Bool) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i ≤ j → j < hi → before j = true → before i = true

def PartitionAt (before : Nat → Bool) (lo hi boundary : Nat) : Prop :=
  lo ≤ boundary ∧ boundary ≤ hi ∧
    (∀ i, lo ≤ i → i < boundary → before i = true) ∧
    (∀ i, boundary ≤ i → i < hi → before i = false)

/-- The computed range boundary has no skipped initial row and no retained
row outside the predicate. This applies to empty and duplicate-key ranges. -/
theorem binaryPartition_correct (before : Nat → Bool) (lo hi : Nat)
    (ordered : InitialSegment before lo hi) (bounds : lo ≤ hi) :
    PartitionAt before lo hi (binaryPartition before lo hi).1 := by
  have aux : ∀ width lo hi, hi - lo = width → lo ≤ hi →
      InitialSegment before lo hi →
      PartitionAt before lo hi (binaryPartition before lo hi).1 := by
    intro width
    induction width using Nat.strong_induction_on with
    | h width ih =>
      intro lo hi size bounds ordered
      rw [binaryPartition]
      split
      next nonempty =>
        let mid := lo + (hi - lo) / 2
        have middle : lo ≤ mid ∧ mid < hi := by dsimp [mid]; omega
        change PartitionAt before lo hi
          (if before mid then binaryPartition before (mid + 1) hi
            else binaryPartition before lo mid).1
        cases test : before mid with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have rest := ih (mid - lo) (by omega) lo mid rfl middle.1
            (by
              intro i j lower ascending upper accepted
              exact ordered i j lower ascending (by omega) accepted)
          rcases rest with ⟨lower, upper, initialRows, remainingRows⟩
          refine ⟨lower, by omega, initialRows, ?_⟩
          intro i atBoundary belowHi
          by_cases earlier : i < mid
          · exact remainingRows i atBoundary earlier
          · cases value : before i with
            | false => rfl
            | true =>
              have contradiction := ordered mid i middle.1 (by omega) belowHi value
              simp [test] at contradiction
        | true =>
          simp only [↓reduceIte]
          have rest := ih (hi - (mid + 1)) (by omega) (mid + 1) hi rfl (by omega)
            (by
              intro i j lower ascending upper accepted
              exact ordered i j (by omega) ascending upper accepted)
          rcases rest with ⟨lower, upper, initialRows, remainingRows⟩
          refine ⟨by omega, upper, ?_, remainingRows⟩
          intro i aboveLo belowBoundary
          by_cases later : mid + 1 ≤ i
          · exact initialRows i later belowBoundary
          · exact ordered i mid aboveLo (by omega) middle.2 test
      next empty =>
        exact ⟨le_rfl, bounds, by omega, by omega⟩
  exact aux (hi - lo) lo hi rfl bounds ordered

/-- Fewer than 2^k rows require at most k midpoint comparisons. This is an
explicit logarithmic account, separate from relation construction and output. -/
theorem binaryPartition_comparisons_le (before : Nat → Bool)
    (lo hi k : Nat) (bounds : lo ≤ hi) (width : hi - lo < 2 ^ k) :
    (binaryPartition before lo hi).2 ≤ k := by
  induction k generalizing lo hi with
  | zero =>
    have equal : hi = lo := by simp only [pow_zero] at width; omega
    subst hi
    rw [binaryPartition]
    simp
  | succ k ih =>
    rw [binaryPartition]
    split
    next nonempty =>
      let mid := lo + (hi - lo) / 2
      have middle : lo ≤ mid ∧ mid < hi := by dsimp [mid]; omega
      have half : (hi - lo) / 2 < 2 ^ k := by
        rw [pow_succ] at width
        omega
      have leftWidth : mid - lo < 2 ^ k := by dsimp [mid]; omega
      have rightWidth : hi - (mid + 1) < 2 ^ k := by dsimp [mid]; omega
      change ((if before mid then binaryPartition before (mid + 1) hi
        else binaryPartition before lo mid).2 + 1) ≤ k + 1
      split
      · exact Nat.add_le_add_right (ih (mid + 1) hi (by omega) rightWidth) 1
      · exact Nat.add_le_add_right (ih lo mid middle.1 leftWidth) 1
    next empty => simp

theorem lower_bound_initial (keys : Nat → Nat) (lo hi target : Nat)
    (sorted : ∀ i j, lo ≤ i → i ≤ j → j < hi → keys i ≤ keys j) :
    InitialSegment (fun i => decide (keys i < target)) lo hi := by
  intro i j lower ascending upper accepted
  simp only [decide_eq_true_eq] at accepted ⊢
  exact lt_of_le_of_lt (sorted i j lower ascending upper) accepted

theorem upper_bound_initial (keys : Nat → Nat) (lo hi target : Nat)
    (sorted : ∀ i j, lo ≤ i → i ≤ j → j < hi → keys i ≤ keys j) :
    InitialSegment (fun i => decide (keys i ≤ target)) lo hi := by
  intro i j lower ascending upper accepted
  simp only [decide_eq_true_eq] at accepted ⊢
  exact le_trans (sorted i j lower ascending upper) accepted

def matchingKeyRange (keys : Nat → Nat) (lo hi target : Nat) : Nat × Nat :=
  ((binaryPartition (fun i => decide (keys i < target)) lo hi).1,
   (binaryPartition (fun i => decide (keys i ≤ target)) lo hi).1)

/-- A prefix-local lower/upper pair retains exactly the matching key rows.
Duplicate physical rows remain separate indices inside the returned range. -/
theorem matchingKeyRange_exact (keys : Nat → Nat) (lo hi target i : Nat)
    (sorted : ∀ a b, lo ≤ a → a ≤ b → b < hi → keys a ≤ keys b)
    (bounds : lo ≤ hi) (rowLower : lo ≤ i) (rowUpper : i < hi) :
    ((matchingKeyRange keys lo hi target).1 ≤ i ∧
      i < (matchingKeyRange keys lo hi target).2) ↔ keys i = target := by
  have lower := binaryPartition_correct (fun a => decide (keys a < target)) lo hi
    (lower_bound_initial keys lo hi target sorted) bounds
  have upper := binaryPartition_correct (fun a => decide (keys a ≤ target)) lo hi
    (upper_bound_initial keys lo hi target sorted) bounds
  rcases lower with ⟨_, _, lowerBefore, lowerAfter⟩
  rcases upper with ⟨_, _, upperBefore, upperAfter⟩
  constructor
  · intro inside
    have notSmaller := lowerAfter i inside.1 rowUpper
    have notLarger := upperBefore i rowLower inside.2
    simp only [decide_eq_false_iff_not, decide_eq_true_eq] at notSmaller notLarger
    omega
  · intro equal
    constructor
    · by_contra outside
      have smaller := lowerBefore i rowLower (by simpa only [matchingKeyRange] using Nat.lt_of_not_ge outside)
      simp only [decide_eq_true_eq] at smaller
      omega
    · by_contra outside
      have larger := upperAfter i (by simpa only [matchingKeyRange] using Nat.le_of_not_gt outside) rowUpper
      simp only [decide_eq_false_iff_not] at larger
      omega

namespace Controls

def duplicateKeys (i : Nat) : Nat := if i = 0 then 1 else if i < 4 then 2 else 3

theorem duplicate_lower_boundary :
    binaryPartition (fun i => decide (duplicateKeys i < 2)) 0 5 = (1, 3) := by
  repeat' (rw [binaryPartition]; norm_num [duplicateKeys])

theorem duplicate_upper_boundary :
    binaryPartition (fun i => decide (duplicateKeys i ≤ 2)) 0 5 = (4, 3) := by
  repeat' (rw [binaryPartition]; norm_num [duplicateKeys])

theorem empty_range_comparisons : binaryPartition (fun _ => true) 7 7 = (7, 0) := by
  rw [binaryPartition]
  norm_num

theorem unordered_predicate_can_skip_row :
    let before := fun i => decide (i = 0 ∨ i = 2)
    let boundary := (binaryPartition before 0 4).1
    before 1 = false ∧ 1 < boundary := by
  dsimp only
  repeat' (rw [binaryPartition]; norm_num)

end Controls

end Mettapedia.GSLT.Dynamics.RelationalKeyRanges
