import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

/-!
# Binary prefix counts over ordered occurrence columns

The binary loop reads one position per step. Its result is proved equal to
the cardinality of the independently filtered index range, so repeated source
positions remain separate occurrences. Sortedness is an admission condition;
the reference count is meaningful without it. No numerical reassociation is
involved: only comparisons and exact index arithmetic are used.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Retrieval.PrefixSearch

def lowerBound (read : Nat → Int) (cutoff : Int) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    let middle := lo + (hi - lo) / 2
    if read middle < cutoff then lowerBound read cutoff (middle + 1) hi
    else lowerBound read cutoff lo middle
  else lo
termination_by hi - lo
decreasing_by all_goals omega

def SortedTo (read : Nat → Int) (length : Nat) : Prop :=
  ∀ i j, i ≤ j → j < length → read i ≤ read j

/-- The portable MeTTa expression divides an even integer, avoiding a
floating intermediate and a profile-specific integer-division primitive. -/
theorem even_quotient_midpoint (lo hi : Nat) :
    lo + ((hi - lo) - (hi - lo) % 2) / 2 = lo + (hi - lo) / 2 := by omega

/-- Independent reference: count positions, not distinct stored values. -/
def countBefore (read : Nat → Int) (length : Nat) (cutoff : Int) : Nat :=
  ((Finset.range length).filter fun i => read i < cutoff).card

private theorem lowerBound_partition (read : Nat → Int) (cutoff : Int) (n : Nat)
    (sorted : SortedTo read n) (lo hi : Nat) (ordered : lo ≤ hi) (bounded : hi ≤ n)
    (before : ∀ i, i < lo → read i < cutoff)
    (after : ∀ i, hi ≤ i → i < n → ¬ read i < cutoff) :
    lo ≤ lowerBound read cutoff lo hi ∧ lowerBound read cutoff lo hi ≤ hi ∧
      ∀ i, i < n → (read i < cutoff ↔ i < lowerBound read cutoff lo hi) := by
  have helper : ∀ width lo hi, hi - lo = width → lo ≤ hi → hi ≤ n →
      (∀ i, i < lo → read i < cutoff) →
      (∀ i, hi ≤ i → i < n → ¬ read i < cutoff) →
      lo ≤ lowerBound read cutoff lo hi ∧ lowerBound read cutoff lo hi ≤ hi ∧
        ∀ i, i < n → (read i < cutoff ↔ i < lowerBound read cutoff lo hi) := by
    intro width
    induction width using Nat.strong_induction_on with
    | h width ih =>
      intro lo hi size ordered bounded before after
      by_cases active : lo < hi
      · let middle := lo + (hi - lo) / 2
        have midLo : lo ≤ middle := by dsimp [middle]; omega
        have midHi : middle < hi := by dsimp [middle]; omega
        rw [lowerBound, dif_pos active]
        change lo ≤ (if read middle < cutoff then
            lowerBound read cutoff (middle + 1) hi else lowerBound read cutoff lo middle) ∧
          (if read middle < cutoff then
            lowerBound read cutoff (middle + 1) hi else lowerBound read cutoff lo middle) ≤ hi ∧
          ∀ i, i < n →
          (read i < cutoff ↔ i < if read middle < cutoff then
            lowerBound read cutoff (middle + 1) hi else lowerBound read cutoff lo middle)
        by_cases hit : read middle < cutoff
        · simp only [hit, if_true]
          have small : hi - (middle + 1) < width := by omega
          have before' : ∀ i, i < middle + 1 → read i < cutoff := by
            intro i hi'
            exact lt_of_le_of_lt (sorted i middle (by omega) (by omega)) hit
          obtain ⟨lower, upper, partition⟩ :=
            ih (hi - (middle + 1)) small (middle + 1) hi rfl (by omega)
              bounded before' after
          exact ⟨by omega, upper, partition⟩
        · simp only [hit, if_false]
          have small : middle - lo < width := by omega
          have after' : ∀ i, middle ≤ i → i < n → ¬ read i < cutoff := by
            intro i hi' hn bad
            exact hit (lt_of_le_of_lt (sorted middle i hi' hn) bad)
          obtain ⟨lower, upper, partition⟩ :=
            ih (middle - lo) small lo middle rfl midLo (by omega) before after'
          exact ⟨lower, by omega, partition⟩
      · rw [lowerBound, dif_neg active]
        refine ⟨le_rfl, ordered, ?_⟩
        intro i hn
        constructor
        · intro hit
          by_contra no
          exact after i (by omega) hn hit
        · exact before i
  exact helper (hi - lo) lo hi rfl ordered bounded before after

theorem lowerBound_eq_countBefore (read : Nat → Int) (length : Nat) (cutoff : Int)
    (sorted : SortedTo read length) :
    lowerBound read cutoff 0 length = countBefore read length cutoff := by
  obtain ⟨_, bounded, partition⟩ := lowerBound_partition read cutoff length sorted
    0 length (Nat.zero_le _) le_rfl (by omega) (by omega)
  have same : (Finset.range length).filter (fun i => read i < cutoff) =
      Finset.range (lowerBound read cutoff 0 length) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hit⟩
      exact (partition i hn).mp hit
    · intro hit
      have hn : i < length := by omega
      exact ⟨hn, (partition i hn).mpr hit⟩
  simp [countBefore, same]

theorem empty_column (read : Nat → Int) (cutoff : Int) :
    lowerBound read cutoff 0 0 = 0 := by rw [lowerBound]; simp

theorem minimum_excludes_column (read : Nat → Int) (length : Nat) (cutoff : Int)
    (sorted : SortedTo read length) (minimum : cutoff ≤ read 0) :
    lowerBound read cutoff 0 length = 0 := by
  rw [lowerBound_eq_countBefore read length cutoff sorted]
  have empty : (Finset.range length).filter (fun i => read i < cutoff) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i member
    obtain ⟨hn, hit⟩ := Finset.mem_filter.mp member
    have lower := sorted 0 i (Nat.zero_le _) (Finset.mem_range.mp hn)
    exact (not_lt_of_ge (minimum.trans lower)) hit
  simp [countBefore, empty]

theorem maximum_includes_column (read : Nat → Int) (length : Nat) (cutoff : Int)
    (sorted : SortedTo read length) (maximum : read (length - 1) < cutoff) :
    lowerBound read cutoff 0 length = length := by
  rw [lowerBound_eq_countBefore read length cutoff sorted]
  have full : (Finset.range length).filter (fun i => read i < cutoff) = Finset.range length := by
    apply Finset.filter_eq_self.mpr
    intro i member
    have hn := Finset.mem_range.mp member
    exact lt_of_le_of_lt (sorted i (length - 1) (by omega) (by omega)) maximum
  simp [countBefore, full]

theorem duplicates_are_occurrences :
    lowerBound (fun i => if i < 3 then 7 else 12) 8 0 5 = 3 ∧
      countBefore (fun i => if i < 3 then 7 else 12) 5 8 = 3 := by
  constructor
  · simp [lowerBound]
  · decide

/-- Without ordering the binary algorithm is not a valid counting region. -/
theorem unordered_column_must_decline :
    lowerBound (fun i => if i = 0 then 0 else -1) 0 0 2 ≠
      countBefore (fun i => if i = 0 then 0 else -1) 2 0 := by
  have found : lowerBound (fun i => if i = 0 then 0 else -1) 0 0 2 = 2 := by
    simp [lowerBound]
  rw [found]
  decide

end Mettapedia.Algorithms.Retrieval.PrefixSearch
