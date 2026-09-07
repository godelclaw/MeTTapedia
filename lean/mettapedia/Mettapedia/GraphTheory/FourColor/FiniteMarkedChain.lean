import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Card
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

/-!
# Constant marked material along a nested chain

In a monotone family of vertex sides, each marked vertex can enter only
once. Thus `(t+1)*n+1` sides suffice for `n` consecutive slabs which acquire
none of `t` marked vertices. The bound is linear in the number of marks,
not exponential in their possible subsets. This is a vertex statement;
an edge with endpoints on opposite persistent sides can still cross every
cut in the selected interval.
-/

namespace Mettapedia.GraphTheory.FourColor.FiniteMarkedChain

/-- An increasing finite sequence of naturals gains at least its index gap. -/
theorem strictMono_nat_gap {N : ℕ} (f : Fin N → ℕ) (hf : StrictMono f)
    {i j : Fin N} (hij : i ≤ j) : j.val - i.val ≤ f j - f i := by
  have aux : ∀ k (hk : k < N), ∀ a (ha : a ≤ k),
      f ⟨a, ha.trans_lt hk⟩ + (k - a) ≤ f ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk a ha
      have : a = 0 := by omega
      subst a
      simp
    | succ k ih =>
      intro hk a ha
      by_cases heq : a = k + 1
      · subst a; simp
      · have hak : a ≤ k := by omega
        have hprev := ih (by omega) a hak
        have hstep := hf (show (⟨k, by omega⟩ : Fin N) < ⟨k + 1, hk⟩ from
          Nat.lt_succ_self k)
        have hsub : k + 1 - a = (k - a) + 1 := by omega
        omega
  have := aux j.val j.isLt i.val hij
  change f i + (j.val - i.val) ≤ f j at this
  omega

/-- Sample the endpoints of the disjoint length-`n` windows. -/
def coarseIndex (t n : ℕ) (j : Fin (t + 2)) : Fin ((t + 1) * n + 1) :=
  ⟨j.val * n, by have := Nat.mul_le_mul_right n (show j.val ≤ t + 1 by omega); omega⟩

/-- The `j`th consecutive window, without changing the order of any cut. -/
def windowIndex (t n : ℕ) (j : Fin (t + 1)) :
    Fin (n + 1) ↪o Fin ((t + 1) * n + 1) where
  toFun i := ⟨j.val * n + i.val, by
    have := Nat.mul_le_mul_right n (show j.val + 1 ≤ t + 1 by omega)
    rw [Nat.add_mul, one_mul] at this
    omega⟩
  inj' := by intro i k h; apply Fin.ext; have := congrArg Fin.val h; simp at this; omega
  map_rel_iff' := by intro i k; change j.val * n + i.val ≤ j.val * n + k.val ↔ i.val ≤ k.val; omega

theorem exists_constant_window {V : Type*} [DecidableEq V]
    (marks : Finset V) (n : ℕ)
    (sides : Fin ((marks.card + 1) * n + 1) → Set V)
    (hmono : Monotone sides) :
    ∃ j : Fin (marks.card + 1), ∀ i : Fin (n + 1),
      ∀ v ∈ marks, v ∈ sides (windowIndex marks.card n j i) ↔
        v ∈ sides (windowIndex marks.card n j 0) := by
  classical
  let slice := fun i => marks.filter (fun v => v ∈ sides i)
  have hs : Monotone slice := by
    intro i j hij v hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,
      hmono hij (Finset.mem_filter.mp hv).2⟩
  let rank : Fin (marks.card + 2) → Fin (marks.card + 1) := fun i =>
    ⟨(slice (coarseIndex marks.card n i)).card,
      Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))⟩
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt rank (by simp)
  have hex : ∃ i j : Fin (marks.card + 2), i < j ∧ rank i = rank j := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ⟨i, j, hij, heq⟩
    · exact ⟨j, i, hji, heq.symm⟩
  obtain ⟨i, j, hij, heq⟩ := hex
  let start : Fin (marks.card + 1) := ⟨i.val, by omega⟩
  have hcoarse : coarseIndex marks.card n i ≤ coarseIndex marks.card n j :=
    Nat.mul_le_mul_right n (Nat.le_of_lt hij)
  have hslice : slice (coarseIndex marks.card n i) =
      slice (coarseIndex marks.card n j) := by
    apply Finset.eq_of_subset_of_card_le (hs hcoarse)
    exact (congrArg Fin.val heq).symm.le
  refine ⟨start, fun p v hv => ?_⟩
  have hlo : coarseIndex marks.card n i ≤ windowIndex marks.card n start p := by
    change i.val * n ≤ i.val * n + p.val
    omega
  have hhi : windowIndex marks.card n start p ≤ coarseIndex marks.card n j := by
    have hmul := Nat.mul_le_mul_right n (show i.val + 1 ≤ j.val by omega)
    rw [Nat.add_mul, one_mul] at hmul
    change i.val * n + p.val ≤ j.val * n
    omega
  have hz : windowIndex marks.card n start 0 = coarseIndex marks.card n i := by
    apply Fin.ext
    simp [windowIndex, coarseIndex, start]
  have hsame : slice (windowIndex marks.card n start p) =
      slice (coarseIndex marks.card n i) :=
    Finset.Subset.antisymm (hslice ▸ hs hhi) (hs hlo)
  rw [hz]
  have := Finset.ext_iff.mp hsame v
  simpa [slice, hv] using this

end Mettapedia.GraphTheory.FourColor.FiniteMarkedChain
