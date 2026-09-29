import Mettapedia.GraphTheory.FourColor.CycleFrame
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.ChainOfFn

/-!
# The actual closed walk of a cyclic frame

A frame's cyclic order constructs a simple graph cycle with exactly its
forward and backward edges. This supplies the input to facial separation;
no second cycle witness or edge-set correspondence is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.InducedCycleLayer

open ZigzagRing SimpleGraph
open Fin.NatCast

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} {G : SimpleGraph V} {k : ℕ} [NeZero k]

/-- Interleave the two vertex classes in cyclic order. -/
def rowIndex (i : Fin (k * 2)) : Vtx k :=
  if i.val % 2 = 0 then .inl ⟨i.val / 2, by omega⟩
  else .inr ⟨i.val / 2, by omega⟩

omit [NeZero k] in
theorem rowIndex_injective : Function.Injective (rowIndex (k := k)) := by
  intro i j h
  unfold rowIndex at h
  split_ifs at h <;> simp only [Sum.inl.injEq, Sum.inr.injEq] at h
  all_goals
    have he := congrArg Fin.val h
    apply Fin.ext
    dsimp at he
    omega

omit [NeZero k] in
theorem rowIndex_surjective : Function.Surjective (rowIndex (k := k)) := by
  rintro (i | i)
  · refine ⟨⟨i.val * 2, by omega⟩, ?_⟩
    simp [rowIndex]
  · refine ⟨⟨i.val * 2 + 1, by omega⟩, ?_⟩
    simp [rowIndex, Nat.add_div]

theorem rowIndex_next (hk : 2 ≤ k) (i : Fin (k * 2)) :
    rowIndex (i + 1) = next k (rowIndex i) := by
  have h1 : (1 : Fin (k * 2)).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < k * 2)]
  have hj : (i + 1).val = (i.val + 1) % (k * 2) := by simp only [Fin.val_add, h1]
  have hki := i.isLt
  by_cases hw : i.val + 1 = k * 2
  · have hi : i.val % 2 ≠ 0 := by omega
    have hdiv : i.val / 2 + 1 = k := by omega
    have hzero : (i + 1).val = 0 := by rw [hj, hw, Nat.mod_self]
    simp only [rowIndex, hzero, Nat.zero_mod, ite_true, hi, ite_false, next]
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one']
    rw [Nat.mod_eq_of_lt (by omega : 1 < k)]
    change 0 = (i.val / 2 + 1) % k
    simp [hdiv]
  · have hjlt : i.val + 1 < k * 2 := by omega
    rw [Nat.mod_eq_of_lt hjlt] at hj
    by_cases hi : i.val % 2 = 0
    · have hn : (i + 1).val % 2 ≠ 0 := by omega
      simp only [rowIndex, hn, ite_false, hi, ite_true, next]
      apply congrArg Sum.inr
      apply Fin.ext
      dsimp
      omega
    · have hn : (i + 1).val % 2 = 0 := by omega
      simp only [rowIndex, hn, ite_true, hi, ite_false, next]
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one']
      rw [Nat.mod_eq_of_lt (by omega : 1 < k)]
      change (i + 1).val / 2 = (i.val / 2 + 1) % k
      rw [Nat.mod_eq_of_lt (by omega : i.val / 2 + 1 < k)]
      omega

namespace Frame

variable (C : Frame G k) (hk : 2 ≤ k) [DecidableEq V] [G.LocallyFinite]
  (hG : G.IsRegularOfDegree 3)

private def cyclicDart (i : Fin (k * 2)) : G.Dart := C.star hk hG (rowIndex i) 1

private theorem cyclicDart_next (i : Fin (k * 2)) :
    G.DartAdj (C.cyclicDart hk hG i) (C.cyclicDart hk hG (i + 1)) := by
  change C.vertex (next k (rowIndex i)) = C.vertex (rowIndex (i + 1))
  rw [rowIndex_next hk]

/-- The cyclic frame is a genuine simple closed walk. Its exact edge
description is retained for the facial separation theorem. -/
theorem exists_cycle :
    ∃ (root : V) (walk : G.Walk root root), walk.IsCycle ∧
      ∀ d : G.Dart, d.edge ∈ walk.edges ↔
        ∃ v, d = C.star hk hG v 1 ∨ d = C.star hk hG v 2 := by
  let darts := List.ofFn (C.cyclicDart hk hG)
  have hn : darts ≠ [] := by
    have : darts.length = k * 2 := by simp [darts]
    intro he
    simp only [he, List.length_nil] at this
    omega
  have hc : List.IsChain G.DartAdj darts := by
    rw [List.isChain_ofFn]
    intro i hi
    have he : (⟨i, by omega⟩ : Fin (k * 2)) + 1 = ⟨i + 1, hi⟩ := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one']
      rw [Nat.mod_eq_of_lt (by omega : 1 < k * 2)]
      exact Nat.mod_eq_of_lt hi
    simpa only [he] using C.cyclicDart_next hk hG ⟨i, by omega⟩
  have hl : G.DartAdj (darts.getLast hn) (darts.head hn) := by
    have hp : 0 < k * 2 := by omega
    have he : (⟨k * 2 - 1, by omega⟩ : Fin (k * 2)) + 1 = 0 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one', Fin.val_zero]
      rw [Nat.mod_eq_of_lt (by omega : 1 < k * 2)]
      simp [Nat.sub_add_cancel hp]
    simpa [darts, List.getLast_ofFn, List.head_ofFn, he] using
      C.cyclicDart_next hk hG ⟨k * 2 - 1, by omega⟩
  let w := (Walk.ofDarts darts hn hc).copy rfl hl
  have hw : w.darts = darts := by simp only [w, Walk.darts_copy, Walk.darts_ofDarts]
  have hnw : ¬ w.Nil := by
    intro h
    exact hn (hw.symm.trans (Walk.darts_eq_nil.mpr h))
  have hnodup : w.support.dropLast.Nodup := by
    rw [← w.map_fst_darts, hw, List.map_ofFn, List.nodup_ofFn]
    exact C.injective.comp rowIndex_injective
  have hcycle : w.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · apply Walk.IsPath.mk'
      rw [w.support_tail_of_not_nil hnw]
      exact w.tail_support_perm_dropLast_support.nodup_iff.mpr hnodup
    · have hh := w.length_darts
      rw [hw] at hh
      simp only [darts, List.length_ofFn] at hh
      omega
  refine ⟨_, w, hcycle, ?_⟩
  intro d
  rw [Walk.edges, hw, List.mem_map]
  constructor
  · rintro ⟨e, he, hed⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    rcases (SimpleGraph.dart_edge_eq_iff d _).mp hed.symm with h | h
    · exact ⟨rowIndex i, Or.inl h⟩
    · refine ⟨next k (rowIndex i), Or.inr ?_⟩
      rw [h]
      apply SimpleGraph.Dart.ext
      simp [cyclicDart, star, prev_next]
  · rintro ⟨v, hv | hv⟩
    · obtain ⟨i, rfl⟩ := rowIndex_surjective v
      exact ⟨C.cyclicDart hk hG i, List.mem_ofFn.mpr ⟨i, rfl⟩, hv ▸ rfl⟩
    · obtain ⟨i, hi⟩ := rowIndex_surjective (prev k v)
      refine ⟨C.cyclicDart hk hG i, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
      rw [hv]
      change (C.star hk hG (rowIndex i) 1).edge = (C.star hk hG v 2).edge
      rw [hi]
      simp [star, next_prev, SimpleGraph.Dart.edge, Sym2.eq_swap]

end Frame
end
end Mettapedia.GraphTheory.FourColor.InducedCycleLayer
