import Mettapedia.GraphTheory.FourColor.PaddedCycleCapColouring
import Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryReindex
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Transport from the literal smaller cycle

The boundary coordinates pair consecutive cycle ports. The source witness
is a genuine colouring of that cycle, not an independent collection of
sector choices. Its nonconstant boundary reconstructs the padded cap.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap

open GoertzelV24OpenTangleComposition

set_option backward.isDefEq.respectTransparency false

variable (m : ℕ) [NeZero m]

def bit : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := i == 1
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def portIndex : Boundary m ≃ Fin (m*2) :=
  (Equiv.prodCongr (Equiv.refl _) bit).trans finProdFinEquiv

theorem portIndex_false_next (i : Fin m) :
    portIndex m (i,false) + 1 = portIndex m (i,true) := by
  apply Fin.ext
  have hi := i.isLt
  simp [portIndex, bit, Fin.val_add, Nat.mod_eq_of_lt (show 1 < m*2 by
    have := NeZero.pos m; omega), Nat.mod_eq_of_lt (show 2*i.val+1 < m*2 by omega)]
  omega

theorem portIndex_true_next (i : Fin m) :
    portIndex m (i,true) + 1 = portIndex m (i+1,false) := by
  apply Fin.ext
  have hi := i.isLt
  have hm := NeZero.pos m
  by_cases hl : i.val + 1 < m
  · simp [portIndex, bit, Fin.val_add, Nat.mod_eq_of_lt (show 1 < m*2 by omega),
      Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (show 1 < m by omega),
      Nat.mod_eq_of_lt (show 1+2*i.val+1 < m*2 by omega)]
    omega
  · have he : i.val+1=m := by omega
    have hz : i+1 = (0 : Fin m) := by
      apply Fin.ext
      by_cases h1 : m=1
      · subst m; simp
      · simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < m by omega), he]
    rw [hz]
    simp [portIndex, bit, Fin.val_add, Nat.mod_eq_of_lt (show 1 < m*2 by omega),
      show 1+2*i.val+1=m*2 by omega]

theorem cycleWitness_of_edges {a : Fin (m*2) → Color}
    (ha : CycleCap.Valid (m*2) a) :
    CycleWitness m (CycleCap.spokes (m*2) a ∘ portIndex m)
      (fun i => a (portIndex m (i,false))) := by
  refine ⟨?_, fun i => ha.1 _, ?_, ?_⟩
  · intro b
    exact add_ne_zero_of_ne (ha.2 _)
  · intro i
    simpa only [Function.comp_apply, CycleCap.spokes, portIndex_false_next,
      ← add_assoc, color_add_self, zero_add] using ha.1 (portIndex m (i,true))
  · intro i
    simp only [Function.comp_apply, CycleCap.spokes, portIndex_false_next,
      portIndex_true_next]
    abel_nf
    simp [two_mul]

/-- Every nonconstant boundary colouring of the actual smaller cycle lifts. -/
theorem reconstruct_cycle (hm : 2 ≤ m) {w : Fin (m*2) → Color}
    (h : (CycleCap.cap (m*2) (by omega)).AcceptsBoundaryWords Empty.elim w)
    (hn : ¬ ∃ c, ∀ i, w i = c) :
    (tangle m hm).AcceptsBoundaryWords Empty.elim (w ∘ portIndex m) := by
  obtain ⟨seam, hc, ht, hw, hs⟩ := (CycleSeamTransfer.accepts_iff_marked (by omega) w).mp h
  have ha := CycleSeamTransfer.edges_valid (by omega) ht
  have he := (CycleSeamTransfer.spokes_edges (by omega) ht).trans hw
  apply accepts_of_nonconstant m hm
    (s := fun i => CycleSeamTransfer.edges hc (portIndex m (i,false)))
  · simpa [he] using cycleWitness_of_edges m ha
  · rintro ⟨c,hc⟩
    apply hn
    refine ⟨c, fun i => ?_⟩
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hc ((portIndex m).symm i)


noncomputable section

/-- The larger cap in the consecutive boundary coordinates of the smaller cycle. -/
def indexedCap (hm : 2 ≤ m) :
    TwoSidedOpenTangleData (Vertex m) (Interior m) Empty (Fin (m*2)) :=
  TwoSidedBoundaryReindex.reindex (tangle m hm)
    (Equiv.sumCongr (Equiv.refl Empty) (portIndex m).symm)

theorem indexed_accepts (hm : 2 ≤ m) (w : Fin (m*2) → Color) :
    (indexedCap m hm).AcceptsBoundaryWords Empty.elim w ↔
      (tangle m hm).AcceptsBoundaryWords Empty.elim (w ∘ portIndex m) := by
  have h := TwoSidedBoundaryReindex.accepts_reindex (tangle m hm)
    (Equiv.sumCongr (Equiv.refl Empty) (portIndex m).symm)
    (Sum.elim Empty.elim (w ∘ portIndex m))
  have he : Sum.elim Empty.elim (w ∘ portIndex m) ∘
      Equiv.sumCongr (Equiv.refl Empty) (portIndex m).symm = Sum.elim Empty.elim w := by
    funext b
    rcases b with e | i
    · exact nomatch e
    · simp
  rw [he, TwoSidedBoundaryReindex.accepts_iff,
    TwoSidedBoundaryReindex.accepts_iff] at h
  exact h

theorem reconstruct_indexed (hm : 2 ≤ m) (x : Empty → Color) (w : Fin (m*2) → Color)
    (h : (CycleCap.cap (m*2) (by omega)).AcceptsBoundaryWords x w)
    (hn : ¬ ∃ c, ∀ i, w i = c) : (indexedCap m hm).AcceptsBoundaryWords x w := by
  have hx : x = Empty.elim := by funext e; exact nomatch e
  subst x
  exact (indexed_accepts m hm w).mpr (reconstruct_cycle m hm h hn)

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap
