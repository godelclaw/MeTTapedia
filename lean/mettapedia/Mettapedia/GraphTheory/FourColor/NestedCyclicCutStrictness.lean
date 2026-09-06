import Mettapedia.GraphTheory.FourColor.CyclicCutConnectedShore

/-!
# Strict incident-shore growth from connected complements

Let `S ⊂ T` be vertex sides, with the old complement connected and the new
complement nonempty. A path in the old complement from `T \ S` to `V \ T`
contains an edge absent from the old incident shore and present in the new
one. Thus conversion of these nested vertex cuts into incident-edge shores
preserves strictness, without a separate fresh-edge hypothesis.

The cyclic-cut corollary supplies strict node shores to the existing exact
state splice. It neither constructs a bounded-width cut nor supplies a long
chain. No boundary, cyclic ordering, or connectivity receipt is changed.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph GoertzelV24ConnectedVertexSideEdgeShore

namespace NestedCyclicCutStrictness

variable {V : Type*} {G : SimpleGraph V}

/-- A walk whose endpoints lie on opposite sides has a crossing edge. -/
theorem exists_crossing_on_walk (side : V → Prop) {a b : V} (p : G.Walk a b)
    (ha : side a) (hb : ¬ side b) :
    ∃ x y, G.Adj x y ∧ side x ∧ ¬ side y := by
  classical
  induction p with
  | nil => exact (hb ha).elim
  | @cons a c b hac p ih =>
      by_cases hc : side c
      · exact ih hc hb
      · exact ⟨a, c, hac, ha, hc⟩

/-- Connectedness of the old exterior forces an edge between newly added
vertices and the still-unselected exterior. -/
theorem exists_fresh_crossing {S T : V → Prop}
    (hnew : ∃ x, T x ∧ ¬ S x) (hout : ∃ y, ¬ T y)
    (hST : ∀ v, S v → T v)
    (hconn : (G.induce (fun v => ¬ S v)).Preconnected) :
    ∃ x y, G.Adj x y ∧ T x ∧ ¬ T y ∧ ¬ S x ∧ ¬ S y := by
  obtain ⟨x, hxT, hxS⟩ := hnew
  obtain ⟨y, hyT⟩ := hout
  have hyS : ¬ S y := fun h => hyT (hST y h)
  obtain ⟨p⟩ := hconn ⟨x, hxS⟩ ⟨y, hyS⟩
  obtain ⟨a, b, hab, ha, hb⟩ :=
    exists_crossing_on_walk (fun v : {v // ¬ S v} => T v) p hxT hyT
  exact ⟨a, b, hab, ha, hb, a.property, b.property⟩

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- The full incident-edge shores are strictly nested. -/
theorem incidentEdgeShore_ssubset {S T : V → Prop}
    (hST : ∀ v, S v → T v) (hnew : ∃ x, T x ∧ ¬ S x)
    (hout : ∃ y, ¬ T y)
    (hconn : (G.induce (fun v => ¬ S v)).Preconnected) :
    incidentEdgeShore G S ⊂ incidentEdgeShore G T := by
  classical
  obtain ⟨x, y, hxy, hxT, _, hxS, hyS⟩ := exists_fresh_crossing hnew hout hST hconn
  let e : G.edgeSet := ⟨s(x, y), hxy⟩
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨incidentEdgeShore_mono hST, ?_⟩
  intro heq
  have hmem : e ∈ incidentEdgeShore G T := by
    rw [mem_incidentEdgeShore_iff]
    exact ⟨x, Sym2.mem_mk_left x y, hxT⟩
  rw [← heq, mem_incidentEdgeShore_iff] at hmem
  obtain ⟨v, hv, hvS⟩ := hmem
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact hxS hvS
  · exact hyS hvS

/-- The cyclic-cut node adapter preserves strict nesting. All widths and
geometry receipts are the original ones; no fresh-edge receipt is assumed. -/
theorem cyclicCut_nodes_strict [G.LocallyFinite]
    {oldCut newCut : Finset G.edgeSet}
    (old : CyclicEdgeCutRealization G oldCut)
    (new : CyclicEdgeCutRealization G newCut)
    (hcubic : ∀ v, (incidentEdgeFinset G v).card = 3)
    (hOldSide : (G.induce old.side).Connected)
    (hOldComplement : (G.induce (fun v => ¬ old.side v)).Connected)
    (hNewSide : (G.induce new.side).Connected)
    (hNewComplement : (G.induce (fun v => ¬ new.side v)).Connected)
    (bound : Nat) (hOldCard : oldCut.card ≤ bound) (hNewCard : newCut.card ≤ bound)
    (hST : ∀ v, old.side v → new.side v)
    (hnew : ∃ v, new.side v ∧ ¬ old.side v) :
    (old.toConnectedShoreNodeOfConnectedSides hcubic hOldSide hOldComplement bound hOldCard).shore ⊂
      (new.toConnectedShoreNodeOfConnectedSides hcubic hNewSide hNewComplement bound hNewCard).shore := by
  obtain ⟨v, hv, _⟩ := new.houtside_cycle
  exact incidentEdgeShore_ssubset hST hnew ⟨v, hv⟩ hOldComplement.preconnected

end Finite

end NestedCyclicCutStrictness
end Mettapedia.GraphTheory.FourColor
