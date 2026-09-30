import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalTriangleFree
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFourEdgeConnectedSides

/-!
# Boundary size opposite a cycle in a cubic graph

A nonempty acyclic side has at least two more outgoing edges than vertices,
even if it is disconnected. Thus a cyclically five-edge-connected cubic
graph cannot separate a cycle from three or more vertices by four edges.
No embedding, distinct exterior attachments, or colouring data are needed.
-/

namespace Mettapedia.GraphTheory.FourColor.CyclicFiveBoundary

open _root_.SimpleGraph GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24MinimalTriangleFree GoertzelV24CubicFourEdgeConnectedSides

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance cyclicFiveBoundaryEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A forest has at most one fewer edge than vertices, without a
connectedness assumption. Cubic degree counting then forces a cycle. -/
theorem hasCycle_of_boundary_card_lt_card_add_two
    (hcubic : G.IsRegularOfDegree 3) (side : V → Prop)
    (hne : Nonempty {v // side v})
    (hcard : Fintype.card (CrossingSideDart G side) < Fintype.card {v // side v} + 2) :
    HasCycleOnSide G side := by
  classical
  by_contra hnoCycle
  have hacyclic : (G.induce {v | side v}).IsAcyclic := by
    intro vertex cycle hcycle
    apply hnoCycle
    let inclusion := (SimpleGraph.Embedding.induce (G := G) {v | side v}).toHom
    refine ⟨vertex.1, vertex.2, cycle.map inclusion, hcycle.map Subtype.val_injective, ?_⟩
    intro v hv
    have hv' : v ∈ cycle.support.map inclusion := SimpleGraph.Walk.support_map inclusion cycle ▸ hv
    obtain ⟨w, _, hw⟩ := List.mem_map.mp hv'
    exact hw ▸ w.2
  have hf := natCard_edgeSet_add_one_le_of_isAcyclic (G.induce {v | side v}) hne hacyclic
  have hs := card_crossingEdgeFinset_add_twice_internal_eq_three_mul (G := G)
    (fun v => (degree_instance_independent v _ _).trans (hcubic v)) side
  rw [card_crossingEdgeFinset_eq_card_crossingSideDart] at hs
  simp only [Nat.card_eq_fintype_card] at hf hs
  have hc : Fintype.card ↑({v | side v} : Set V) = Fintype.card {v // side v} := rfl
  omega

/-- Cyclic connectivity also controls a boundary when a cycle is known
only on one side: three exterior vertices suffice in a cubic graph. -/
theorem five_le_crossing_card
    (hcubic : G.IsRegularOfDegree 3) (hcyclic : CyclicallyFiveEdgeConnected G)
    (side : V → Prop) (hinside : HasCycleOnSide G side)
    (hsize : 3 ≤ Fintype.card {v // ¬ side v}) :
    5 ≤ Fintype.card (CrossingSideDart G side) := by
  classical
  by_contra hn
  have hb : Fintype.card (CrossingSideDart G side) ≤ 4 := by omega
  have hcompl : Fintype.card (CrossingSideDart G (fun v => ¬ side v)) =
      Fintype.card (CrossingSideDart G side) := by
    rw [← card_crossingEdgeFinset_eq_card_crossingSideDart,
      ← card_crossingEdgeFinset_eq_card_crossingSideDart, crossingEdgeFinset_compl]
  have houtside : HasCycleOnSide G (fun v => ¬ side v) :=
    hasCycle_of_boundary_card_lt_card_add_two hcubic _
      (Fintype.card_pos_iff.mp (by omega)) (by rw [hcompl]; omega)
  let cut : SmallCyclicEdgeCut G :=
    { edgeCut := crossingEdgeFinset G side
      side := side
      hcut_eq := mem_crossingEdgeFinset_iff side
      hcard_le_four := by rw [card_crossingEdgeFinset_eq_card_crossingSideDart]; exact hb
      hinside_cycle := hinside
      houtside_cycle := houtside }
  have hfive := hcyclic cut
  change 5 ≤ (crossingEdgeFinset G side).card at hfive
  rw [card_crossingEdgeFinset_eq_card_crossingSideDart] at hfive
  omega

end
end Mettapedia.GraphTheory.FourColor.CyclicFiveBoundary
