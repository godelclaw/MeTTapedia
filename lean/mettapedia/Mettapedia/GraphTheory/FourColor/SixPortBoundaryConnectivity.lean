import Mettapedia.GraphTheory.FourColor.MatchingBoundaryConnectivity

/-!
# Connectivity behind six ports without distinct attachments

In a cubic graph with cyclic cuts of size at least four, a nonempty induced
component opposite a cycle has at least three outgoing edges. If it contains
an edge, it has at least four. Consequently a side with at most six ports
and an internal edge is connected. More than two side vertices already force
such an edge by the cubic dart count.

The conclusion permits repeated boundary endpoints and requires no embedding
or colouring. The cycle in the complement is essential to the cut argument.
-/

namespace Mettapedia.GraphTheory.FourColor.SixPortBoundaryConnectivity

open SimpleGraph GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24CyclicThreeCutConnectedSides RootedCutSaturation
open MatchingBoundaryConnectivity

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A connected cubic side which were a tree would have exactly two more
ports than vertices. A smaller boundary therefore witnesses a cycle. -/
theorem hasCycle_of_boundary_card_lt_card_add_two
    (hcubic : G.IsRegularOfDegree 3) (side : V → Prop)
    (hconnected : (G.induce {v | side v}).Connected)
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
    have hv' : v ∈ cycle.support.map inclusion := Walk.support_map inclusion cycle ▸ hv
    obtain ⟨w, _, hw⟩ := List.mem_map.mp hv'
    exact hw ▸ w.2
  have ht := (show (G.induce {v | side v}).IsTree from ⟨hconnected, hacyclic⟩).card_edgeFinset
  have hp := Fintype.card_congr (sideDartEquivInternalSumCrossing G side)
  rw [Fintype.card_sum] at hp
  have hs := card_sideDart_eq_three_mul hcubic side
  have hi := card_internalSideDart_eq_twice_card_edges (G := G) side
  have hc : Fintype.card ↑({v | side v} : Set V) = Fintype.card {v // side v} := rfl
  omega

variable (side : V → Prop) (root : V) (hroot : side root)

theorem component_crossing_mem_edges
    (d : CrossingSideDart G (inducedReachableSide G side root hroot)) :
    (⟨d.1.edge, d.1.edge_mem⟩ : G.edgeSet) ∈ componentEdges side root hroot := by
  apply (mem_componentEdges side root hroot _).mpr
  exact ⟨d.1.fst, d.1.snd, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _, d.2⟩

theorem component_not_cycle_of_card_le_three
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hother : HasCycleOnSide G (fun v => ¬ side v))
    (hcard : (componentPorts (G := G) side root hroot).card ≤ 3) :
    ¬ HasCycleOnSide G (inducedReachableSide G side root hroot) := by
  intro hcycle
  have he : (componentEdges (G := G) side root hroot).card ≤
      (componentPorts (G := G) side root hroot).card := Finset.card_image_le
  let cut : SmallCyclicEdgeCut G :=
    { edgeCut := componentEdges side root hroot
      side := inducedReachableSide G side root hroot
      hcut_eq := mem_componentEdges side root hroot
      hcard_le_four := by omega
      hinside_cycle := hcycle
      houtside_cycle := hother.mono (fun _ hn hc => hn hc.choose) }
  have hc := hcyclic cut
  change 4 ≤ (componentEdges (G := G) side root hroot).card at hc
  omega

theorem three_le_componentPorts
    (hcubic : G.IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hother : HasCycleOnSide G (fun v => ¬ side v)) :
    3 ≤ (componentPorts (G := G) side root hroot).card := by
  by_contra hn
  have he : (componentEdges (G := G) side root hroot).card ≤
      (componentPorts (G := G) side root hroot).card := Finset.card_image_le
  apply component_not_cycle_of_card_le_three side root hroot hcyclic hother (by omega)
  exact hasCycleOnSide_of_cubic_of_connected_induce_of_crossing_le_two hcubic _
    ⟨root, inducedReachableSide_root (G := G) side root hroot⟩
    (induce_inducedReachableSide_connected side root hroot)
    (componentEdges side root hroot) (by omega)
    (component_crossing_mem_edges side root hroot)

theorem four_le_componentPorts_of_adj
    (hcubic : G.IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hother : HasCycleOnSide G (fun v => ¬ side v))
    {next : V} (hnext : side next) (hadj : G.Adj root next) :
    4 ≤ (componentPorts (G := G) side root hroot).card := by
  classical
  by_contra hn
  have he : (componentEdges (G := G) side root hroot).card ≤
      (componentPorts (G := G) side root hroot).card := Finset.card_image_le
  have hcase := hasCycleOnSide_or_card_eq_one_of_local_cubic_of_connected_induce_of_crossing_le_three
    (inducedReachableSide G side root hroot) (fun v _ => hcubic v)
    ⟨root, inducedReachableSide_root (G := G) side root hroot⟩
    (induce_inducedReachableSide_connected side root hroot)
    (componentEdges side root hroot) (by omega)
    (component_crossing_mem_edges side root hroot)
  rcases hcase with hcycle | hone
  · exact component_not_cycle_of_card_le_three side root hroot hcyclic hother (by omega) hcycle
  · have : Subsingleton {v // inducedReachableSide G side root hroot v} :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hnxt : inducedReachableSide G side root hroot next :=
      ⟨hnext, SimpleGraph.Adj.reachable (G := G.induce {v | side v}) hadj⟩
    exact hadj.ne (congrArg Subtype.val
      (Subsingleton.elim (⟨root, inducedReachableSide_root (G := G) side root hroot⟩ :
        {v // inducedReachableSide G side root hroot v}) ⟨next, hnxt⟩))

omit root hroot in
/-- An internal edge costs four ports in its component; a second component
would cost at least three more. The endpoints of the six ports may repeat. -/
theorem connected_of_internal_edge_of_boundary_card_le_six
    (hcubic : G.IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hother : HasCycleOnSide G (fun v => ¬ side v))
    (hcard : Fintype.card (CrossingSideDart G side) ≤ 6)
    (hedge : ∃ u v, side u ∧ side v ∧ G.Adj u v) :
    (G.induce {v | side v}).Connected := by
  classical
  obtain ⟨root, next, hroot, hnext, hadj⟩ := hedge
  have hfour := four_le_componentPorts_of_adj side root hroot hcubic hcyclic hother hnext hadj
  have reaches : ∀ v : {v // side v},
      (G.induce {v | side v}).Reachable ⟨root, hroot⟩ v := by
    intro v
    by_contra hn
    have hthree := three_le_componentPorts side v.1 v.2 hcubic hcyclic hother
    have hd := components_disjoint side hroot v.2 hn
    have disj : Disjoint (componentPorts (G := G) side root hroot)
        (componentPorts (G := G) side v.1 v.2) := by
      rw [Finset.disjoint_left]
      intro d ha hb
      exact hd d.1.fst (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    have hb := Finset.card_le_univ
      (s := componentPorts (G := G) side root hroot ∪ componentPorts side v.1 v.2)
    rw [Finset.card_union_of_disjoint disj] at hb
    omega
  exact { nonempty := ⟨⟨root, hroot⟩⟩
          preconnected := fun u v => (reaches u).symm.trans (reaches v) }

omit root hroot in
/-- In a cubic graph, more than two vertices behind at most six ports force
an internal edge. The complementary cycle and cyclic cut bound then force
the entire side to be connected. -/
theorem connected_of_two_lt_card_of_boundary_card_le_six
    (hcubic : G.IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hother : HasCycleOnSide G (fun v => ¬ side v))
    (hcard : Fintype.card (CrossingSideDart G side) ≤ 6)
    (hsize : 2 < Fintype.card {v // side v}) :
    (G.induce {v | side v}).Connected := by
  have hp := Fintype.card_congr (sideDartEquivInternalSumCrossing G side)
  rw [Fintype.card_sum] at hp
  have hs := card_sideDart_eq_three_mul hcubic side
  have hi : 0 < Fintype.card (InternalSideDart G side) := by omega
  obtain ⟨d⟩ := Fintype.card_pos_iff.mp hi
  exact connected_of_internal_edge_of_boundary_card_le_six side hcubic hcyclic hother hcard
    ⟨d.1.fst, d.1.snd, d.2.1, d.2.2, d.1.adj⟩

end
end Mettapedia.GraphTheory.FourColor.SixPortBoundaryConnectivity
