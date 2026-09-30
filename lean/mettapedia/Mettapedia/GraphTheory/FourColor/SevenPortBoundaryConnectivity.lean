import Mettapedia.GraphTheory.FourColor.SixPortBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.CyclicFiveBoundary

/-!
# Connectivity behind seven ports without distinct attachments

In a cyclically five-edge-connected cubic graph, a component containing a
cycle costs at least five ports when the opposite shore contains a cycle.
Every other component costs at least three. Fewer than eight ports therefore
force connectivity. Six vertices behind seven ports already force a cycle.
-/

namespace Mettapedia.GraphTheory.FourColor.SevenPortBoundaryConnectivity

open _root_.SimpleGraph GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24CyclicThreeCutConnectedSides RootedCutSaturation
open MatchingBoundaryConnectivity SixPortBoundaryConnectivity

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance sevenConnectedEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A cyclic component costs five ports; a second component would cost
three more. Neither shore needs distinct attachment endpoints. -/
theorem connected_of_cycles_of_boundary_card_lt_eight
    (hcubic : G.IsRegularOfDegree 3) (hcyclic : CyclicallyFiveEdgeConnected G)
    (side : V → Prop) (hinside : HasCycleOnSide G side)
    (hother : HasCycleOnSide G (fun v => ¬side v))
    (hcard : Fintype.card (CrossingSideDart G side) < 8) :
    (G.induce {v | side v}).Connected := by
  classical
  obtain ⟨root, hroot, walk, hcycle, hs⟩ := hinside
  have hrootCycle := hasCycleOnSide_inducedReachableSide side root hroot walk hcycle hs
  have hfive : 5 ≤ (componentPorts (G := G) side root hroot).card := by
    by_contra hn
    have he : (componentEdges (G := G) side root hroot).card ≤
        (componentPorts (G := G) side root hroot).card := Finset.card_image_le
    let cut : SmallCyclicEdgeCut G :=
      { edgeCut := componentEdges side root hroot
        side := inducedReachableSide G side root hroot
        hcut_eq := mem_componentEdges side root hroot
        hcard_le_four := by omega
        hinside_cycle := hrootCycle
        houtside_cycle := hother.mono (fun _ hn hc => hn hc.choose) }
    have hc := hcyclic cut
    change 5 ≤ (componentEdges (G := G) side root hroot).card at hc
    omega
  have hc4 : CyclicEdgeConnectivityAtLeast G 4 := fun cut => by
    have hc := hcyclic cut
    change 5 ≤ cut.edgeCut.card at hc
    change 4 ≤ cut.edgeCut.card
    omega
  have reaches : ∀ v : {v // side v},
      (G.induce {v | side v}).Reachable ⟨root, hroot⟩ v := by
    intro v
    by_contra hn
    have hthree := three_le_componentPorts side v.1 v.2 hcubic hc4 hother
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

/-- Cubic forest counting supplies the cycle, so six side vertices suffice. -/
theorem connected_of_six_le_card_of_boundary_card_le_seven
    (hcubic : G.IsRegularOfDegree 3) (hcyclic : CyclicallyFiveEdgeConnected G)
    (side : V → Prop) (hother : HasCycleOnSide G (fun v => ¬side v))
    (hcard : Fintype.card (CrossingSideDart G side) ≤ 7)
    (hsize : 6 ≤ Fintype.card {v // side v}) :
    (G.induce {v | side v}).Connected := by
  apply connected_of_cycles_of_boundary_card_lt_eight hcubic hcyclic side _ hother (by omega)
  exact CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two hcubic side
    (Fintype.card_pos_iff.mp (by omega)) (by omega)

end
end Mettapedia.GraphTheory.FourColor.SevenPortBoundaryConnectivity
