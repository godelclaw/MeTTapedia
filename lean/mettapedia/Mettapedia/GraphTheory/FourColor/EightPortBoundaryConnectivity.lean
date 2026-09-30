import Mettapedia.GraphTheory.FourColor.SevenPortBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.CubicDualInternalSixConnectivity

/-!
# Connectivity behind eight ports in the internal-six normal form

A disconnected cubic side behind eight ports can consist of a cyclic
five-port component and one isolated vertex. Internal-six connectivity
bounds the cyclic component by five vertices when the opposite shore has
at least six. Thus seven vertices behind eight ports force connectivity.
The attachment vertices need not be distinct. No embedding is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.EightPortBoundaryConnectivity

open _root_.SimpleGraph GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24CyclicThreeCutConnectedSides RootedCutSaturation
open MatchingBoundaryConnectivity SixPortBoundaryConnectivity

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance eightConnectedEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

omit [DecidableEq V] in
private theorem ports_disjoint (side : V → Prop) {u v : V} (hu : side u) (hv : side v)
    (hne : ¬ (G.induce {w | side w}).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    Disjoint (componentPorts (G := G) side u hu) (componentPorts side v hv) := by
  classical
  rw [Finset.disjoint_left]
  intro d ha hb
  exact components_disjoint side hu hv hne d.1.fst
    (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

omit [DecidableEq V] in
/-- Seven side vertices and six complementary vertices exclude the only
disconnected eight-port possibility: a small cyclic component plus a point. -/
theorem connected_of_seven_le_card_of_boundary_card_le_eight
    (hcubic : G.IsRegularOfDegree 3) (hinternal : CubicDualInternallySixConnected G)
    (side : V → Prop) (hother : HasCycleOnSide G (fun v => ¬ side v))
    (hcard : Fintype.card (CrossingSideDart G side) ≤ 8)
    (hsize : 7 ≤ Fintype.card {v // side v})
    (hspace : 6 ≤ Fintype.card {v // ¬ side v}) :
    (G.induce {v | side v}).Connected := by
  classical
  have hc4 : CyclicEdgeConnectivityAtLeast G 4 := fun cut => by
    have hh := hinternal.1 cut
    change 5 ≤ cut.edgeCut.card at hh
    change 4 ≤ cut.edgeCut.card
    omega
  have hinside := CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
    hcubic side (Fintype.card_pos_iff.mp (by omega)) (by omega)
  obtain ⟨root, hroot, walk, hcycle, hs⟩ := hinside
  have hrootCycle := hasCycleOnSide_inducedReachableSide side root hroot walk hcycle hs
  let A := inducedReachableSide G side root hroot
  have hfive : 5 ≤ (componentPorts (G := G) side root hroot).card := by
    by_contra hn
    have he : (componentEdges (G := G) side root hroot).card ≤
        (componentPorts (G := G) side root hroot).card := Finset.card_image_le
    let cut : SmallCyclicEdgeCut G :=
      { edgeCut := componentEdges side root hroot
        side := A
        hcut_eq := mem_componentEdges side root hroot
        hcard_le_four := by omega
        hinside_cycle := hrootCycle
        houtside_cycle := hother.mono (fun _ hn hc => hn hc.choose) }
    have hh := hinternal.1 cut
    change 5 ≤ (componentEdges (G := G) side root hroot).card at hh
    omega
  have reaches : ∀ v : {v // side v},
      (G.induce {v | side v}).Reachable ⟨root, hroot⟩ v := by
    intro v
    by_contra hn
    let B := inducedReachableSide G side v.1 v.2
    have hthree := three_le_componentPorts side v.1 v.2 hcubic hc4 hother
    have hab := ports_disjoint side hroot v.2 hn
    have hb := Finset.card_le_univ
      (s := componentPorts (G := G) side root hroot ∪ componentPorts side v.1 v.2)
    rw [Finset.card_union_of_disjoint hab] at hb
    have hAports : (componentPorts (G := G) side root hroot).card ≤ 5 := by omega
    have hBports : (componentPorts (G := G) side v.1 v.2).card ≤ 3 := by omega
    have hAedges : (componentEdges (G := G) side root hroot).card ≤ 5 :=
      Finset.card_image_le.trans hAports
    let cut : CyclicEdgeCutRealization G (componentEdges side root hroot) :=
      { side := A
        hcut_eq := mem_componentEdges side root hroot
        hinside_cycle := hrootCycle
        houtside_cycle := hother.mono (fun _ hn hc => hn hc.choose) }
    have hsmall := cut.hasShoreOfSizeAtMost_five hinternal hAedges
    have hlarge : 6 ≤ (Finset.univ.filter (fun w => ¬ A w)).card := by
      have hh : (Finset.univ.filter (fun w => ¬ side w)).card ≤
          (Finset.univ.filter (fun w => ¬ A w)).card := by
        apply Finset.card_le_card
        intro w hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun ha => (Finset.mem_filter.mp hw).2 ha.choose⟩
      rw [Fintype.card_subtype] at hspace
      omega
    have hAsize : (Finset.univ.filter A).card ≤ 5 := by
      have ha : cut.vertexSide = Finset.univ.filter A := by ext w; simp [cut]
      have hb' : cut.compl.vertexSide = Finset.univ.filter (fun w => ¬ A w) := by
        ext w; simp [CyclicEdgeCutRealization.compl, cut]
      rw [CyclicEdgeCutRealization.HasShoreOfSizeAtMost, ha, hb'] at hsmall
      omega
    have hBsize : (Finset.univ.filter B).card = 1 := by
      have he : (componentEdges (G := G) side v.1 v.2).card ≤ 3 :=
        Finset.card_image_le.trans hBports
      have hcase := hasCycleOnSide_or_card_eq_one_of_local_cubic_of_connected_induce_of_crossing_le_three
        B (fun w _ => hcubic w)
        ⟨v.1, inducedReachableSide_root (G := G) side v.1 v.2⟩
        (induce_inducedReachableSide_connected side v.1 v.2)
        (componentEdges side v.1 v.2) he (component_crossing_mem_edges side v.1 v.2)
      have hone := hcase.resolve_left
        (component_not_cycle_of_card_le_three side v.1 v.2 hc4 hother hBports)
      simpa [Fintype.card_subtype] using hone
    have hcover : Finset.univ.filter side ⊆ Finset.univ.filter A ∪ Finset.univ.filter B := by
      intro w hw
      have hsw := (Finset.mem_filter.mp hw).2
      by_cases ha : A w
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
      by_cases hb' : B w
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'⟩)
      have hwa : ¬ (G.induce {x | side x}).Reachable ⟨root, hroot⟩ ⟨w, hsw⟩ :=
        fun hp => ha ⟨hsw, hp⟩
      have hwb : ¬ (G.induce {x | side x}).Reachable v ⟨w, hsw⟩ :=
        fun hp => hb' ⟨hsw, hp⟩
      have hwthree := three_le_componentPorts side w hsw hcubic hc4 hother
      have hac := ports_disjoint side hroot hsw hwa
      have hbc := ports_disjoint side v.2 hsw hwb
      have hh := Finset.card_le_univ (s :=
        (componentPorts (G := G) side root hroot ∪ componentPorts side v.1 v.2) ∪
          componentPorts side w hsw)
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hac, hbc⟩),
        Finset.card_union_of_disjoint hab] at hh
      omega
    have hbound := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have hcount : Fintype.card {v // side v} = (Finset.univ.filter side).card :=
      Fintype.card_of_subtype _ (by intro w; simp)
    rw [hcount] at hsize
    omega
  exact { nonempty := ⟨⟨root, hroot⟩⟩
          preconnected := fun u v => (reaches u).symm.trans (reaches v) }

end
end Mettapedia.GraphTheory.FourColor.EightPortBoundaryConnectivity
