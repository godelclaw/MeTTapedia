import Mettapedia.GraphTheory.FourColor.RootedCutSaturation

/-!
# Connectivity behind a small boundary with distinct endpoints

In a finite cubic graph, an induced connected component with at most one
outgoing dart at each vertex contains a cycle: the cubic dart count rules out
a tree. If cyclic cuts have at least four edges, two such components require
at least eight boundary edges. A nonempty side with fewer than eight ports
and distinct attachment vertices is therefore connected.

Only the endpoints on the selected side need be distinct. No embedding or
colouring assumption occurs in this graph-theoretic criterion.
-/

namespace Mettapedia.GraphTheory.FourColor.MatchingBoundaryConnectivity

open SimpleGraph GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24CyclicThreeCutConnectedSides RootedCutSaturation

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A connected cubic side with distinct outgoing endpoints cannot be a tree. -/
theorem hasCycle_of_injective_boundary
    (hcubic : G.IsRegularOfDegree 3) (side : V → Prop)
    (hconnected : (G.induce {v | side v}).Connected)
    (hinj : Function.Injective (fun d : CrossingSideDart G side => d.1.fst)) :
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
  have hb : Fintype.card (CrossingSideDart G side) ≤ Fintype.card {v // side v} :=
    Fintype.card_le_of_injective (fun d => (⟨d.1.fst, d.2.1⟩ : {v // side v}))
      (fun _ _ he => hinj (congrArg Subtype.val he))
  have hc : Fintype.card ↑({v | side v} : Set V) = Fintype.card {v // side v} := rfl
  omega

variable (side : V → Prop) (root : V) (hroot : side root)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A component's outgoing dart already leaves the original side. -/
theorem component_dart_snd_not_side
    (d : CrossingSideDart G (inducedReachableSide G side root hroot)) :
    ¬ side d.1.snd := by
  intro hs
  apply d.2.2
  refine ⟨hs, d.2.1.choose_spec.trans ?_⟩
  exact SimpleGraph.Adj.reachable (G := G.induce {v | side v}) d.1.adj

def componentDart (d : CrossingSideDart G (inducedReachableSide G side root hroot)) :
    CrossingSideDart G side :=
  ⟨d.1, d.2.1.choose, component_dart_snd_not_side side root hroot d⟩

/-- Every component inherits the same distinct-endpoint condition. -/
theorem component_hasCycle (hcubic : G.IsRegularOfDegree 3)
    (hinj : Function.Injective (fun d : CrossingSideDart G side => d.1.fst)) :
    HasCycleOnSide G (inducedReachableSide G side root hroot) := by
  apply hasCycle_of_injective_boundary hcubic _
    (induce_inducedReachableSide_connected side root hroot)
  intro a b he
  have hd : componentDart side root hroot a = componentDart side root hroot b := hinj he
  apply Subtype.ext
  exact congrArg (fun d : CrossingSideDart G side => d.1) hd

def componentPorts : Finset (CrossingSideDart G side) :=
  by
    classical
    exact Finset.univ.filter (fun d => inducedReachableSide G side root hroot d.1.fst)

def componentEdges : Finset G.edgeSet :=
  by
    classical
    exact (componentPorts (G := G) side root hroot).image
      (fun d => ⟨d.1.edge, d.1.edge_mem⟩)

theorem mem_componentEdges (e : G.edgeSet) :
    e ∈ componentEdges (G := G) side root hroot ↔
      EdgeCrossesVertexSide G (inducedReachableSide G side root hroot) e := by
  classical
  constructor
  · rintro he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact ⟨d.1.fst, d.1.snd, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _,
      (Finset.mem_filter.mp hd).2, fun hc => d.2.2 hc.choose⟩
  · rintro ⟨u, v, hu, hv, hc, hn⟩
    have hne : u ≠ v := fun he => hn (he ▸ hc)
    have he : e.1 = s(u, v) := sym2_eq_mk_of_mem_of_mem_of_ne hu hv hne
    let d : G.Dart := ⟨(u, v), (SimpleGraph.mem_edgeSet G).mp (he ▸ e.2)⟩
    let cd : CrossingSideDart G (inducedReachableSide G side root hroot) := ⟨d, hc, hn⟩
    let bd := componentDart side root hroot cd
    apply Finset.mem_image.mpr
    refine ⟨bd, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, ?_⟩
    exact Subtype.ext he.symm

theorem four_le_componentPorts
    (hcubic : G.IsRegularOfDegree 3) (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hinj : Function.Injective (fun d : CrossingSideDart G side => d.1.fst))
    (hother : HasCycleOnSide G (fun v => ¬ inducedReachableSide G side root hroot v)) :
    4 ≤ (componentPorts (G := G) side root hroot).card := by
  classical
  have he : (componentEdges (G := G) side root hroot).card ≤
      (componentPorts (G := G) side root hroot).card := Finset.card_image_le
  by_contra hn
  let cut : SmallCyclicEdgeCut G :=
    { edgeCut := componentEdges side root hroot
      side := inducedReachableSide G side root hroot
      hcut_eq := mem_componentEdges side root hroot
      hcard_le_four := by omega
      hinside_cycle := component_hasCycle side root hroot hcubic hinj
      houtside_cycle := hother }
  have h := hcyclic cut
  change 4 ≤ (componentEdges (G := G) side root hroot).card at h
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem components_disjoint {first second : V} (hf : side first) (hs : side second)
    (hne : ¬ (G.induce {v | side v}).Reachable ⟨first, hf⟩ ⟨second, hs⟩) :
    ∀ v, inducedReachableSide G side first hf v →
      ¬ inducedReachableSide G side second hs v := by
  intro v ha hb
  exact hne (ha.choose_spec.trans hb.choose_spec.symm)

/-- The boundary condition is local: no selected-side vertex owns two ports.
Together with cyclic four-edge-connectivity and fewer than eight ports it
forces the entire selected side to be connected. -/
theorem connected_of_boundary_card_lt_eight
    (hcubic : G.IsRegularOfDegree 3) (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hnonempty : ∃ v, side v)
    (hinj : Function.Injective (fun d : CrossingSideDart G side => d.1.fst))
    (hcard : Fintype.card (CrossingSideDart G side) < 8) :
    (G.induce {v | side v}).Connected := by
  classical
  refine { nonempty := ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩, preconnected := ?_ }
  intro first second
  by_contra hn
  have hd := components_disjoint side first.2 second.2 hn
  have hds := components_disjoint side second.2 first.2 (fun h => hn h.symm)
  have cf := component_hasCycle side first.1 first.2 hcubic hinj
  have cs := component_hasCycle side second.1 second.2 hcubic hinj
  have hf := four_le_componentPorts side first.1 first.2 hcubic hcyclic hinj
    (cs.mono (fun v hv h => hd v h hv))
  have hs := four_le_componentPorts side second.1 second.2 hcubic hcyclic hinj
    (cf.mono (fun v hv h => hds v h hv))
  have disj : Disjoint (componentPorts (G := G) side first.1 first.2)
      (componentPorts (G := G) side second.1 second.2) := by
    rw [Finset.disjoint_left]
    intro d ha hb
    exact hd d.1.fst (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have hb := Finset.card_le_univ
    (s := componentPorts (G := G) side first.1 first.2 ∪ componentPorts side second.1 second.2)
  rw [Finset.card_union_of_disjoint disj] at hb
  omega

end
end Mettapedia.GraphTheory.FourColor.MatchingBoundaryConnectivity
