import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicSmallBoundaryCycle

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CubicTwoEdgeCyclicCut

open GoertzelV24CubicSmallBoundaryCycle
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- An edge crossing a component of the graph obtained by deleting two edges
must be one of those two deleted edges. -/
theorem edge_mem_pair_of_crosses_delete_component
    (first second : G.edgeSet)
    (component :
      (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).ConnectedComponent)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) edge) :
    edge ∈ ({first, second} : Finset G.edgeSet) := by
  classical
  rcases hcross with ⟨u, v, huEdge, hvEdge, huComponent, hvComponent⟩
  have huv : u ≠ v := by
    intro heq
    exact hvComponent (heq ▸ huComponent)
  have hedgeValue : edge.1 = s(u, v) :=
    sym2_eq_mk_of_mem_of_mem_of_ne huEdge hvEdge huv
  by_contra hnotMem
  have hnotFirst : edge.1 ≠ first.1 := by
    intro heq
    apply hnotMem
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inl (Subtype.ext heq)
  have hnotSecond : edge.1 ≠ second.1 := by
    intro heq
    apply hnotMem
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Subtype.ext heq)
  have hadj : G.Adj u v :=
    (SimpleGraph.mem_edgeSet G).1 (by simpa [hedgeValue] using edge.2)
  have hdeleteAdj :
      (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).Adj u v := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hadj, ?_⟩
    simp [← hedgeValue, hnotFirst, hnotSecond]
  exact hvComponent
    ((component.mem_supp_congr_adj hdeleteAdj).mp huComponent)

/-- Every outgoing dart of a deleted-graph component is supported on the two
deleted edges. -/
theorem crossingSideDart_edge_mem_pair_of_delete_component
    (first second : G.edgeSet)
    (component :
      (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).ConnectedComponent)
    (dart : CrossingSideDart G (fun vertex => vertex ∈ component.supp)) :
    (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈
      ({first, second} : Finset G.edgeSet) := by
  apply edge_mem_pair_of_crosses_delete_component first second component
  refine ⟨dart.1.fst, dart.1.snd, ?_, ?_, dart.2.1, dart.2.2⟩
  · change dart.1.fst ∈ s(dart.1.fst, dart.1.snd)
    simp
  · change dart.1.snd ∈ s(dart.1.fst, dart.1.snd)
    simp

/-- A component of a two-edge deletion remains connected when it is induced
inside the original graph. -/
theorem connected_induce_component_of_delete_pair
    (first second : G.edgeSet)
    (component :
      (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).ConnectedComponent) :
    (G.induce component.supp).Connected := by
  exact component.connected_toSimpleGraph.mono (by
    intro left right hadj
    exact (G.deleteEdges_le ({first.1, second.1} : Set (Sym2 V))) hadj)

/-- If deleting two edges disconnects a connected cubic graph, the two edges
support a cyclic edge cut of size at most two. -/
theorem exists_smallCyclicEdgeCut_card_le_two_of_not_connected_deleteEdges_pair
    (hregular : G.IsRegularOfDegree 3) (hconnected : G.Connected)
    (first second : G.edgeSet)
    (hdelete :
      ¬ (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).Connected) :
    ∃ cut : SmallCyclicEdgeCut G, cut.edgeCut.card ≤ 2 := by
  classical
  let deleted := G.deleteEdges ({first.1, second.1} : Set (Sym2 V))
  letI : Nonempty V := hconnected.nonempty
  have hnotPreconnected : ¬ deleted.Preconnected := by
    intro hpreconnected
    exact hdelete ⟨hpreconnected⟩
  rw [SimpleGraph.Preconnected] at hnotPreconnected
  push Not at hnotPreconnected
  rcases hnotPreconnected with ⟨insideVertex, outsideVertex, hnotReachable⟩
  let inside :=
    (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).connectedComponentMk
      insideVertex
  let outside :=
    (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).connectedComponentMk
      outsideVertex
  have hcomponents : inside ≠ outside := by
    intro heq
    exact hnotReachable (ConnectedComponent.exact heq)
  have hinsideCycle : HasCycleOnSide G
      (fun vertex => vertex ∈ inside.supp) := by
    refine hasCycleOnSide_of_cubic_of_connected_induce_of_crossing_le_two
      hregular (fun vertex => vertex ∈ inside.supp) inside.nonempty_supp
      (connected_induce_component_of_delete_pair first second inside)
      ({first, second} : Finset G.edgeSet) Finset.card_le_two ?_
    exact crossingSideDart_edge_mem_pair_of_delete_component first second inside
  have houtsideComponentCycle : HasCycleOnSide G
      (fun vertex => vertex ∈ outside.supp) := by
    refine hasCycleOnSide_of_cubic_of_connected_induce_of_crossing_le_two
      hregular (fun vertex => vertex ∈ outside.supp) outside.nonempty_supp
      (connected_induce_component_of_delete_pair first second outside)
      ({first, second} : Finset G.edgeSet) Finset.card_le_two ?_
    exact crossingSideDart_edge_mem_pair_of_delete_component first second outside
  have houtsideCycle : HasCycleOnSide G
      (fun vertex => ¬ vertex ∈ inside.supp) :=
    HasCycleOnSide.mono (fun vertex houtside hinside =>
      hcomponents (ConnectedComponent.eq_of_common_vertex hinside houtside))
      houtsideComponentCycle
  let edgeCut := Finset.univ.filter fun edge : G.edgeSet =>
    EdgeCrossesVertexSide G (fun vertex => vertex ∈ inside.supp) edge
  have hedgeCutSubset :
      edgeCut ⊆ ({first, second} : Finset G.edgeSet) := by
    intro edge hedge
    simp only [edgeCut, Finset.mem_filter, Finset.mem_univ, true_and] at hedge
    exact edge_mem_pair_of_crosses_delete_component first second inside edge hedge
  have hedgeCutCard : edgeCut.card ≤ 2 := by
    calc
      edgeCut.card ≤ ({first, second} : Finset G.edgeSet).card :=
        Finset.card_le_card hedgeCutSubset
      _ ≤ 2 := Finset.card_le_two
  let cut : SmallCyclicEdgeCut G :=
    { edgeCut := edgeCut
      side := fun vertex => vertex ∈ inside.supp
      hcut_eq := fun edge => by simp [edgeCut]
      hcard_le_four := le_trans hedgeCutCard (by omega)
      hinside_cycle := hinsideCycle
      houtside_cycle := houtsideCycle }
  exact ⟨cut, hedgeCutCard⟩

end

end GoertzelV24CubicTwoEdgeCyclicCut

end Mettapedia.GraphTheory.FourColor
