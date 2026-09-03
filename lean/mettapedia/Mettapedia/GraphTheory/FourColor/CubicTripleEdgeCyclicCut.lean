import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicTwoEdgeCyclicCut

/-!
# Deleting three edges of a cubic graph

If deleting three edges disconnects a connected cubic graph, then either
the three edges support a cyclic edge cut of size at most three, or some
vertex carries exactly those three edges.  The dichotomy is the sharp
degree-count fact: an acyclic side of the split would be a tree whose
crossing count exceeds three unless it is a single vertex.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24CubicSmallBoundaryCycle
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- An edge crossing a component of the graph obtained by deleting three
edges must be one of those three. -/
theorem edge_mem_triple_of_crosses_delete_component
    (first second third : G.edgeSet)
    (component :
      (G.deleteEdges
        ({first.1, second.1, third.1} : Set (Sym2 V))).ConnectedComponent)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) edge) :
    edge ∈ ({first, second, third} : Finset G.edgeSet) := by
  classical
  rcases hcross with ⟨u, v, huEdge, hvEdge, huComponent, hvComponent⟩
  have huv : u ≠ v := by
    intro heq
    exact hvComponent (heq ▸ huComponent)
  have hedgeValue : edge.1 = s(u, v) :=
    sym2_eq_mk_of_mem_of_mem_of_ne huEdge hvEdge huv
  by_contra hnotMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnotMem
  push Not at hnotMem
  have hadj : G.Adj u v :=
    (SimpleGraph.mem_edgeSet G).1 (by simpa [hedgeValue] using edge.2)
  have hdeleteAdj :
      (G.deleteEdges ({first.1, second.1, third.1} : Set (Sym2 V))).Adj u v := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hadj, ?_⟩
    have hnotFirst : edge.1 ≠ first.1 :=
      fun heq => hnotMem.1 (Subtype.ext heq)
    have hnotSecond : edge.1 ≠ second.1 :=
      fun heq => hnotMem.2.1 (Subtype.ext heq)
    have hnotThird : edge.1 ≠ third.1 :=
      fun heq => hnotMem.2.2 (Subtype.ext heq)
    simp [← hedgeValue, hnotFirst, hnotSecond, hnotThird]
  exact hvComponent
    ((component.mem_supp_congr_adj hdeleteAdj).mp huComponent)

/-- Every outgoing dart of a triple-deletion component is supported on the
three deleted edges. -/
theorem crossingSideDart_edge_mem_triple_of_delete_component
    (first second third : G.edgeSet)
    (component :
      (G.deleteEdges
        ({first.1, second.1, third.1} : Set (Sym2 V))).ConnectedComponent)
    (dart : CrossingSideDart G (fun vertex => vertex ∈ component.supp)) :
    (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈
      ({first, second, third} : Finset G.edgeSet) := by
  apply edge_mem_triple_of_crosses_delete_component first second third
    component
  refine ⟨dart.1.fst, dart.1.snd, ?_, ?_, dart.2.1, dart.2.2⟩
  · change dart.1.fst ∈ s(dart.1.fst, dart.1.snd)
    simp
  · change dart.1.snd ∈ s(dart.1.fst, dart.1.snd)
    simp

/-- A component of a three-edge deletion remains connected inside the
original graph. -/
theorem connected_induce_component_of_delete_triple
    (first second third : G.edgeSet)
    (component :
      (G.deleteEdges
        ({first.1, second.1, third.1} : Set (Sym2 V))).ConnectedComponent) :
    (G.induce component.supp).Connected := by
  exact component.connected_toSimpleGraph.mono (by
    intro left right hadj
    exact (G.deleteEdges_le
      ({first.1, second.1, third.1} : Set (Sym2 V))) hadj)

/-- A single-vertex side with all outgoing darts on the deleted triple
carries exactly those edges. -/
theorem forall_incident_mem_triple_of_card_eq_one
    (first second third : G.edgeSet)
    (side : V → Prop) [Fintype {vertex : V // side vertex}]
    (hcard : Fintype.card {vertex : V // side vertex} = 1)
    (hcrossing : ∀ dart : CrossingSideDart G side,
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈
        ({first, second, third} : Finset G.edgeSet)) :
    ∃ vertex : V, side vertex ∧
      ∀ edge : G.edgeSet, vertex ∈ (edge.1 : Sym2 V) →
        edge ∈ ({first, second, third} : Finset G.edgeSet) := by
  classical
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨⟨vertex, hvertex⟩, hunique⟩
  refine ⟨vertex, hvertex, ?_⟩
  intro edge hincident
  rcases Sym2.mem_iff_exists.mp hincident with ⟨other, hother⟩
  have hadj : G.Adj vertex other :=
    (SimpleGraph.mem_edgeSet G).1 (by
      rw [SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeSet]
      simpa [hother] using edge.2)
  have hotherNotSide : ¬ side other := by
    intro hotherSide
    have hsame := hunique ⟨other, hotherSide⟩
    have hvertexEq : other = vertex := congrArg Subtype.val hsame
    exact G.irrefl (hvertexEq ▸ hadj)
  let dart : CrossingSideDart G side :=
    ⟨⟨(vertex, other), hadj⟩, hvertex, hotherNotSide⟩
  have hedge := hcrossing dart
  have hedgeEq : (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) = edge := by
    apply Subtype.ext
    change s(vertex, other) = edge.1
    rw [hother]
  rw [hedgeEq] at hedge
  exact hedge

/-- **Triple-deletion dichotomy for connected cubic graphs.**  If deleting
three edges disconnects the graph, the triple supports a cyclic edge cut
of size at most three, or some vertex carries exactly those three
edges. -/
theorem cyclicCut_or_incident_of_not_connected_deleteEdges_triple
    (hregular : G.IsRegularOfDegree 3) (hconnected : G.Connected)
    (first second third : G.edgeSet)
    (hdelete :
      ¬ (G.deleteEdges
        ({first.1, second.1, third.1} : Set (Sym2 V))).Connected) :
    (∃ cut : SmallCyclicEdgeCut G, cut.edgeCut.card ≤ 3) ∨
      ∃ vertex : V,
        ∀ edge : G.edgeSet, vertex ∈ (edge.1 : Sym2 V) →
          edge ∈ ({first, second, third} : Finset G.edgeSet) := by
  classical
  let deleted := G.deleteEdges ({first.1, second.1, third.1} : Set (Sym2 V))
  letI : Nonempty V := hconnected.nonempty
  have hnotPreconnected : ¬ deleted.Preconnected := by
    intro hpreconnected
    exact hdelete ⟨hpreconnected⟩
  rw [SimpleGraph.Preconnected] at hnotPreconnected
  push Not at hnotPreconnected
  rcases hnotPreconnected with ⟨insideVertex, outsideVertex, hnotReachable⟩
  let inside := deleted.connectedComponentMk insideVertex
  let outside := deleted.connectedComponentMk outsideVertex
  have hcomponents : inside ≠ outside := by
    intro heq
    exact hnotReachable (ConnectedComponent.exact heq)
  have hdegreeLocal : ∀ side : V → Prop,
      ∀ vertex, side vertex → G.degree vertex = 3 :=
    fun _ vertex _ => hregular vertex
  have hinsideDichotomy :=
    hasCycleOnSide_or_card_eq_one_of_local_cubic_of_connected_induce_of_crossing_le_three
      (G := G) (fun vertex => vertex ∈ inside.supp)
      (hdegreeLocal _)
      inside.nonempty_supp
      (connected_induce_component_of_delete_triple first second third inside)
      ({first, second, third} : Finset G.edgeSet)
      (Finset.card_le_three)
      (crossingSideDart_edge_mem_triple_of_delete_component
        first second third inside)
  have houtsideDichotomy :=
    hasCycleOnSide_or_card_eq_one_of_local_cubic_of_connected_induce_of_crossing_le_three
      (G := G) (fun vertex => vertex ∈ outside.supp)
      (hdegreeLocal _)
      outside.nonempty_supp
      (connected_induce_component_of_delete_triple first second third outside)
      ({first, second, third} : Finset G.edgeSet)
      (Finset.card_le_three)
      (crossingSideDart_edge_mem_triple_of_delete_component
        first second third outside)
  rcases hinsideDichotomy with hinsideCycle | hinsideOne
  · rcases houtsideDichotomy with houtsideCycle | houtsideOne
    · -- both sides carry cycles: a cyclic cut of size ≤ 3
      left
      have houtsideCycleCompl : HasCycleOnSide G
          (fun vertex => ¬ vertex ∈ inside.supp) :=
        HasCycleOnSide.mono (fun vertex houtsideMem hinsideMem =>
          hcomponents (ConnectedComponent.eq_of_common_vertex
            hinsideMem houtsideMem))
          houtsideCycle
      let edgeCut := Finset.univ.filter fun edge : G.edgeSet =>
        EdgeCrossesVertexSide G
          (fun vertex => vertex ∈ inside.supp) edge
      have hedgeCutSubset :
          edgeCut ⊆ ({first, second, third} : Finset G.edgeSet) := by
        intro edge hedge
        simp only [edgeCut, Finset.mem_filter, Finset.mem_univ,
          true_and] at hedge
        exact edge_mem_triple_of_crosses_delete_component
          first second third inside edge hedge
      have hedgeCutCard : edgeCut.card ≤ 3 := by
        calc
          edgeCut.card ≤
              ({first, second, third} : Finset G.edgeSet).card :=
            Finset.card_le_card hedgeCutSubset
          _ ≤ 3 := Finset.card_le_three
      refine ⟨{ edgeCut := edgeCut
                side := fun vertex => vertex ∈ inside.supp
                hcut_eq := fun edge => by simp [edgeCut]
                hcard_le_four := le_trans hedgeCutCard (by omega)
                hinside_cycle := hinsideCycle
                houtside_cycle := houtsideCycleCompl }, hedgeCutCard⟩
    · -- the outside component is one vertex
      right
      rcases forall_incident_mem_triple_of_card_eq_one first second third
          (fun vertex => vertex ∈ outside.supp) houtsideOne
          (crossingSideDart_edge_mem_triple_of_delete_component
            first second third outside) with ⟨vertex, _, hvertex⟩
      exact ⟨vertex, hvertex⟩
  · -- the inside component is one vertex
    right
    rcases forall_incident_mem_triple_of_card_eq_one first second third
        (fun vertex => vertex ∈ inside.supp) hinsideOne
        (crossingSideDart_edge_mem_triple_of_delete_component
          first second third inside) with ⟨vertex, _, hvertex⟩
    exact ⟨vertex, hvertex⟩

end

end Mettapedia.GraphTheory.FourColor
