import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureCycleReduction

namespace SimpleGraph.Walk

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

omit [DecidableEq V] in
/-- Two cycles through a cubic vertex use a common incident edge. Each cycle
uses two of the three ambient neighbors, so their local neighbor pairs must
overlap. -/
theorem IsCycle.exists_common_toSubgraph_neighbor_of_neighborSet_ncard_eq_three
    {firstBase secondBase vertex : V}
    {first : G.Walk firstBase firstBase}
    {second : G.Walk secondBase secondBase}
    (hfirst : first.IsCycle) (hsecond : second.IsCycle)
    (hfirstVertex : vertex ∈ first.support)
    (hsecondVertex : vertex ∈ second.support)
    (hambientCard : (G.neighborSet vertex).ncard = 3) :
    ∃ neighbor : V,
      first.toSubgraph.Adj vertex neighbor ∧
        second.toSubgraph.Adj vertex neighbor := by
  let firstNeighbors := first.toSubgraph.neighborSet vertex
  let secondNeighbors := second.toSubgraph.neighborSet vertex
  have hfirstCard : firstNeighbors.ncard = 2 := by
    exact hfirst.ncard_neighborSet_toSubgraph_eq_two hfirstVertex
  have hsecondCard : secondNeighbors.ncard = 2 := by
    exact hsecond.ncard_neighborSet_toSubgraph_eq_two hsecondVertex
  have hintersection :
      (firstNeighbors ∩ secondNeighbors).Nonempty := by
    by_contra hempty
    have hdisjoint : Disjoint firstNeighbors secondNeighbors := by
      rw [Set.disjoint_left]
      intro neighbor hfirstNeighbor hsecondNeighbor
      exact hempty ⟨neighbor, hfirstNeighbor, hsecondNeighbor⟩
    have hunionCard :
        (firstNeighbors ∪ secondNeighbors).ncard = 4 := by
      rw [Set.ncard_union_eq hdisjoint, hfirstCard, hsecondCard]
    have hunionSubset :
        firstNeighbors ∪ secondNeighbors ⊆ G.neighborSet vertex :=
      Set.union_subset
        (first.toSubgraph.neighborSet_subset vertex)
        (second.toSubgraph.neighborSet_subset vertex)
    have hle := Set.ncard_le_ncard hunionSubset
    rw [hunionCard, hambientCard] at hle
    omega
  rcases hintersection with ⟨neighbor, hfirstNeighbor, hsecondNeighbor⟩
  exact ⟨neighbor, hfirstNeighbor, hsecondNeighbor⟩

omit [DecidableEq V] in
/-- If two cycles in a cubic graph have exactly two common edges, every
common support vertex is an endpoint of one of those two edges. -/
theorem IsCycle.mem_sharedEdge_of_mem_both_support_of_neighborSet_ncard_eq_three
    {firstBase secondBase vertex : V}
    {first : G.Walk firstBase firstBase}
    {second : G.Walk secondBase secondBase}
    (hfirst : first.IsCycle) (hsecond : second.IsCycle)
    (hcubic : ∀ current : V, (G.neighborSet current).ncard = 3)
    (firstShared secondShared : Sym2 V)
    (hexact : ∀ edge : Sym2 V,
      edge ∈ first.edges ∧ edge ∈ second.edges ↔
        edge = firstShared ∨ edge = secondShared)
    (hfirstVertex : vertex ∈ first.support)
    (hsecondVertex : vertex ∈ second.support) :
    vertex ∈ firstShared ∨ vertex ∈ secondShared := by
  rcases hfirst.exists_common_toSubgraph_neighbor_of_neighborSet_ncard_eq_three
      hsecond hfirstVertex hsecondVertex (hcubic vertex) with
    ⟨neighbor, hfirstNeighbor, hsecondNeighbor⟩
  have hfirstEdge : s(vertex, neighbor) ∈ first.edges :=
    first.mem_edges_toSubgraph.mp hfirstNeighbor
  have hsecondEdge : s(vertex, neighbor) ∈ second.edges :=
    second.mem_edges_toSubgraph.mp hsecondNeighbor
  rcases (hexact s(vertex, neighbor)).1
      ⟨hfirstEdge, hsecondEdge⟩ with hedge | hedge
  · left
    rw [← hedge]
    simp
  · right
    rw [← hedge]
    simp

omit [DecidableEq V] in
/-- Consequently the common vertex support of two cubic cycles with an
exact two-edge intersection is exactly the union of the endpoints of the
two shared edges. -/
theorem IsCycle.mem_both_support_iff_mem_sharedEdges_of_neighborSet_ncard_eq_three
    {firstBase secondBase : V}
    {first : G.Walk firstBase firstBase}
    {second : G.Walk secondBase secondBase}
    (hfirst : first.IsCycle) (hsecond : second.IsCycle)
    (hcubic : ∀ current : V, (G.neighborSet current).ncard = 3)
    (firstShared secondShared : Sym2 V)
    (hexact : ∀ edge : Sym2 V,
      edge ∈ first.edges ∧ edge ∈ second.edges ↔
        edge = firstShared ∨ edge = secondShared)
    (vertex : V) :
    vertex ∈ first.support ∧ vertex ∈ second.support ↔
      vertex ∈ firstShared ∨ vertex ∈ secondShared := by
  constructor
  · rintro ⟨hfirstVertex, hsecondVertex⟩
    exact hfirst.mem_sharedEdge_of_mem_both_support_of_neighborSet_ncard_eq_three
      hsecond hcubic firstShared secondShared hexact
        hfirstVertex hsecondVertex
  · intro hshared
    have hfirstShared := (hexact firstShared).2 (Or.inl rfl)
    have hsecondShared := (hexact secondShared).2 (Or.inr rfl)
    rcases hshared with hvertex | hvertex
    · exact ⟨
        first.mem_support_of_mem_edges hfirstShared.1 hvertex,
        second.mem_support_of_mem_edges hfirstShared.2 hvertex⟩
    · exact ⟨
        first.mem_support_of_mem_edges hsecondShared.1 hvertex,
        second.mem_support_of_mem_edges hsecondShared.2 hvertex⟩

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexDecidableEq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every endpoint of an edge embedded from the deleted graph survives the
adjacent-pair deletion. -/
theorem retainedEdgeToAmbientEdge_endpoint_mem_retainedVertexSet
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    {vertex : V}
    (hvertex : vertex ∈ (retainedEdgeToAmbientEdge data edge).1) :
    vertex ∈ retainedVertexSet data.firstVertex data.secondVertex := by
  rw [retainedEdgeToAmbientEdge_val] at hvertex
  rcases Sym2.mem_map.mp hvertex with
    ⟨retained, _hretained, hvalue⟩
  subst vertex
  exact retained.2

omit [Fintype V] [DecidableRel G.Adj] in
/-- The embedded retained edge and restored central edge have disjoint
endpoint sets. -/
theorem retainedEdgeToAmbientEdge_toFinset_disjoint_centralEdgeValue
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    Disjoint (retainedEdgeToAmbientEdge data edge).1.toFinset
      (centralEdgeValue data).toFinset := by
  rw [Finset.disjoint_left]
  intro vertex hretained hcentral
  have hsurvives :=
    retainedEdgeToAmbientEdge_endpoint_mem_retainedVertexSet data edge
      (Sym2.mem_toFinset.mp hretained)
  have hdeleted : vertex = data.firstVertex ∨
      vertex = data.secondVertex := by
    simpa [centralEdgeValue] using (Sym2.mem_toFinset.mp hcentral)
  rcases hdeleted with rfl | rfl
  · exact hsurvives.1 rfl
  · exact hsurvives.2 rfl

/-- In the irreducible simple-cycle branch, the two exact ambient closures
share no vertices beyond the endpoints of the retained cross edge and the
restored central edge. -/
theorem CrossCentralExactFaceCutPair.mem_both_closure_support_iff
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hprefixCycle :
      (data.oppositePortClosure pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure pair.suffixTrail).IsCycle)
    (vertex : V) :
    vertex ∈ (data.oppositePortClosure pair.prefixTrail).support ∧
        vertex ∈
          (data.alternateOppositePortClosure pair.suffixTrail).support ↔
      vertex ∈ (retainedEdgeToAmbientEdge data cross).1 ∨
        vertex ∈ centralEdgeValue data := by
  letI : ∀ current : V, Fintype (G.neighborSet current) :=
    fun _ => Subtype.fintype _
  have hcubic : ∀ current : V,
      (G.neighborSet current).ncard = 3 := by
    intro current
    calc
      (G.neighborSet current).ncard =
          Fintype.card (G.neighborSet current) :=
        (Set.fintypeCard_eq_ncard (G.neighborSet current)).symm
      _ = G.degree current := G.card_neighborSet_eq_degree current
      _ = 3 := (graphData.toRotationSystem_isCubic_iff.mp
        minimal.spherical.cubic).degree_eq current
  apply
    hprefixCycle.mem_both_support_iff_mem_sharedEdges_of_neighborSet_ncard_eq_three
      hsuffixCycle hcubic
      (retainedEdgeToAmbientEdge data cross).1 (centralEdgeValue data)
  exact
    data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
      pair.prefixTrail pair.suffixTrail cross pair.retainedIntersectionExact

/-- Finset form of the exact common-support classification. -/
theorem CrossCentralExactFaceCutPair.common_closure_support_toFinset_eq
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hprefixCycle :
      (data.oppositePortClosure pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure pair.suffixTrail).IsCycle) :
    (data.oppositePortClosure pair.prefixTrail).support.toFinset ∩
        (data.alternateOppositePortClosure pair.suffixTrail).support.toFinset =
      (retainedEdgeToAmbientEdge data cross).1.toFinset ∪
        (centralEdgeValue data).toFinset := by
  ext vertex
  simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_union,
    Sym2.mem_toFinset]
  exact pair.mem_both_closure_support_iff minimal hprefixCycle
    hsuffixCycle vertex

/-- The two irreducible closures have exactly four common vertices: the
two endpoints of the retained cross edge and the two deleted vertices. -/
theorem CrossCentralExactFaceCutPair.card_common_closure_support_eq_four
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hprefixCycle :
      (data.oppositePortClosure pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure pair.suffixTrail).IsCycle) :
    ((data.oppositePortClosure pair.prefixTrail).support.toFinset ∩
      (data.alternateOppositePortClosure pair.suffixTrail).support.toFinset).card =
        4 := by
  rw [pair.common_closure_support_toFinset_eq minimal hprefixCycle
    hsuffixCycle]
  calc
    ((retainedEdgeToAmbientEdge data cross).1.toFinset ∪
        (centralEdgeValue data).toFinset).card =
        (retainedEdgeToAmbientEdge data cross).1.toFinset.card +
          (centralEdgeValue data).toFinset.card :=
      Finset.card_union_of_disjoint
        (retainedEdgeToAmbientEdge_toFinset_disjoint_centralEdgeValue
          data cross)
    _ = 2 + 2 := by
      rw [Sym2.card_toFinset_of_not_isDiag
          (retainedEdgeToAmbientEdge data cross).1
          (G.not_isDiag_of_mem_edgeSet
            (retainedEdgeToAmbientEdge data cross).2),
        Sym2.card_toFinset_of_not_isDiag (centralEdgeValue data)
          (G.not_isDiag_of_mem_edgeSet (centralEdge data).2)]
    _ = 4 := rfl

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
