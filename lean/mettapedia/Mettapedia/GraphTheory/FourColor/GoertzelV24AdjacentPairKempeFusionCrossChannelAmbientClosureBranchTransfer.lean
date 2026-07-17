import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureCycleIntersection
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureDualTransfer

namespace SimpleGraph.Walk

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

omit [DecidableEq V] in
/-- At an endpoint of exactly one of two shared edges, two cycles in a
cubic graph have one common arm and two distinct exclusive arms. -/
theorem IsCycle.exists_exact_branch_neighbors
    {firstBase secondBase vertex : V}
    {first : G.Walk firstBase firstBase}
    {second : G.Walk secondBase secondBase}
    (hfirst : first.IsCycle) (hsecond : second.IsCycle)
    (hambientCard : (G.neighborSet vertex).ncard = 3)
    (firstShared secondShared : Sym2 V)
    (hexact : ∀ edge : Sym2 V,
      edge ∈ first.edges ∧ edge ∈ second.edges ↔
        edge = firstShared ∨ edge = secondShared)
    (hvertexFirstShared : vertex ∈ firstShared)
    (hvertexNotSecondShared : vertex ∉ secondShared) :
    ∃ shared firstOnly secondOnly : V,
      s(vertex, shared) = firstShared ∧
        first.toSubgraph.Adj vertex shared ∧
        second.toSubgraph.Adj vertex shared ∧
        first.toSubgraph.Adj vertex firstOnly ∧
        ¬ second.toSubgraph.Adj vertex firstOnly ∧
        ¬ first.toSubgraph.Adj vertex secondOnly ∧
        second.toSubgraph.Adj vertex secondOnly ∧
        shared ≠ firstOnly ∧ shared ≠ secondOnly ∧
        firstOnly ≠ secondOnly := by
  have hfirstSharedBoth := (hexact firstShared).2 (Or.inl rfl)
  have hfirstSupport : vertex ∈ first.support :=
    first.mem_support_of_mem_edges hfirstSharedBoth.1 hvertexFirstShared
  have hsecondSupport : vertex ∈ second.support :=
    second.mem_support_of_mem_edges hfirstSharedBoth.2 hvertexFirstShared
  rcases hfirst.exists_common_toSubgraph_neighbor_of_neighborSet_ncard_eq_three
      hsecond hfirstSupport hsecondSupport hambientCard with
    ⟨shared, hfirstSharedAdj, hsecondSharedAdj⟩
  have hsharedValue : s(vertex, shared) = firstShared := by
    have hfirstEdge : s(vertex, shared) ∈ first.edges :=
      first.mem_edges_toSubgraph.mp hfirstSharedAdj
    have hsecondEdge : s(vertex, shared) ∈ second.edges :=
      second.mem_edges_toSubgraph.mp hsecondSharedAdj
    rcases (hexact s(vertex, shared)).1
        ⟨hfirstEdge, hsecondEdge⟩ with hvalue | hvalue
    · exact hvalue
    · exact False.elim (hvertexNotSecondShared (by
        rw [← hvalue]
        simp))
  have hfirstCard :
      (first.toSubgraph.neighborSet vertex).ncard = 2 :=
    hfirst.ncard_neighborSet_toSubgraph_eq_two hfirstSupport
  rcases Set.exists_ne_of_one_lt_ncard (by omega :
      1 < (first.toSubgraph.neighborSet vertex).ncard) shared with
    ⟨firstOnly, hfirstOnlyAdj, hfirstOnlyNe⟩
  have hfirstOnlyNotSecond :
      ¬ second.toSubgraph.Adj vertex firstOnly := by
    intro hsecondOnlyAdj
    have hfirstEdge : s(vertex, firstOnly) ∈ first.edges :=
      first.mem_edges_toSubgraph.mp hfirstOnlyAdj
    have hsecondEdge : s(vertex, firstOnly) ∈ second.edges :=
      second.mem_edges_toSubgraph.mp hsecondOnlyAdj
    rcases (hexact s(vertex, firstOnly)).1
        ⟨hfirstEdge, hsecondEdge⟩ with hvalue | hvalue
    · apply hfirstOnlyNe
      apply (Sym2.mkEmbedding vertex).injective
      exact hvalue.trans hsharedValue.symm
    · exact hvertexNotSecondShared (by
        rw [← hvalue]
        simp)
  have hsecondCard :
      (second.toSubgraph.neighborSet vertex).ncard = 2 :=
    hsecond.ncard_neighborSet_toSubgraph_eq_two hsecondSupport
  rcases Set.exists_ne_of_one_lt_ncard (by omega :
      1 < (second.toSubgraph.neighborSet vertex).ncard) shared with
    ⟨secondOnly, hsecondOnlyAdj, hsecondOnlyNe⟩
  have hsecondOnlyNotFirst :
      ¬ first.toSubgraph.Adj vertex secondOnly := by
    intro hfirstOnlyAdj'
    have hfirstEdge : s(vertex, secondOnly) ∈ first.edges :=
      first.mem_edges_toSubgraph.mp hfirstOnlyAdj'
    have hsecondEdge : s(vertex, secondOnly) ∈ second.edges :=
      second.mem_edges_toSubgraph.mp hsecondOnlyAdj
    rcases (hexact s(vertex, secondOnly)).1
        ⟨hfirstEdge, hsecondEdge⟩ with hvalue | hvalue
    · apply hsecondOnlyNe
      apply (Sym2.mkEmbedding vertex).injective
      exact hvalue.trans hsharedValue.symm
    · exact hvertexNotSecondShared (by
        rw [← hvalue]
        simp)
  have hfirstSecondNe : firstOnly ≠ secondOnly := by
    intro hvalue
    apply hfirstOnlyNotSecond
    simpa [hvalue] using hsecondOnlyAdj
  exact ⟨shared, firstOnly, secondOnly, hsharedValue,
    hfirstSharedAdj, hsecondSharedAdj, hfirstOnlyAdj,
    hfirstOnlyNotSecond, hsecondOnlyNotFirst, hsecondOnlyAdj,
    hfirstOnlyNe.symm, hsecondOnlyNe.symm, hfirstSecondNe⟩

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24SimpleGraphTaitBridge
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

private theorem CrossCentralExactFaceCutPair.exists_incidentEdgeTransfer_triple_of_shared
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
    (vertex : V) (firstShared secondShared : Sym2 V)
    (hexact : ∀ edge : Sym2 V,
      edge ∈ (data.oppositePortClosure pair.prefixTrail).edges ∧
          edge ∈
            (data.alternateOppositePortClosure pair.suffixTrail).edges ↔
        edge = firstShared ∨ edge = secondShared)
    (hvertexFirstShared : vertex ∈ firstShared)
    (hvertexNotSecondShared : vertex ∉ secondShared)
    (hfirstSharedPurple :
      firstShared = (retainedEdgeToAmbientEdge data cross).1 ∨
        firstShared = centralEdgeValue data) :
    ∃ purpleEdge redEdge blueEdge : G.edgeSet,
      incidentEdgeFinset G vertex = {purpleEdge, redEdge, blueEdge} ∧
        pair.edgeTransfer purpleEdge = purple ∧
        pair.edgeTransfer redEdge = red ∧
        pair.edgeTransfer blueEdge = blue := by
  letI : ∀ current : V, Fintype (G.neighborSet current) :=
    fun _ => Subtype.fintype _
  have hambientCard : (G.neighborSet vertex).ncard = 3 := by
    calc
      (G.neighborSet vertex).ncard =
          Fintype.card (G.neighborSet vertex) :=
        (Set.fintypeCard_eq_ncard (G.neighborSet vertex)).symm
      _ = G.degree vertex := G.card_neighborSet_eq_degree vertex
      _ = 3 := (graphData.toRotationSystem_isCubic_iff.mp
        minimal.spherical.cubic).degree_eq vertex
  rcases hprefixCycle.exists_exact_branch_neighbors hsuffixCycle
      hambientCard firstShared secondShared hexact hvertexFirstShared
        hvertexNotSecondShared with
    ⟨shared, firstOnly, secondOnly, hsharedValue,
      hprefixSharedAdj, _hsuffixSharedAdj,
      hprefixFirstOnlyAdj, hsuffixFirstOnlyNotAdj,
      hprefixSecondOnlyNotAdj, hsuffixSecondOnlyAdj,
      _hsharedFirstOnly, _hsharedSecondOnly, _hfirstSecondOnly⟩
  let purpleEdge : G.edgeSet :=
    ⟨s(vertex, shared), hprefixSharedAdj.adj_sub⟩
  let redEdge : G.edgeSet :=
    ⟨s(vertex, firstOnly), hprefixFirstOnlyAdj.adj_sub⟩
  let blueEdge : G.edgeSet :=
    ⟨s(vertex, secondOnly), hsuffixSecondOnlyAdj.adj_sub⟩
  have hpurple : pair.edgeTransfer purpleEdge = purple := by
    apply (pair.edgeTransfer_eq_purple_iff minimal purpleEdge).2
    change s(vertex, shared) =
        (retainedEdgeToAmbientEdge data cross).1 ∨
      s(vertex, shared) = centralEdgeValue data
    simpa only [hsharedValue] using hfirstSharedPurple
  have hred : pair.edgeTransfer redEdge = red := by
    apply (pair.edgeTransfer_eq_red_iff minimal redEdge).2
    constructor
    · exact (data.oppositePortClosure pair.prefixTrail)
        |>.mem_edges_toSubgraph.mp hprefixFirstOnlyAdj
    · intro hedge
      exact hsuffixFirstOnlyNotAdj
        ((data.alternateOppositePortClosure pair.suffixTrail)
          |>.mem_edges_toSubgraph.mpr hedge)
  have hblue : pair.edgeTransfer blueEdge = blue := by
    apply (pair.edgeTransfer_eq_blue_iff minimal blueEdge).2
    constructor
    · intro hedge
      exact hprefixSecondOnlyNotAdj
        ((data.oppositePortClosure pair.prefixTrail)
          |>.mem_edges_toSubgraph.mpr hedge)
    · exact (data.alternateOppositePortClosure pair.suffixTrail)
        |>.mem_edges_toSubgraph.mp hsuffixSecondOnlyAdj
  have hpurpleMem : purpleEdge ∈ incidentEdgeFinset G vertex := by
    simp [incidentEdgeFinset, purpleEdge]
  have hredMem : redEdge ∈ incidentEdgeFinset G vertex := by
    simp [incidentEdgeFinset, redEdge]
  have hblueMem : blueEdge ∈ incidentEdgeFinset G vertex := by
    simp [incidentEdgeFinset, blueEdge]
  have hpurpleRed : purpleEdge ≠ redEdge := by
    intro hedge
    have hcolor := congrArg pair.edgeTransfer hedge
    rw [hpurple, hred] at hcolor
    exact red_ne_purple hcolor.symm
  have hpurpleBlue : purpleEdge ≠ blueEdge := by
    intro hedge
    have hcolor := congrArg pair.edgeTransfer hedge
    rw [hpurple, hblue] at hcolor
    exact blue_ne_purple hcolor.symm
  have hredBlue : redEdge ≠ blueEdge := by
    intro hedge
    have hcolor := congrArg pair.edgeTransfer hedge
    rw [hred, hblue] at hcolor
    exact red_ne_blue hcolor
  have htripleSubset :
      ({purpleEdge, redEdge, blueEdge} : Finset G.edgeSet) ⊆
        incidentEdgeFinset G vertex := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact hpurpleMem
    · exact hredMem
    · exact hblueMem
  have htripleCard :
      ({purpleEdge, redEdge, blueEdge} : Finset G.edgeSet).card = 3 := by
    simp [hpurpleRed, hpurpleBlue, hredBlue]
  have hincidentCard : (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic vertex
  have htripleEq :
      ({purpleEdge, redEdge, blueEdge} : Finset G.edgeSet) =
        incidentEdgeFinset G vertex :=
    Finset.eq_of_subset_of_card_le htripleSubset (by
      rw [hincidentCard, htripleCard])
  exact ⟨purpleEdge, redEdge, blueEdge, htripleEq.symm,
    hpurple, hred, hblue⟩

/-- Every common branch vertex of the two irreducible closures has the
exact three-letter transfer alphabet: one purple shared edge, one red
first-only edge, and one blue second-only edge. -/
theorem CrossCentralExactFaceCutPair.exists_incidentEdgeTransfer_triple
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
    (vertex : V)
    (hcommon :
      vertex ∈ (data.oppositePortClosure pair.prefixTrail).support ∧
        vertex ∈
          (data.alternateOppositePortClosure pair.suffixTrail).support) :
    ∃ purpleEdge redEdge blueEdge : G.edgeSet,
      incidentEdgeFinset G vertex = {purpleEdge, redEdge, blueEdge} ∧
        pair.edgeTransfer purpleEdge = purple ∧
        pair.edgeTransfer redEdge = red ∧
        pair.edgeTransfer blueEdge = blue := by
  have hbranch := (pair.mem_both_closure_support_iff minimal
    hprefixCycle hsuffixCycle vertex).1 hcommon
  have hdisjoint :=
    retainedEdgeToAmbientEdge_toFinset_disjoint_centralEdgeValue data cross
  rcases hbranch with hcross | hcentral
  · have hnotCentral : vertex ∉ centralEdgeValue data := by
      intro hcentral
      exact (Finset.disjoint_left.mp hdisjoint)
        (Sym2.mem_toFinset.mpr hcross)
        (Sym2.mem_toFinset.mpr hcentral)
    exact pair.exists_incidentEdgeTransfer_triple_of_shared minimal
      hprefixCycle hsuffixCycle vertex
      (retainedEdgeToAmbientEdge data cross).1 (centralEdgeValue data)
      (data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
        pair.prefixTrail pair.suffixTrail cross
          pair.retainedIntersectionExact)
      hcross hnotCentral (Or.inl rfl)
  · have hnotCross :
        vertex ∉ (retainedEdgeToAmbientEdge data cross).1 := by
      intro hcross
      exact (Finset.disjoint_left.mp hdisjoint)
        (Sym2.mem_toFinset.mpr hcross)
        (Sym2.mem_toFinset.mpr hcentral)
    apply pair.exists_incidentEdgeTransfer_triple_of_shared minimal
      hprefixCycle hsuffixCycle vertex (centralEdgeValue data)
      (retainedEdgeToAmbientEdge data cross).1
      (fun edge => ?_) hcentral hnotCross (Or.inr rfl)
    simpa only [or_comm] using
      (data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
        pair.prefixTrail pair.suffixTrail cross
          pair.retainedIntersectionExact edge)

/-- Equivalently, the image of the three incident edges at any common
branch vertex is exactly the finite nonzero transfer alphabet. -/
theorem CrossCentralExactFaceCutPair.image_edgeTransfer_incidentEdgeFinset_eq
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
    (vertex : V)
    (hcommon :
      vertex ∈ (data.oppositePortClosure pair.prefixTrail).support ∧
        vertex ∈
          (data.alternateOppositePortClosure pair.suffixTrail).support) :
    (incidentEdgeFinset G vertex).image pair.edgeTransfer =
      {red, blue, purple} := by
  rcases pair.exists_incidentEdgeTransfer_triple minimal hprefixCycle
      hsuffixCycle vertex hcommon with
    ⟨purpleEdge, redEdge, blueEdge, hincident,
      hpurple, hred, hblue⟩
  rw [hincident]
  ext color
  simp [hpurple, hred, hblue, or_comm, or_left_comm]

/-- The irreducible pair therefore exposes a finite four-branch interface,
and every branch carries the complete three-letter nonzero transfer
alphabet. -/
theorem CrossCentralExactFaceCutPair.four_branch_transfer_profile
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
          (data.alternateOppositePortClosure
            pair.suffixTrail).support.toFinset).card = 4 ∧
      ∀ vertex ∈
          (data.oppositePortClosure pair.prefixTrail).support.toFinset ∩
            (data.alternateOppositePortClosure
              pair.suffixTrail).support.toFinset,
        (incidentEdgeFinset G vertex).image pair.edgeTransfer =
          {red, blue, purple} := by
  constructor
  · exact pair.card_common_closure_support_eq_four minimal
      hprefixCycle hsuffixCycle
  · intro vertex hvertex
    apply pair.image_edgeTransfer_incidentEdgeFinset_eq minimal
      hprefixCycle hsuffixCycle vertex
    simpa only [Finset.mem_inter, List.mem_toFinset] using hvertex

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
