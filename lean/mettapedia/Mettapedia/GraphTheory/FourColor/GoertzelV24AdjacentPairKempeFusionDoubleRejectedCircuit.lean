import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionZeroFusionTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelRejectedTrail

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open SimpleGraph

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance doubleRejectedCircuitGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A cross-prefix splice omits a positive suffix of each source route, so
its primal edge support is strictly smaller than the two complete route
supports together. -/
theorem EvenKempePortPath.crossSplice_support_length_lt_route_lengths
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.crossSplice second site).support.length <
      first.ambientPath.length + second.ambientPath.length + 2 := by
  have hfirstSplit := congrArg SimpleGraph.Walk.length
    (first.firstPrefix_append_firstSuffix second site)
  have hsecondSplit := congrArg SimpleGraph.Walk.length
    (first.secondPrefix_append_secondSuffix second site)
  have hfirstSuffix :
      0 < (first.firstSuffixFromCrossSite second site).length :=
    first.firstSuffixFromCrossSite_length_pos second hab hbc site
  have hsecondSuffix :
      0 < (first.secondSuffixFromCrossSite second site).length :=
    first.secondSuffixFromCrossSite_length_pos second hac hbc site
  rw [EvenKempePortPath.crossSplice,
    SimpleGraph.Walk.length_support,
    SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse]
  simp only [SimpleGraph.Walk.length_append] at hfirstSplit hsecondSplit
  omega

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Zero fusion within each lens and same-family separation between the
lenses make the two complementary cross-prefix splices edge-disjoint. -/
theorem EvenKempeFusionLens.bcCrossSplice_support_disjoint_cbCrossSplice_support_of_zeroFusion
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hzero01 : lens01.fusionSiteCount = 0)
    (hzero23 : lens23.fusionSiteCount = 0)
    (bcSite : lens01.bRoute.CrossSite lens23.cRoute)
    (cbSite : lens01.cRoute.CrossSite lens23.bRoute) :
    (lens01.bRoute.crossSplice lens23.cRoute bcSite).support.Disjoint
      (lens01.cRoute.crossSplice lens23.bRoute cbSite).support := by
  have hzeroDisjoint01 :=
    EvenKempeFusionLens.routeSupports_disjoint_of_fusionSiteCount_eq_zero
      lens01 hzero01
  have hzeroDisjoint23 :=
    EvenKempeFusionLens.routeSupports_disjoint_of_fusionSiteCount_eq_zero
      lens23 hzero23
  rw [List.disjoint_left]
  intro edge hbcSplice hcbSplice
  have hbcRoutes := lens01.bRoute.crossSplice_support_subset_route_supports
    lens23.cRoute bcSite hbcSplice
  have hcbRoutes := lens01.cRoute.crossSplice_support_subset_route_supports
    lens23.bRoute cbSite hcbSplice
  rcases List.mem_append.mp hbcRoutes with hb01 | hc23
  · rcases List.mem_append.mp hcbRoutes with hc01 | hb23
    · exact (List.disjoint_left.mp hzeroDisjoint01) hb01 hc01
    · exact (List.disjoint_left.mp hbDisjoint) hb01 hb23
  · rcases List.mem_append.mp hcbRoutes with hc01 | hb23
    · exact (List.disjoint_left.mp hcDisjoint) hc01 hc23
    · exact (List.disjoint_left.mp hzeroDisjoint23) hb23 hc23

/-- The corresponding lists of primal edge values are disjoint as well. -/
theorem EvenKempeFusionLens.bcCrossSplice_edges_disjoint_cbCrossSplice_edges_of_zeroFusion
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hzero01 : lens01.fusionSiteCount = 0)
    (hzero23 : lens23.fusionSiteCount = 0)
    (bcSite : lens01.bRoute.CrossSite lens23.cRoute)
    (cbSite : lens01.cRoute.CrossSite lens23.bRoute) :
    ((lens01.bRoute.crossSplice lens23.cRoute bcSite).support.map
        Subtype.val).Disjoint
      ((lens01.cRoute.crossSplice lens23.bRoute cbSite).support.map
        Subtype.val) := by
  have hsupport :=
    EvenKempeFusionLens.bcCrossSplice_support_disjoint_cbCrossSplice_support_of_zeroFusion
      data lens01 lens23 hbDisjoint hcDisjoint hzero01 hzero23 bcSite cbSite
  rw [List.disjoint_left]
  intro edge hbcEdge hcbEdge
  rcases List.mem_map.mp hbcEdge with ⟨bcEdge, hbcSupport, rfl⟩
  rcases List.mem_map.mp hcbEdge with ⟨cbEdge, hcbSupport, heq⟩
  have hedge : bcEdge = cbEdge := Subtype.ext heq.symm
  subst cbEdge
  exact (List.disjoint_left.mp hsupport) hbcSupport hcbSupport

/-- If both sparse cross channels are rejected in zero-fusion normal form,
their exact opposite-port trails close to an edge-simple primal circuit.
Its length is the sum of the two prefix-splice supports and is strictly less
than the sum of the two original lens lengths. -/
theorem EvenKempeFusionLens.exists_doubleRejectedCrossSpliceCircuit_of_zeroFusion
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hbcCount : (lens01.bcCrossSites lens23).length ≤ 1)
    (hcbCount : (lens01.cbCrossSites lens23).length ≤ 1)
    (hzero01 : lens01.fusionSiteCount = 0)
    (hzero23 : lens23.fusionSiteCount = 0)
    (bcSite : lens01.bRoute.CrossSite lens23.cRoute)
    (hbcFalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc bcSite = false)
    (cbSite : lens01.cRoute.CrossSite lens23.bRoute)
    (hcbFalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc cbSite = false) :
    ∃ circuit : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk
        (data.retainedPort 0) (data.retainedPort 0),
      circuit.IsCircuit ∧
        circuit.length =
          (lens01.bRoute.crossSplice lens23.cRoute bcSite).support.length +
            (lens01.cRoute.crossSplice lens23.bRoute cbSite).support.length ∧
        circuit.length < lens01.closedWalk.length + lens23.closedWalk.length := by
  rcases EvenKempeFusionLens.exists_bcExactCrossSpliceTrail_of_rejected
      graphData data lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
      hbcCount bcSite
      hbcFalse with
    ⟨bcTrail, hbcTrail, hbcPositive, hbcEdges, _hbcSite, _hbcClosure⟩
  rcases EvenKempeFusionLens.exists_cbExactCrossSpliceTrail_of_rejected
      graphData data lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
      hcbCount cbSite
      hcbFalse with
    ⟨cbTrail, hcbTrail, hcbPositive, hcbEdges, _hcbSite, _hcbClosure⟩
  have hspliceDisjoint :=
    EvenKempeFusionLens.bcCrossSplice_edges_disjoint_cbCrossSplice_edges_of_zeroFusion
      data lens01 lens23 hbDisjoint hcDisjoint hzero01 hzero23 bcSite cbSite
  have htrailDisjoint : bcTrail.edges.Disjoint cbTrail.reverse.edges := by
    rw [hbcEdges, SimpleGraph.Walk.edges_reverse, hcbEdges,
      List.disjoint_reverse_right]
    exact hspliceDisjoint
  let circuit := bcTrail.append cbTrail.reverse
  have hcircuitTrail : circuit.IsTrail := by
    apply (SimpleGraph.Walk.isTrail_append bcTrail cbTrail.reverse).2
    exact ⟨hbcTrail,
      (SimpleGraph.Walk.reverse_isTrail_iff cbTrail).2 hcbTrail,
      htrailDisjoint⟩
  have hcircuit : circuit.IsCircuit := by
    refine ⟨hcircuitTrail, ?_⟩
    intro heq
    have hlength : circuit.length = 0 := by rw [heq]; rfl
    dsimp only [circuit] at hlength
    simp only [SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse] at hlength
    omega
  have hlength : circuit.length =
      (lens01.bRoute.crossSplice lens23.cRoute bcSite).support.length +
        (lens01.cRoute.crossSplice lens23.bRoute cbSite).support.length := by
    dsimp only [circuit]
    rw [SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse,
      ← SimpleGraph.Walk.length_edges bcTrail,
      ← SimpleGraph.Walk.length_edges cbTrail,
      hbcEdges, hcbEdges]
    simp only [List.length_map, SimpleGraph.Walk.length_support]
  have hbcShort :=
    lens01.bRoute.crossSplice_support_length_lt_route_lengths
      lens23.cRoute hab hac hbc bcSite
  have hcbShort :=
    lens01.cRoute.crossSplice_support_length_lt_route_lengths
      lens23.bRoute hac hab hbc.symm cbSite
  refine ⟨circuit, hcircuit, hlength, ?_⟩
  rw [hlength, lens01.closedWalk_length, lens23.closedWalk_length]
  simp only [EvenKempePortPath.ambientPath_length] at hbcShort hcbShort
  omega

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
