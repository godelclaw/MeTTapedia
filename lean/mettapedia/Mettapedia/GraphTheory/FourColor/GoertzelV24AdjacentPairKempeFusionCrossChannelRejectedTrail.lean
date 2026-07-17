import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelFaceSymbol
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelRouteIntervals

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open SimpleGraph

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rejectedCrossTrailGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- In the reversed-pairing state, a sparse `bc` cross splice lifts without
triangle contraction. Its primal trail contains exactly the splice support,
including the selected cross edge. -/
theorem EvenKempeFusionLens.exists_bcExactCrossSpliceTrail_of_pairing_false
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hpairing : lens01.bRoute.crossPairingBit lens23.cRoute
      hab hac hbc site = false) :
    ∃ trail : G.Walk (data.defectVertex 0) (data.defectVertex 2),
      trail.IsTrail ∧ 0 < trail.length ∧
        trail.edges =
          (lens01.bRoute.crossSplice lens23.cRoute site).support.map
            Subtype.val ∧
        site.1.1 ∈ trail.edges := by
  let joined := lens01.bRoute.crossSplice lens23.cRoute site
  have hleftmost : ∀ edge : G.edgeSet,
      edge ∈ (lens01.bRoute.firstPrefixToCrossSite
        lens23.cRoute site).support →
      edge ∈ lens23.cRoute.ambientPath.support →
      edge = site.1 := by
    intro edge hprefix hsecond
    exact lens01.bcCrossSite_eq_of_length_le_one lens23 hcount site edge
      (lens01.bRoute.firstPrefixToCrossSite_support_subset
        lens23.cRoute site hprefix) hsecond
  have hpath : joined.IsPath := by
    exact lens01.bRoute.crossSplice_isPath_of_leftmost
      lens23.cRoute site hleftmost
  have hseam :=
    (lens01.bRoute.crossPairingBit_eq_false_iff_seam_ne
      lens23.cRoute hab hac hbc site).1 hpairing
  have hcoherent : joined.IsPrimalCoherent := by
    exact lens01.bRoute.crossSplice_isPrimalCoherent_of_seam_ne
      lens23.cRoute hab hac hbc site hseam
  have hpositive : 0 < joined.length := by
    exact lens01.bRoute.crossSplice_length_pos lens23.cRoute hbc site
  have hsupport : joined.support ⊆
      lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support := by
    exact lens01.bRoute.crossSplice_support_subset_route_supports
      lens23.cRoute site
  have hc01Start : lens01.cRoute.leftEdge.1 ∈
      lens01.cRoute.ambientPath.support := by
    simpa only [lens01.cRoute.ambientPath.getVert_zero] using
      lens01.cRoute.ambientPath.getVert_mem_support 0
  have hb23Start : lens23.bRoute.leftEdge.1 ∈
      lens23.bRoute.ambientPath.support := by
    simpa only [lens23.bRoute.ambientPath.getVert_zero] using
      lens23.bRoute.ambientPath.getVert_mem_support 0
  have hc01Absent : lens01.cRoute.leftEdge.1 ∉ joined.support := by
    intro hmem
    rcases List.mem_append.mp (hsupport hmem) with hb01 | hc23
    · exact lens01.cLeftEdge_not_mem_bAmbientPath_support hab hac hb01
    · exact (List.disjoint_left.mp hcDisjoint) hc01Start hc23
  have hb23Absent : lens23.bRoute.leftEdge.1 ∉ joined.support := by
    intro hmem
    rcases List.mem_append.mp (hsupport hmem) with hb01 | hc23
    · exact (List.disjoint_left.mp hbDisjoint) hb01 hb23Start
    · exact lens23.bLeftEdge_not_mem_cAmbientPath_support hab hac hc23
  have hstartNe := lens01.leftDefect_ne_firstJunction_of_bTerminal
    hdata joined hpositive hc01Absent
  have hendNe := lens23.lastJunction_ne_leftDefect_of_cTerminal
    hdata joined hpositive hb23Absent
  have hstartMem : data.defectVertex 0 ∈
      (lens01.bRoute.leftEdge.1.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using lens01.bRoute.leftIncident
  have hendMem : data.defectVertex 2 ∈
      (lens23.cRoute.leftEdge.1.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using lens23.cRoute.leftIncident
  let trail := joined.cappedPrimalLift hpositive hcoherent
    (data.defectVertex 0) (data.defectVertex 2)
    hstartMem hendMem hstartNe hendNe
  have hedges : trail.edges = joined.support.map Subtype.val := by
    dsimp only [trail]
    exact joined.cappedPrimalLift_edges_eq_map_support
      hpositive hcoherent
      (data.defectVertex 0) (data.defectVertex 2)
      hstartMem hendMem hstartNe hendNe
  have hsiteSupport : site.1 ∈ joined.support := by
    dsimp only [joined]
    rw [EvenKempePortPath.crossSplice,
      SimpleGraph.Walk.support_append]
    apply List.mem_append.mpr
    exact Or.inl
      (lens01.bRoute.firstPrefixToCrossSite
        lens23.cRoute site).end_mem_support
  refine ⟨trail, ?_, ?_, hedges, ?_⟩
  · dsimp only [trail]
    exact joined.cappedPrimalLift_isTrail_of_isPath
      hpositive hcoherent hpath
      (data.defectVertex 0) (data.defectVertex 2)
      hstartMem hendMem hstartNe hendNe
  · dsimp only [trail]
    rw [joined.cappedPrimalLift_length]
    omega
  · rw [hedges]
    exact List.mem_map.mpr ⟨site.1, hsiteSupport, rfl⟩

/-- Secondary-color symmetry gives the exact uncontracted `cb` trail. -/
theorem EvenKempeFusionLens.exists_cbExactCrossSpliceTrail_of_pairing_false
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hpairing : lens01.cRoute.crossPairingBit lens23.bRoute
      hac hab hbc.symm site = false) :
    ∃ trail : G.Walk (data.defectVertex 0) (data.defectVertex 2),
      trail.IsTrail ∧ 0 < trail.length ∧
        trail.edges =
          (lens01.cRoute.crossSplice lens23.bRoute site).support.map
            Subtype.val ∧
        site.1.1 ∈ trail.edges := by
  simpa only [EvenKempeFusionLens.swapSecondaryColors_bRoute,
      EvenKempeFusionLens.swapSecondaryColors_cRoute] using
    lens01.swapSecondaryColors.exists_bcExactCrossSpliceTrail_of_pairing_false
      lens23.swapSecondaryColors hdata hac hab hbc.symm hcDisjoint
        hbDisjoint hcount site hpairing

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

/-- A rejected sparse `bc` state produces an exact uncontracted retained
trail, and the selected cross edge therefore lies in its ambient closure. -/
theorem EvenKempeFusionLens.exists_bcExactCrossSpliceTrail_of_rejected
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
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ path : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2),
      path.IsTrail ∧ 0 < path.length ∧
        path.edges =
          (lens01.bRoute.crossSplice lens23.cRoute site).support.map
            Subtype.val ∧
        site.1.1 ∈ path.edges ∧
        (retainedEdgeToAmbientEdge data site.1).1 ∈
          (data.oppositePortClosure path).edges := by
  have hpairing :=
    (EvenKempeFusionLens.bcRejectedCrossState_of_faceTransferBit_eq_false
      graphData data lens01 lens23 hab hac hbc site hfalse).1
  rcases lens01.exists_bcExactCrossSpliceTrail_of_pairing_false lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hcount site hpairing with
    ⟨path, htrail, hpositive, hedges, hsite⟩
  exact ⟨path, htrail, hpositive, hedges, hsite,
    (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
      data path site.1).2 hsite⟩

/-- The rejected `cb` state has the same exact retained and ambient support
consequence. -/
theorem EvenKempeFusionLens.exists_cbExactCrossSpliceTrail_of_rejected
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
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ path : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2),
      path.IsTrail ∧ 0 < path.length ∧
        path.edges =
          (lens01.cRoute.crossSplice lens23.bRoute site).support.map
            Subtype.val ∧
        site.1.1 ∈ path.edges ∧
        (retainedEdgeToAmbientEdge data site.1).1 ∈
          (data.oppositePortClosure path).edges := by
  have hpairing :=
    (EvenKempeFusionLens.cbRejectedCrossState_of_faceTransferBit_eq_false
      graphData data lens01 lens23 hab hac hbc site hfalse).1
  rcases lens01.exists_cbExactCrossSpliceTrail_of_pairing_false lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hcount site hpairing with
    ⟨path, htrail, hpositive, hedges, hsite⟩
  exact ⟨path, htrail, hpositive, hedges, hsite,
    (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
      data path site.1).2 hsite⟩

end


end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
