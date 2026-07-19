import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitPortPairingReductionBridgeCyclicCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutKempeEscape
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondBoundaryOrder

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24FourEdgeCutComplementCoordinates
open GoertzelV24FourEdgeCutAlternatingTrail
open GoertzelV24FourEdgeCutKempeEscape
open GoertzelV24FourEdgeCutNoncrossingInterfaces
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

local instance reductionKempeEscapeGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance reductionKempeEscapeRetainedVertexSetFintype
    (first second : V) :
    Fintype (retainedVertexSet first second) :=
  retainedVertexSetFintype first second

local instance reductionKempeEscapeRetainedVertexSetDecidableEq
    (first second : V) :
    DecidableEq (retainedVertexSet first second) :=
  retainedVertexSetDecidableEq first second

/-- The physical port coordinates transported to the computed boundary
darts of the adjacent-pair deletion. -/
def cyclicBoundaryOrder
    (graphData : Data G) (data : AdjacentPairData G) :
    Fin 4 ≃ BoundaryDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices) :=
  (boundaryPortEquiv SquareReductionSide.join12_30).symm.trans
    (orderedBoundaryPositionEquiv
      (data.rootedRotationSystem graphData) data.deletedVertices
      (data.leftCrossing SquareReductionSide.join12_30)
      (data.rightCrossing SquareReductionSide.join12_30)
      (data.pairedCut_boundary (data.rootedGraphData graphData)
        SquareReductionSide.join12_30)
      (data.leftCrossing_injective SquareReductionSide.join12_30)
      (data.rightCrossing_injective SquareReductionSide.join12_30)
      (data.pairedCuts_disjoint SquareReductionSide.join12_30))

/-- The port coordinate really names its corresponding restored boundary
edge. -/
theorem cyclicBoundaryOrder_edgeOf
    (graphData : Data G) (data : AdjacentPairData G) (port : Fin 4) :
    (data.rootedRotationSystem graphData).edgeOf
        ((data.cyclicBoundaryOrder graphData port).1.1) =
      data.boundaryEdge port := by
  let side := SquareReductionSide.join12_30
  let position := (boundaryPortEquiv side).symm port
  change (data.rootedRotationSystem graphData).edgeOf
      ((orderedBoundaryPositionEquiv
        (data.rootedRotationSystem graphData) data.deletedVertices
        (data.leftCrossing side) (data.rightCrossing side)
        (data.pairedCut_boundary (data.rootedGraphData graphData) side)
        (data.leftCrossing_injective side)
        (data.rightCrossing_injective side)
        (data.pairedCuts_disjoint side) position).1.1) =
      data.boundaryEdge port
  rw [data.orderedBoundaryPosition_edgeOf graphData side position]
  congr 1
  change boundaryPortEquiv side position = port
  exact (boundaryPortEquiv side).apply_symm_apply port

/-- The retained endpoint of the boundary dart in a physical port
coordinate is the named retained port vertex. -/
@[simp]
theorem cyclicBoundaryOrder_vertOf
    (graphData : Data G) (data : AdjacentPairData G) (port : Fin 4) :
    (data.rootedRotationSystem graphData).vertOf
        ((data.cyclicBoundaryOrder graphData port).1.1) =
      data.portVertex port := by
  let side := SquareReductionSide.join12_30
  let position := (boundaryPortEquiv side).symm port
  have hport : side.boundaryPort position = port := by
    change boundaryPortEquiv side position = port
    exact (boundaryPortEquiv side).apply_symm_apply port
  change (data.rootedRotationSystem graphData).vertOf
      ((orderedBoundaryPositionEquiv
        (data.rootedRotationSystem graphData) data.deletedVertices
        (data.leftCrossing side) (data.rightCrossing side)
        (data.pairedCut_boundary (data.rootedGraphData graphData) side)
        (data.leftCrossing_injective side)
        (data.rightCrossing_injective side)
        (data.pairedCuts_disjoint side) position).1.1) =
      data.portVertex port
  rcases position with step | step
  · rw [orderedBoundaryPositionEquiv_apply_left,
      data.leftBoundaryDart_vertex]
    exact congrArg data.portVertex hport
  · rw [orderedBoundaryPositionEquiv_apply_right,
      data.rightBoundaryDart_vertex]
    exact congrArg data.portVertex hport

/-- The standard positive rotation of the physical ports transports to the
computed positive boundary successor. -/
theorem cyclicBoundaryOrder_permCongr_finRotate
    (graphData : Data G) (data : AdjacentPairData G) :
    (data.cyclicBoundaryOrder graphData).permCongr (finRotate 4) =
      data.squareExpectedBoundaryCycle graphData
        SquareReductionSide.join12_30 := by
  let side := SquareReductionSide.join12_30
  let positions := orderedBoundaryPositionEquiv
    (data.rootedRotationSystem graphData) data.deletedVertices
    (data.leftCrossing side) (data.rightCrossing side)
    (data.pairedCut_boundary (data.rootedGraphData graphData) side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.pairedCuts_disjoint side)
  have hfinite :
      (boundaryPortEquiv side).symm.permCongr (finRotate 4) =
        oppositeBoundaryCycle 2 := by
    rw [← boundaryPortEquiv_permCongr_oppositeBoundaryCycle side]
    apply Equiv.ext
    intro position
    change (boundaryPortEquiv side).symm
        (boundaryPortEquiv side
          (oppositeBoundaryCycle 2
            ((boundaryPortEquiv side).symm
              (boundaryPortEquiv side position)))) =
      oppositeBoundaryCycle 2 position
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change (((boundaryPortEquiv side).symm.trans positions).permCongr
      (finRotate 4)) = positions.permCongr (oppositeBoundaryCycle 2)
  rw [permCongr_trans_equiv, hfinite]

/-- The adjacent-pair deletion has a common cyclic boundary coordinate on
both sides of its planar bond. -/
def cyclicFourBoundaryDataOfOrder
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData) :
    CyclicFourBoundaryData (data.rootedRotationSystem graphData)
      data.deletedVertices where
  boundaryOrder := data.cyclicBoundaryOrder graphData
  deleted_order := horder.trans
    (data.cyclicBoundaryOrder_permCongr_finRotate graphData).symm
  retained_order := by
    have hconnected : G.Connected := by
      rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
      exact minimal.primalConnected
    have hretainedConnected :
        (G.induce {vertex |
          deletedRegionKeep data.deletedVertices vertex}).Connected := by
      have hkeep : {vertex |
          deletedRegionKeep data.deletedVertices vertex} =
          retainedVertexSet data.firstVertex data.secondVertex := by
        ext vertex
        simp [deletedRegionKeep, AdjacentPairData.deletedVertices,
          retainedVertexSet]
      rw [hkeep]
      exact retainedRegion_connected_of_vertexMinimalTaitCounterexample
        graphData minimal data
    have hinverse :=
      retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond
        (data.rootedGraphData graphData) data.deletedVertices
        (by simpa [rootedGraphData, rootedRotationSystem] using
          minimal.spherical)
        (by simpa [rootedGraphData, rootedRotationSystem] using
          minimal.facesTwoSided)
        hconnected
        (by simpa [rootedGraphData, rootedRotationSystem] using
          minimal.vertexRotationCyclic)
        hretainedConnected data.deletedRegion_connected
    rw [hinverse, horder,
      data.cyclicBoundaryOrder_permCongr_finRotate graphData]

/-- Two retained trails joining the opposite port pairs of a cyclically
ordered adjacent-pair deletion cannot be edge-disjoint. -/
theorem no_edge_disjoint_opposite_retained_trails_of_order
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData)
    (firstTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (secondTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hfirstTrail : firstTrail.IsTrail)
    (hsecondTrail : secondTrail.IsTrail)
    (hdisjoint : firstTrail.edges.Disjoint secondTrail.edges) :
    False := by
  let rooted := data.rootedGraphData graphData
  let cyclicData := data.cyclicFourBoundaryDataOfOrder graphData minimal horder
  let separator := data.oppositePortClosure firstTrail
  let route := data.retainedWalkToAmbient secondTrail
  have hsphere : OrbitSphericalCubicMapData rooted.toRotationSystem := by
    simpa [rooted, rootedGraphData, rootedRotationSystem] using
      minimal.spherical
  have htwoSided : OrbitFacesTwoSided rooted.toRotationSystem := by
    simpa [rooted, rootedGraphData, rootedRotationSystem] using
      minimal.facesTwoSided
  have hrotation : VertexRotationCyclic rooted.toRotationSystem := by
    simpa [rooted, rootedGraphData, rootedRotationSystem] using
      minimal.vertexRotationCyclic
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
    exact minimal.primalConnected
  have hprimal : (rotationPrimalGraph rooted.toRotationSystem).Connected := by
    rw [rotationPrimalGraph_toRotationSystem_eq]
    exact hconnected
  have hdual : (interiorDualGraph
      (orbitFaceBoundary rooted.toRotationSystem)
      (Finset.univ : Finset (OrbitFace rooted.toRotationSystem))).Connected :=
    orbitFaceInteriorDual_connected rooted.toRotationSystem hsphere.cubic
      hprimal hrotation
  have hseparator : separator.IsTrail :=
    data.oppositePortClosure_isTrail firstTrail hfirstTrail
  have hzero :
      (rooted.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 0).1.1).1 ∈ separator.edges := by
    rw [show rooted.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 0).1.1 = data.boundaryEdge 0 by
      simpa [rooted, cyclicData, cyclicFourBoundaryDataOfOrder] using
        data.cyclicBoundaryOrder_edgeOf graphData 0]
    simpa [separator] using
      (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff
        firstTrail 0).2 (Or.inl rfl)
  have hone :
      (rooted.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 1).1.1).1 ∉ separator.edges := by
    rw [show rooted.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 1).1.1 = data.boundaryEdge 1 by
      simpa [rooted, cyclicData, cyclicFourBoundaryDataOfOrder] using
        data.cyclicBoundaryOrder_edgeOf graphData 1]
    simpa [separator] using
      (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff
        firstTrail 1).not
  have hthree :
      (rooted.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 3).1.1).1 ∉ separator.edges := by
    rw [show rooted.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 3).1.1 = data.boundaryEdge 3 by
      simpa [rooted, cyclicData, cyclicFourBoundaryDataOfOrder] using
        data.cyclicBoundaryOrder_edgeOf graphData 3]
    simpa [separator] using
      (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff
        firstTrail 3).not
  have hsecondNil : ¬secondTrail.Nil :=
    SimpleGraph.Walk.not_nil_of_ne
      (data.retainedPort_injective.ne (by decide))
  have hrouteNil : ¬route.Nil :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.retainedWalkToAmbient_not_nil
      data secondTrail hsecondNil
  have hrouteTrail : route.IsTrail :=
    data.retainedWalkToAmbient_isTrail hsecondTrail
  have hambientDisjoint :
      (data.retainedWalkToAmbient firstTrail).edges.Disjoint
        (data.retainedWalkToAmbient secondTrail).edges := by
    simp only [retainedWalkToAmbient, SimpleGraph.Walk.edges_map]
    exact hdisjoint.map (Sym2.map.injective Subtype.val_injective)
  have hrouteDisjoint : ∀ edge : G.edgeSet,
      edge.1 ∈ route.edges → edge.1 ∉ separator.edges := by
    intro edge hroute hseparatorEdge
    change edge.1 ∈
        ((data.retainedWalkToAmbient firstTrail).append
          data.oppositePortCentralReturn).edges at hseparatorEdge
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at hseparatorEdge
    rcases hseparatorEdge with hfirst | hreturn
    · exact hambientDisjoint hfirst hroute
    · exact
        (data.retainedWalkToAmbient_edges_disjoint_oppositePortCentralReturn
          secondTrail) hroute hreturn
  have hfirstNe : route.firstDart hrouteNil ≠
      (cyclicData.boundaryOrder 1).1.1 := by
    intro hdart
    have hedge := congrArg rooted.toRotationSystem.edgeOf hdart
    have hboundary : rooted.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 1).1.1 = data.boundaryEdge 1 := by
      exact data.cyclicBoundaryOrder_edgeOf graphData 1
    rw [hboundary] at hedge
    have hmem : (rooted.toRotationSystem.edgeOf
        (route.firstDart hrouteNil)).1 ∈ route.edges := by
      exact route.mk_start_snd_mem_edges hrouteNil
    rw [hedge] at hmem
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      secondTrail 1 hmem
  have hlastNe : rooted.toRotationSystem.alpha
      (route.lastDart hrouteNil) ≠
        (cyclicData.boundaryOrder 3).1.1 := by
    intro hdart
    have hedge := congrArg rooted.toRotationSystem.edgeOf hdart
    have hboundary : rooted.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 3).1.1 = data.boundaryEdge 3 := by
      exact data.cyclicBoundaryOrder_edgeOf graphData 3
    rw [rooted.toRotationSystem.edge_alpha, hboundary] at hedge
    have hmem : (rooted.toRotationSystem.edgeOf
        (route.lastDart hrouteNil)).1 ∈ route.edges := by
      exact route.mk_penultimate_end_mem_edges hrouteNil
    rw [hedge] at hmem
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      secondTrail 3 hmem
  have hplanar := no_disjoint_trail_between_one_and_three
    rooted htwoSided hdual hconnected hsphere hsphere.cubic hrotation
      data.deletedVertices cyclicData separator hseparator hzero hone hthree
  have hleft : rooted.toRotationSystem.vertOf
      (cyclicData.boundaryOrder 1).1.1 = data.portVertex 1 :=
    data.cyclicBoundaryOrder_vertOf graphData 1
  have hright : rooted.toRotationSystem.vertOf
      (cyclicData.boundaryOrder 3).1.1 = data.portVertex 3 :=
    data.cyclicBoundaryOrder_vertOf graphData 3
  rw [hleft, hright] at hplanar
  exact hplanar route hrouteNil hrouteTrail hrouteDisjoint hfirstNe hlastNe

/-- The all-equal coloring supplied by the alternate square reduction has
a strict adjacent `01|23` Kempe successor. -/
theorem exists_deletedColoring_adjacent01_23_of_order
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData) :
    ∃ deletedColoring :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).EdgeColoring Color,
      IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          deletedColoring ∧
        SquareBoundaryWord.Adjacent01_23
          (data.degreeTwoBoundaryData.colorWord deletedColoring) := by
  rcases
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.exists_deletedColoring_allEqual_of_order
        graphData minimal data horder with
    ⟨constantColoring, hconstantColoring, hAllEqual⟩
  let word := data.degreeTwoBoundaryData.colorWord constantColoring
  have hconstant : ∀ port : Fin 4, word port = word 0 := by
    intro port
    fin_cases port
    · rfl
    · exact hAllEqual.1.symm
    · exact (hAllEqual.1.trans hAllEqual.2.1).symm
    · exact (hAllEqual.1.trans
        (hAllEqual.2.1.trans hAllEqual.2.2)).symm
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hwell := data.degreeTwoBoundaryData_wellFormed hcubic
  have hnoOppositeTrails :
      ∀ (firstTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.degreeTwoBoundaryData.defectVertex 0)
            (data.degreeTwoBoundaryData.defectVertex 2))
        (secondTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.degreeTwoBoundaryData.defectVertex 1)
            (data.degreeTwoBoundaryData.defectVertex 3)),
        firstTrail.IsTrail → secondTrail.IsTrail →
          firstTrail.edges.Disjoint secondTrail.edges → False := by
    intro firstTrail secondTrail hfirst hsecond hdisjoint
    exact data.no_edge_disjoint_opposite_retained_trails_of_order
      graphData minimal horder firstTrail secondTrail hfirst hsecond hdisjoint
  rcases exists_adjacent_kempe_successor_of_no_disjoint_opposite_trails
      data.degreeTwoBoundaryData hwell constantColoring hconstantColoring
      hconstant hnoOppositeTrails with
    ⟨adjacentColoring, hAdjacentColoring, hAdjacent⟩
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  have hsameSide :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable adjacentColoring hAdjacentColoring
  rcases hAdjacent with hcanonical | halternate
  · exact ⟨adjacentColoring, hAdjacentColoring, hcanonical⟩
  · exfalso
    exact halternate.2.2
      (hsameSide.1.symm.trans halternate.2.1.symm)

/-- Reading any adjacent pair from its two local cubic rotations supplies
both its cyclic port order and a strict `01|23` deleted coloring. -/
theorem exists_rotationOrdered_deletedColoring_adjacent01_23
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) :
    let ordered := data.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    ordered.PortsFollowCyclicDeletedBoundaryOrder graphData ∧
      ∃ deletedColoring :
          (DeletedAdjacentPairGraph G ordered.firstVertex
            ordered.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
            (DeletedAdjacentPairGraph G ordered.firstVertex
              ordered.secondVertex) deletedColoring ∧
          SquareBoundaryWord.Adjacent01_23
            (ordered.degreeTwoBoundaryData.colorWord deletedColoring) := by
  dsimp only
  let ordered := data.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have horder : ordered.PortsFollowCyclicDeletedBoundaryOrder graphData :=
    data.rotationOrderedData_portsFollowCyclicDeletedBoundaryOrder graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
  exact ⟨horder,
    ordered.exists_deletedColoring_adjacent01_23_of_order
      graphData minimal horder⟩

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
