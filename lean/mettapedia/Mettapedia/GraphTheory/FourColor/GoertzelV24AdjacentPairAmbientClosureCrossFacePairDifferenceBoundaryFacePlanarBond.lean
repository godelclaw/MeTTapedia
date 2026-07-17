import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondBoundaryOrder

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance boundaryFacePlanarBondGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace GoertzelV24PlanarBondBoundaryOrder

/-- For a spherical graph-backed rotation with two connected cut sides,
every facial cycle changes sides at most twice. -/
theorem cutFacesHaveAtMostTwoTransitions_of_connected_sides
    (data : Data G) (deleted : Finset V)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected) :
    CutFacesHaveAtMostTwoTransitionDarts data.toRotationSystem deleted := by
  rcases hretainedConnected.nonempty with ⟨retainedVertex⟩
  rcases hdeletedConnected.nonempty with ⟨deletedVertex⟩
  have hretained : ∃ vertex, deletedRegionKeep deleted vertex :=
    ⟨retainedVertex.1, by
      simpa only [Set.mem_setOf_eq] using retainedVertex.2⟩
  have hdeleted : ∃ vertex,
      Not (deletedRegionKeep deleted vertex) :=
    ⟨deletedVertex.1, by
      simpa only [Set.mem_setOf_eq] using deletedVertex.2⟩
  rcases cutSideTransitionFaces_nonempty_of_connected
      data deleted hconnected hretained hdeleted with
    ⟨touchedFace, htouchedFace⟩
  have hretainedNotPure : ∃ face : OrbitFace data.toRotationSystem,
      face ∉ orbitFacesAllOnSide data.toRotationSystem
        (deletedRegionKeep deleted) := by
    refine ⟨touchedFace, ?_⟩
    intro hpure
    exact (Finset.disjoint_left.1
      (cutSideTransitionFaces_disjoint_allOnSide
        data.toRotationSystem deleted)) htouchedFace hpure
  have hdeletedNotPure : ∃ face : OrbitFace data.toRotationSystem,
      face ∉ orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => Not (deletedRegionKeep deleted vertex)) := by
    refine ⟨touchedFace, ?_⟩
    intro hpure
    exact (Finset.disjoint_left.1
      (cutSideTransitionFaces_disjoint_allOffSide
        data.toRotationSystem deleted)) htouchedFace hpure
  have hretainedRank := pureSideFace_cycleRankBound_of_connected
    data htwoSided hdual (deletedRegionKeep deleted)
      hretainedConnected hretainedNotPure
  have hdeletedRank := pureSideFace_cycleRankBound_of_connected
    data htwoSided hdual
      (fun vertex => Not (deletedRegionKeep deleted vertex))
      hdeletedConnected hdeletedNotPure
  exact cutFacesHaveAtMostTwoTransitions_of_sideCycleRankBounds
    data deleted hsphere hretainedRank hdeletedRank

/-- Connectedness of the primal graph and cyclic vertex rotations compute
the dual-connectedness premise in the preceding planar-bond theorem. -/
theorem cutFacesHaveAtMostTwoTransitions_of_planar_bond
    (data : Data G) (deleted : Finset V)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected) :
    CutFacesHaveAtMostTwoTransitionDarts data.toRotationSystem deleted := by
  have hprimal :
      (rotationPrimalGraph data.toRotationSystem).Connected := by
    rw [rotationPrimalGraph_toRotationSystem_eq]
    exact hconnected
  have hdual := orbitFaceInteriorDual_connected
    data.toRotationSystem hsphere.cubic hprimal hrotation
  exact cutFacesHaveAtMostTwoTransitions_of_connected_sides
    data deleted hsphere htwoSided hdual hconnected
      hretainedConnected hdeletedConnected

end GoertzelV24PlanarBondBoundaryOrder

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24PlanarBondBoundaryOrder

/-- In a graph-backed vertex-minimal counterexample, the connected adjacent
pair cut meets each quotient facial cycle at most twice. -/
theorem cutFacesHaveAtMostTwoTransitions_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) :
    CutFacesHaveAtMostTwoTransitionDarts graphData.toRotationSystem
      data.deletedVertices := by
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
      simp [deletedRegionKeep, deletedVertices, retainedVertexSet]
    rw [hkeep]
    exact retainedRegion_connected_of_vertexMinimalTaitCounterexample
      graphData minimal data
  exact cutFacesHaveAtMostTwoTransitions_of_planar_bond
    graphData data.deletedVertices minimal.spherical minimal.facesTwoSided
      hconnected minimal.vertexRotationCyclic hretainedConnected
        data.deletedRegion_connected

/-- The retained orientation of a rotation-indexed adjacent-pair boundary
edge, bundled as an exposed dart of the deleted-pair cut. -/
def rotationRetainedBoundaryDart
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    BoundaryDart graphData.toRotationSystem
      (deletedRegionKeep
        (data.rotationOrderedData graphData hcubic hrotation).deletedVertices) := by
  let ordered := data.rotationOrderedData graphData hcubic hrotation
  let dart :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      ordered port
  have hretained : deletedRegionKeep ordered.deletedVertices
      (graphData.toRotationSystem.vertOf dart) := by
    change ordered.portVertex port ∉ ordered.deletedVertices
    simp only [AdjacentPairData.deletedVertices, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨ordered.portNeFirst port, ordered.portNeSecond port⟩
  have hdeleted : graphData.toRotationSystem.vertOf
      (graphData.toRotationSystem.alpha dart) ∈ ordered.deletedVertices := by
    dsimp only [dart]
    rw [data.rotationOrdered_boundaryPortDart_eq_alpha_rotationPortDart
      graphData hcubic hrotation, graphData.toRotationSystem.alpha_involutive]
    change (data.rotationPortDart graphData port).fst ∈
      ordered.deletedVertices
    rw [data.rotationPortDart_fst graphData port]
    fin_cases port <;>
      simp [ordered, rotationOrderedData, AdjacentPairData.deletedVertices]
  exact ⟨⟨dart, hretained⟩, by
    simpa only [deletedRegionKeep, not_not] using hdeleted⟩

/-- The underlying retained dart is the restored boundary dart used by the
cross-face transfer layer. -/
theorem rotationRetainedBoundaryDart_val
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    (data.rotationRetainedBoundaryDart graphData hcubic hrotation port).1.1 =
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
        (data.rotationOrderedData graphData hcubic hrotation) port := by
  rfl

/-- The two exterior faces opposite the restored central edge are distinct
in a graph-backed vertex-minimal counterexample.  Otherwise one face would
contain two distinct retained occurrences of the connected four-edge cut. -/
theorem rotationExteriorOrbitFaces_ne_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) :
    data.rotationFirstExteriorOrbitFace graphData
        minimal.spherical.cubic minimal.vertexRotationCyclic ≠
      data.rotationSecondExteriorOrbitFace graphData
        minimal.spherical.cubic minimal.vertexRotationCyclic := by
  let ordered := data.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let firstBoundary := data.rotationRetainedBoundaryDart graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic 0
  let secondBoundary := data.rotationRetainedBoundaryDart graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic 2
  have hatMost := ordered.cutFacesHaveAtMostTwoTransitions_of_minimal
    graphData minimal
  have hunique := cutFacesHaveUniqueRetainedBoundaryDart_of_atMostTwoTransitions
    graphData.toRotationSystem ordered.deletedVertices hatMost
  intro hfaces
  change dartOrbitFace graphData.toRotationSystem
      (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
        ordered 0) =
    dartOrbitFace graphData.toRotationSystem
      (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
        ordered 2) at hfaces
  rw [← data.rotationRetainedBoundaryDart_val graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic 0,
    ← data.rotationRetainedBoundaryDart_val graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic 2] at hfaces
  change Quotient.mk _ firstBoundary.1.1 =
    Quotient.mk _ secondBoundary.1.1 at hfaces
  rw [Quotient.eq] at hfaces
  have hboundary : firstBoundary = secondBoundary :=
    hunique firstBoundary secondBoundary hfaces
  have hdart : firstBoundary.1.1 = secondBoundary.1.1 :=
    congrArg (fun boundary => boundary.1.1) hboundary
  have hedge := congrArg graphData.toRotationSystem.edgeOf hdart
  rw [data.rotationRetainedBoundaryDart_val graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic 0,
    data.rotationRetainedBoundaryDart_val graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic 2,
    data.rotationOrdered_boundaryPortDart_edgeOf graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic 0,
    data.rotationOrdered_boundaryPortDart_edgeOf graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic 2] at hedge
  have hports : (0 : Fin 4) = 2 := ordered.boundaryEdge_injective hedge
  omega

/-- Planar-bond uniqueness removes the coincident-exterior alternative from
the aligned face signature: only the face remote from both exterior wedges
remains. -/
theorem faceMatchesBothOrNeitherRotationExterior_iff_neither_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (face : OrbitFace graphData.toRotationSystem) :
    data.FaceMatchesBothOrNeitherRotationExterior graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic face ↔
      face ≠ data.rotationFirstExteriorOrbitFace graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic ∧
        face ≠ data.rotationSecondExteriorOrbitFace graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic := by
  unfold FaceMatchesBothOrNeitherRotationExterior
  constructor
  · intro haligned
    rcases haligned with hboth | hneither
    · exact False.elim
        (data.rotationExteriorOrbitFaces_ne_of_minimal graphData minimal
          (hboth.1.symm.trans hboth.2))
    · exact hneither
  · exact Or.inr

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- In a minimal spherical map, nontrivial compensated cross transfer is
equivalent to the selected singleton face avoiding both exterior wedges. -/
theorem CrossCentralExactFaceCutPair.closedTransfer_ne_refl_iff_selectedFace_remote
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross)
    (coordinate : Bool) (firstIndex secondIndex : Fin 2)
    (hcentral : crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile
        (centralEdge (baseData.rotationOrderedData graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic))) ≠ 0)
    (hfirstExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge (baseData.rotationOrderedData graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)
                (firstSidePort candidate))) ≠ 0 ↔
        candidate = firstIndex)
    (hsecondExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge (baseData.rotationOrderedData graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)
                (secondSidePort candidate))) ≠ 0 ↔
        candidate = secondIndex) :
    rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex ≠
          Equiv.refl (Bool × Bool) ↔
      (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate ≠
            baseData.rotationFirstExteriorOrbitFace graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic) ∧
        (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate ≠
            baseData.rotationSecondExteriorOrbitFace graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic) := by
  rw [pair.closedTransfer_ne_refl_iff_selectedFace_eq_both_or_neitherRotationExterior
      minimal baseData coordinate firstIndex secondIndex hcentral
        hfirstExact hsecondExact]
  exact baseData.faceMatchesBothOrNeitherRotationExterior_iff_neither_of_minimal
    graphData minimal _

/-- Equivalently, the nontrivial branch is an untouched selected face: it
contains none of the four restored boundary edges. -/
theorem CrossCentralExactFaceCutPair.closedTransfer_ne_refl_iff_selectedFace_avoids_boundary
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross)
    (coordinate : Bool) (firstIndex secondIndex : Fin 2)
    (hcentral : crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile
        (centralEdge (baseData.rotationOrderedData graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic))) ≠ 0)
    (hfirstExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge (baseData.rotationOrderedData graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)
                (firstSidePort candidate))) ≠ 0 ↔
        candidate = firstIndex)
    (hsecondExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge (baseData.rotationOrderedData graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)
                (secondSidePort candidate))) ≠ 0 ↔
        candidate = secondIndex) :
    rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex ≠
          Equiv.refl (Bool × Bool) ↔
      (∀ candidate : Fin 2,
        boundaryEdge (baseData.rotationOrderedData graphData
            minimal.spherical.cubic minimal.vertexRotationCyclic)
              (firstSidePort candidate) ∉
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate)) ∧
      (∀ candidate : Fin 2,
        boundaryEdge (baseData.rotationOrderedData graphData
            minimal.spherical.cubic minimal.vertexRotationCyclic)
              (secondSidePort candidate) ∉
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate)) := by
  have hremote := pair.closedTransfer_ne_refl_iff_selectedFace_remote
    minimal baseData coordinate firstIndex secondIndex hcentral
      hfirstExact hsecondExact
  have hfirstFace := pair.selectedFace_eq_rotationFirstExteriorOrbitFace_iff
    minimal baseData coordinate firstIndex hcentral hfirstExact
  have hsecondFace := pair.selectedFace_eq_rotationSecondExteriorOrbitFace_iff
    minimal baseData coordinate secondIndex hcentral hsecondExact
  have hfirstBoundary :=
    pair.boundaryEdge_mem_selectedFaceBoundary_iff_firstExteriorTurn
      minimal coordinate firstIndex hfirstExact
  have hsecondBoundary :=
    pair.boundaryEdge_mem_selectedFaceBoundary_iff_secondExteriorTurn
      minimal coordinate secondIndex hsecondExact
  constructor
  · intro hnontrivial
    have hne := hremote.1 hnontrivial
    constructor
    · intro candidate hmem
      apply hne.1
      exact hfirstFace.2 ((hfirstBoundary candidate).1 hmem)
    · intro candidate hmem
      apply hne.2
      exact hsecondFace.2 ((hsecondBoundary candidate).1 hmem)
  · intro havoids
    apply hremote.2
    constructor
    · intro hface
      have hturn := hfirstFace.1 hface
      exact havoids.1 0 ((hfirstBoundary 0).2 hturn)
    · intro hface
      have hturn := hsecondFace.1 hface
      exact havoids.2 0 ((hsecondBoundary 0).2 hturn)

/-- Every exact rejected-cross pair in rotation order therefore carries a
simple cross-avoiding closure whose only nontrivial-transfer alternative is
a selected cross face wholly remote from the restored cut boundary. -/
theorem CrossCentralExactFaceCutPair.exists_exactCrossSideClosedTransfer_remoteFaceNormalForm
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross) :
    ∃ (coordinate : Bool) (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G baseData.firstVertex
          baseData.secondVertex).Walk
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).retainedPort
                (firstSidePort firstIndex))
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).retainedPort
                (secondSidePort secondIndex))),
      path.IsPath ∧
        (cross : Sym2 (retainedVertexSet baseData.firstVertex
          baseData.secondVertex)) ∉ path.edges ∧
        ((baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic).crossSidePortClosure
            firstIndex secondIndex path).IsCycle ∧
        pair.centralReturnCoordinateParity coordinate
            firstIndex secondIndex = 1 ∧
        retainedEdgeToAmbientEdge
            (baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic) cross ∈
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate) ∧
        centralEdge (baseData.rotationOrderedData graphData
            minimal.spherical.cubic minimal.vertexRotationCyclic) ∉
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate) ∧
        (rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex ≠
              Equiv.refl (Bool × Bool) ↔
          (∀ candidate : Fin 2,
            boundaryEdge (baseData.rotationOrderedData graphData
                minimal.spherical.cubic minimal.vertexRotationCyclic)
                  (firstSidePort candidate) ∉
              orbitFaceBoundary graphData.toRotationSystem
                (edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge
                    (baseData.rotationOrderedData graphData
                      minimal.spherical.cubic minimal.vertexRotationCyclic)
                        cross) coordinate)) ∧
          (∀ candidate : Fin 2,
            boundaryEdge (baseData.rotationOrderedData graphData
                minimal.spherical.cubic minimal.vertexRotationCyclic)
                  (secondSidePort candidate) ∉
              orbitFaceBoundary graphData.toRotationSystem
                (edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge
                    (baseData.rotationOrderedData graphData
                      minimal.spherical.cubic minimal.vertexRotationCyclic)
                        cross) coordinate))) := by
  rcases pair.exists_exactCrossSideClosedTransfer_selectedFaceBoundarySupport
      minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      hcentral, hfirstExact, hsecondExact, hcycle, hparity,
      hsource, hnotCentral, _hidentity⟩
  exact ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcycle, hparity, hsource, hnotCentral,
    pair.closedTransfer_ne_refl_iff_selectedFace_avoids_boundary
      minimal baseData coordinate firstIndex secondIndex hcentral
        hfirstExact hsecondExact⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
