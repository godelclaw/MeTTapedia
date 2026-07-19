import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutCollarChordCrossing
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalTriangleFree

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24MinimalTriangleFree
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  collarFiniteGraphLocallyFinite
  GoertzelV24DualCycleSeparator.graphEdgeSetDecidableEq

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace ClosureRecoveryFaceTransferCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Short saturated recovery yields a remote exact adjacent-pair collar
whose chord triangles cut off precisely the two endpoint stars and whose
rotation-ordered deletion has a compatible Tait coloring. -/
theorem exists_remote_endpoint_star_chord_triangles_of_arcLength_le_four
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (hshort : rebaseCircuit.arcLength ≤ 4) :
    rebaseCircuit.arcLength = 4 ∧
      ∃ walk :
          (interiorDualGraph
            (orbitFaceBoundary graphData.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace graphData.toRotationSystem))).Walk
            rebaseCircuit.first.dualFace rebaseCircuit.first.dualFace,
        walk.IsCycle ∧
          ¬ (G.deleteEdges
            (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
              (pairwiseUniqueSharedInteriorEdges graphData minimal)
              walk)).Connected ∧
          (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
            (pairwiseUniqueSharedInteriorEdges graphData minimal)
              walk).ncard = 4 ∧
          (let removed := dualWalkCrossingEdges
              (orbitFaceBoundary graphData.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace graphData.toRotationSystem))
              (pairwiseUniqueSharedInteriorEdges graphData minimal) walk
            ∃ component :
                (G.deleteEdges
                  (GoertzelV24DualCycleSeparator.dualWalkPrimalCut
                    graphData
                    (pairwiseUniqueSharedInteriorEdges graphData minimal)
                    walk)).ConnectedComponent,
              ∃ first second : V,
                first ≠ second ∧ component.supp = {first, second} ∧
                  G.Adj first second ∧
                  crossingEdgeFinset G
                      (fun vertex => vertex ∈ component.supp) =
                    removed ∧
                  HasRotationOrderedCyclicKempeFusionChainNormalForm
                    graphData minimal first second ∧
                  ∃ internalEdge : G.edgeSet,
                    ∃ leftFace rightFace : AmbientFace
                        (Finset.univ : Finset
                          (OrbitFace graphData.toRotationSystem)),
                      ∃ firstTriangle secondTriangle :
                          (interiorDualGraph
                            (orbitFaceBoundary graphData.toRotationSystem)
                            (Finset.univ : Finset
                              (OrbitFace graphData.toRotationSystem))).Walk
                            leftFace leftFace,
                        ∃ firstComponent :
                            (G.deleteEdges
                              (GoertzelV24DualCycleSeparator.dualWalkPrimalCut
                                graphData
                                (pairwiseUniqueSharedInteriorEdges
                                  graphData minimal)
                                firstTriangle)).ConnectedComponent,
                          ∃ secondComponent :
                              (G.deleteEdges
                                (GoertzelV24DualCycleSeparator.dualWalkPrimalCut
                                  graphData
                                  (pairwiseUniqueSharedInteriorEdges
                                    graphData minimal)
                                  secondTriangle)).ConnectedComponent,
                            internalEdge.1 = s(first, second) ∧
                              internalEdge ∉ removed ∧
                              internalEdge ∈ orbitFaceBoundary
                                graphData.toRotationSystem leftFace.1 ∧
                              internalEdge ∈ orbitFaceBoundary
                                graphData.toRotationSystem rightFace.1 ∧
                              firstTriangle.IsCycle ∧
                              firstTriangle.length = 3 ∧
                              secondTriangle.IsCycle ∧
                              secondTriangle.length = 3 ∧
                              crossingEdgeFinset G
                                  (fun vertex =>
                                    vertex ∈ firstComponent.supp) =
                                dualWalkCrossingEdges
                                  (orbitFaceBoundary
                                    graphData.toRotationSystem)
                                  (Finset.univ : Finset
                                    (OrbitFace
                                      graphData.toRotationSystem))
                                  (pairwiseUniqueSharedInteriorEdges
                                    graphData minimal) firstTriangle ∧
                              crossingEdgeFinset G
                                  (fun vertex =>
                                    vertex ∈ secondComponent.supp) =
                                dualWalkCrossingEdges
                                  (orbitFaceBoundary
                                    graphData.toRotationSystem)
                                  (Finset.univ : Finset
                                    (OrbitFace
                                      graphData.toRotationSystem))
                                  (pairwiseUniqueSharedInteriorEdges
                                    graphData minimal) secondTriangle ∧
                              ((firstComponent.supp = {first} ∧
                                  secondComponent.supp = {second}) ∨
                                (firstComponent.supp = {second} ∧
                                  secondComponent.supp = {first})) ∧
                              internalEdge ∈ dualWalkCrossingEdges
                                (orbitFaceBoundary
                                  graphData.toRotationSystem)
                                (Finset.univ : Finset
                                  (OrbitFace graphData.toRotationSystem))
                                (pairwiseUniqueSharedInteriorEdges
                                  graphData minimal) firstTriangle ∧
                              internalEdge ∈ dualWalkCrossingEdges
                                (orbitFaceBoundary
                                  graphData.toRotationSystem)
                                (Finset.univ : Finset
                                  (OrbitFace graphData.toRotationSystem))
                                (pairwiseUniqueSharedInteriorEdges
                                  graphData minimal) secondTriangle ∧
                              dualWalkCrossingEdges
                                  (orbitFaceBoundary
                                    graphData.toRotationSystem)
                                  (Finset.univ : Finset
                                    (OrbitFace
                                      graphData.toRotationSystem))
                                  (pairwiseUniqueSharedInteriorEdges
                                    graphData minimal) firstTriangle ≠
                                dualWalkCrossingEdges
                                  (orbitFaceBoundary
                                    graphData.toRotationSystem)
                                  (Finset.univ : Finset
                                    (OrbitFace
                                      graphData.toRotationSystem))
                                  (pairwiseUniqueSharedInteriorEdges
                                    graphData minimal) secondTriangle) ∧
          (∀ face ∈ walk.support,
            centralEdge
                (baseData.rotationOrderedData graphData
                  minimal.spherical.cubic minimal.vertexRotationCyclic) ∉
              orbitFaceBoundary graphData.toRotationSystem face.1) ∧
          (∀ face ∈ walk.support, ∀ port : Fin 4,
            boundaryEdge
                (baseData.rotationOrderedData graphData
                  minimal.spherical.cubic minimal.vertexRotationCyclic)
                  port ∉
              orbitFaceBoundary graphData.toRotationSystem face.1) := by
  have hcyclic : CyclicallyFiveEdgeConnected G :=
    GoertzelV24FourEdgeCutGluing.cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
      graphData minimal
  rcases
      circuit.exists_remote_primal_separator_with_four_port_opposite_walk_chord_of_arcLength_le_four
        hcyclic hminimal hlength hshort with
    ⟨hrebaseLength, walk, hcycle, hdelete, hcutCard, _hoppositeChord,
      hcentral, hboundary⟩
  have hregular : G.IsRegularOfDegree 3 :=
    graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hdual := orbitFaceInteriorDual_connected
    graphData.toRotationSystem minimal.spherical.cubic
      minimal.primalConnected minimal.vertexRotationCyclic
  have hwalkLength : walk.length = 4 := by
    calc
      walk.length =
          (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
            (pairwiseUniqueSharedInteriorEdges graphData minimal)
              walk).ncard :=
        (GoertzelV24DualCycleSeparator.ncard_dualWalkPrimalCut_eq_length_of_isCycle
          graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
            walk hcycle).symm
      _ = 4 := hcutCard
  rcases
      GoertzelV24DualCycleSeparator.exists_primalCut_adjacent_pair_collar_of_isCycle_of_length_eq_four
        graphData hregular hconnected hcyclic minimal.facesTwoSided
          (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle
            hwalkLength hdelete with
    ⟨component, first, second, hfirstSecond, hsupp, hadj,
      hcomponentBoundary, _internalEdge, _hinternalValue,
      _hinternalNotRemoved, _hfirstBoundaryCard,
      _hsecondBoundaryCard⟩
  have hsideEq :
      (fun vertex => vertex ∈ component.supp) =
        (fun vertex => vertex ∈ ({first, second} : Set V)) := by
    funext vertex
    rw [hsupp]
  have hpairBoundary := hcomponentBoundary
  rw [hsideEq] at hpairBoundary
  have hstars :=
    GoertzelV24DualCycleSeparator.exists_chord_triangle_singleton_components_of_adjacent_pair_boundary_eq
      graphData hregular hconnected hcyclic minimal.vertexRotationCyclic
        minimal.facesTwoSided hdual minimal.spherical
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle
          hwalkLength hadj hpairBoundary
  dsimp only at hstars
  have htransfer :=
    exists_rotationOrderedCyclicKempeFusionChainNormalForm_of_vertexMinimalTaitCounterexample
      graphData minimal hadj
  refine ⟨hrebaseLength, walk, hcycle, hdelete, hcutCard, ?_, hcentral,
    hboundary⟩
  dsimp only
  exact ⟨component, first, second, hfirstSecond, hsupp, hadj,
    hcomponentBoundary, htransfer, hstars⟩

end ClosureRecoveryFaceTransferCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
