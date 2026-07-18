import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainTransfer

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Equal endpoint indices leave the endpoint-only involution after closing
the rejected diagonal cross through the central return. -/
theorem rejectedCrossCentralReturnClosedTransfer_eq_endpointOnly_of_indices_eq
    (firstIndex secondIndex : Fin 2)
    (hindices : firstIndex = secondIndex) :
    rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
      signedRoutePermutation true false := by
  rw [rejectedCrossCentralReturnClosedTransfer_eq_endpointOnly,
    (crossSideChannelEndpointFlip_eq_false_iff
      firstIndex secondIndex).2 hindices]
  rfl

/-- The forced diagonal common-run transfer cancels the endpoint bit of an
active equal-index rejected-cross closure and leaves the pure route flip. -/
theorem diagonal_mul_rejectedCrossCentralReturnClosedTransfer_eq_routeOnly_of_indices_eq
    (firstIndex secondIndex : Fin 2)
    (hindices : firstIndex = secondIndex) :
    signedRoutePermutation true true *
        rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
      signedRoutePermutation false true := by
  rw [rejectedCrossCentralReturnClosedTransfer_eq_endpointOnly_of_indices_eq
    firstIndex secondIndex hindices]
  simpa using (signedRoutePermutation_xor true true false true).symm

/-- In a signed fusion-chain resolution, a clean four-arm branch composes
with the active rejected-cross closure to the pure route flip. Cycle and
descent branches satisfy the predicate without a transfer equation. -/
def LocalizedFusionChainSignedTransferResolution.CleanClosedTransferIsRouteOnly
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (resolution : LocalizedFusionChainSignedTransferResolution pair
      oldCross face)
    (firstIndex secondIndex : Fin 2) : Prop :=
  match resolution with
  | .cleanFourArms _ _ _ _ _ certificate _ =>
      certificate.signedTransfer *
          rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
        signedRoutePermutation false true
  | _ => True

/-- Exact diagonal transfer and equality of the endpoint indices imply the
clean closed-transfer route-only equation. -/
theorem LocalizedFusionChainSignedTransferResolution.cleanClosedTransfer_isRouteOnly
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (resolution : LocalizedFusionChainSignedTransferResolution pair
      oldCross face)
    (hdiagonal : resolution.CleanTransferIsDiagonal)
    (firstIndex secondIndex : Fin 2)
    (hindices : firstIndex = secondIndex) :
    resolution.CleanClosedTransferIsRouteOnly firstIndex secondIndex := by
  cases resolution with
  | parallelArmCycle => trivial
  | crossedArmCycle => trivial
  | cleanFourArms profile splice clean mergeState splitState certificate
      transfer_ne_refl =>
      change certificate.signedTransfer =
        signedRoutePermutation true true at hdiagonal
      change certificate.signedTransfer *
          rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
        signedRoutePermutation false true
      rw [hdiagonal]
      exact
        diagonal_mul_rejectedCrossCentralReturnClosedTransfer_eq_routeOnly_of_indices_eq
          firstIndex secondIndex hindices
  | alignedBubbleCycle => trivial
  | strictlyShorterMixedPortCycles => trivial
  | orderInversionPrimalCycle => trivial

/-- The successor trichotomy with its clean fusion-chain branch carrying
both the diagonal local transfer and its pure-route closed composition. -/
def LocalizedFusionSuccessorResolution.RouteOnlyCompositionOutcome
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    {face : OrbitFace graphData.toRotationSystem}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    (successors : LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion)
    (firstIndex secondIndex : Fin 2) : Prop :=
  successors.prefixSuccessor.edges.Disjoint
      successors.suffixSuccessor.edges ∨
    (∃ (nextCross : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet)
        (nextPair : CrossCentralExactFaceCutPair graphData data nextCross),
      nextCross ≠ cross ∧
        retainedEdgeToAmbientEdge data nextCross ∈
          orbitFaceBoundary graphData.toRotationSystem face ∧
        nextPair.prefixTrail = successors.prefixSuccessor ∧
        nextPair.suffixTrail = successors.suffixSuccessor) ∨
    (∃ successor : LocalizedSuccessorFusionChainProfile cross face
        successors.prefixSuccessor successors.suffixSuccessor,
      ∃ signed : LocalizedFusionChainSignedTransferResolution
          successor.pair cross face,
        signed.CleanTransferIsDiagonal ∧
          signed.CleanClosedTransferIsRouteOnly firstIndex secondIndex)

/-- In an equal-index state, the finite successor resolution has an exact
pure-route composition in every clean fusion-chain branch. -/
theorem LocalizedFusionSuccessorResolution.finite_routeOnlyComposition_outcome_of_indices_eq
    (graphData : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross}
    {face : OrbitFace graphData.toRotationSystem}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    (successors : LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion)
    (firstIndex secondIndex : Fin 2)
    (hindices : firstIndex = secondIndex) :
    successors.RouteOnlyCompositionOutcome firstIndex secondIndex := by
  unfold LocalizedFusionSuccessorResolution.RouteOnlyCompositionOutcome
  have houtcome := successors.finite_diagonalTransfer_outcome
    graphData minimal baseData
  unfold LocalizedFusionSuccessorResolution.DiagonalTransferOutcome at houtcome
  rcases houtcome with hdisjoint | hrebase | hclean
  · exact Or.inl hdisjoint
  · exact Or.inr (Or.inl hrebase)
  · rcases hclean with ⟨successor, signed, hdiagonal⟩
    exact Or.inr (Or.inr ⟨successor, signed, hdiagonal,
      signed.cleanClosedTransfer_isRouteOnly hdiagonal
        firstIndex secondIndex hindices⟩)

/-- A support-certified remote resolution with the active closed monodromy
composed through every clean fusion-chain branch. -/
def CrossSideRemoteFusionChainResolution.RouteOnlyCompositionOutcome
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    {coordinate : Bool}
    (resolution : CrossSideRemoteFusionChainResolution graphData data cross
      pair coordinate)
    (firstIndex secondIndex : Fin 2) : Prop :=
  (∃ (hroot : resolution.firstRoot ∈
        retainedVertexSet data.firstVertex data.secondVertex)
      (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk ⟨resolution.firstRoot, hroot⟩
          ⟨resolution.firstRoot, hroot⟩),
    retainedFusion.IsCycle ∧
      data.retainedWalkToAmbient retainedFusion = resolution.firstFusion) ∨
    (∃ (hroot : resolution.secondRoot ∈
        retainedVertexSet data.firstVertex data.secondVertex)
      (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk ⟨resolution.secondRoot, hroot⟩
          ⟨resolution.secondRoot, hroot⟩),
    retainedFusion.IsCycle ∧
      data.retainedWalkToAmbient retainedFusion = resolution.secondFusion) ∨
    (∃ successors : LocalizedFusionSuccessorResolution pair
        (edgeCrossFaceCoordinateOrbitFace graphData
          (retainedEdgeToAmbientEdge data cross) coordinate)
        resolution.firstFusion resolution.secondFusion,
      successors.RouteOnlyCompositionOutcome firstIndex secondIndex)

/-- Every equal-index remote resolution in a minimal spherical
counterexample has the route-only-composition-refined outcome. -/
theorem CrossSideRemoteFusionChainResolution.routeOnlyComposition_outcome_of_indices_eq
    (graphData : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross}
    {coordinate : Bool}
    (resolution : CrossSideRemoteFusionChainResolution graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross pair coordinate)
    (firstIndex secondIndex : Fin 2)
    (hindices : firstIndex = secondIndex) :
    resolution.RouteOnlyCompositionOutcome firstIndex secondIndex := by
  unfold CrossSideRemoteFusionChainResolution.RouteOnlyCompositionOutcome
  rcases resolution.outcome with hfirst | hsecond | hsuccessors
  · exact Or.inl hfirst
  · exact Or.inr (Or.inl hsecond)
  · rcases hsuccessors with ⟨successors⟩
    exact Or.inr (Or.inr ⟨successors,
      successors.finite_routeOnlyComposition_outcome_of_indices_eq
        graphData minimal baseData firstIndex secondIndex hindices⟩)

/-- Complete finite monodromy normal form of a remote fusion-chain witness.
Mixed endpoint indices give the identity. Equal indices activate a remote
resolution whose clean terminal composition is the pure route flip. -/
def CrossSideRemoteFusionChainTransferWitness.FiniteClosedMonodromyOutcome
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    (witness : CrossSideRemoteFusionChainTransferWitness graphData data
      cross pair) : Prop :=
  (witness.firstIndex ≠ witness.secondIndex ∧
      rejectedCrossCentralReturnClosedTransfer witness.firstIndex
          witness.secondIndex = Equiv.refl (Bool × Bool)) ∨
    (∃ (_active : CrossSideRemoteFusionChainActiveState witness)
        (resolution : CrossSideRemoteFusionChainResolution graphData data
          cross pair witness.coordinate),
      resolution.RouteOnlyCompositionOutcome witness.firstIndex
        witness.secondIndex)

/-- Every remote witness in a minimal spherical counterexample realizes its
complete two-state closed-monodromy normal form. -/
theorem CrossSideRemoteFusionChainTransferWitness.finiteClosedMonodromy_outcome_of_minimal
    (graphData : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross}
    (witness : CrossSideRemoteFusionChainTransferWitness graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross pair) :
    witness.FiniteClosedMonodromyOutcome := by
  unfold CrossSideRemoteFusionChainTransferWitness.FiniteClosedMonodromyOutcome
  rcases witness.mixedIndices_or_activeState with hmixed | hactive
  · exact Or.inl hmixed
  · rcases hactive with ⟨active⟩
    rcases active.exists_resolution with ⟨resolution⟩
    exact Or.inr ⟨active, resolution,
      resolution.routeOnlyComposition_outcome_of_indices_eq
        graphData minimal baseData witness.firstIndex witness.secondIndex
          active.indices_eq⟩

/-- The source-closure alternative sharpened to the complete finite closed
monodromy normal form on its remote branch. -/
theorem CrossCentralExactFaceCutPair.sourceClosureCycleDescent_or_exists_finiteClosedMonodromy
    {graphData : SimpleGraphDartRotation.Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross) :
    CrossCentralSourceClosureCycleDescent pair ∨
      (∃ witness : CrossSideRemoteFusionChainTransferWitness graphData
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) cross pair,
        witness.FiniteClosedMonodromyOutcome) := by
  rcases
      pair.sourceClosureCycleDescent_or_exists_exactCrossSideClosedTransfer_remoteFaceFusionChainResolution
        minimal baseData with hdescent | hwitness
  · exact Or.inl hdescent
  · rcases hwitness with ⟨witness⟩
    exact Or.inr ⟨witness,
      witness.finiteClosedMonodromy_outcome_of_minimal
        graphData minimal baseData⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
