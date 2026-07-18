import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunEndpointFacePairing

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Complete local chiral certificate for a clean common-run splice. It
stores the two actual endpoint rotations together with the derived facial
and prefix/suffix route transport equations. -/
structure LocalizedCommonRunEndpointChiralCertificate
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (mergeState : LocalizedCommonRunMergeArmState splice)
    (splitState : LocalizedCommonRunSplitArmState splice) where
  mergeRotation : RotationSystem.ThreeDartRotation
    graphData.toRotationSystem mergeState.ambientOutgoingDarts
  splitRotation : RotationSystem.ThreeDartRotation
    graphData.toRotationSystem splitState.ambientOutgoingDarts
  trunkFaceSide_complement :
    splice.splitTrunkFaceSide = !splice.mergeTrunkFaceSide
  routeFace_eq :
    mergeRotation.displayedSideOrbitFace
        (mergeState.ambientRoutePosition
          (mergeState.ambientTrunkFaceRoute mergeRotation))
        (!splice.mergeTrunkFaceSide) =
      splitRotation.displayedSideOrbitFace
        (splitState.ambientRoutePosition
          (splitState.ambientTrunkFaceRoute splitRotation))
        splice.mergeTrunkFaceSide
  routeFlip_eq_frameParity :
    splice.ambientEndpointRouteFlip mergeState splitState
        mergeRotation splitRotation =
      RotationSystem.threeArmEndpointFrameParity
        mergeState.ambientRouteOrderFlipped
        splitState.ambientRouteOrderFlipped
        mergeRotation.orientation splitRotation.orientation

/-- Construct the complete chiral certificate from cubic cyclic endpoint
rotations and two-sided facial geometry. -/
def LocalizedAlignedCommonRunSplice.endpointChiralCertificate
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (mergeState : LocalizedCommonRunMergeArmState splice)
    (splitState : LocalizedCommonRunSplitArmState splice)
    (mergeRotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem mergeState.ambientOutgoingDarts)
    (splitRotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem splitState.ambientOutgoingDarts)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    LocalizedCommonRunEndpointChiralCertificate splice mergeState
      splitState where
  mergeRotation := mergeRotation
  splitRotation := splitRotation
  trunkFaceSide_complement :=
    splice.splitTrunkFaceSide_eq_not_merge hcubic hrotation htwoSided
  routeFace_eq :=
    splice.ambientEndpoint_routeFace_eq mergeState splitState
      mergeRotation splitRotation hcubic hrotation htwoSided
  routeFlip_eq_frameParity :=
    splice.ambientEndpointRouteFlip_eq_frameParity mergeState splitState
      mergeRotation splitRotation hcubic hrotation htwoSided

/-- The fusion-chain normal form with its clean branch refined to a complete
endpoint chiral certificate. -/
inductive LocalizedFusionChainChiralResolution
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  | parallelArmCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : LocalizedAlignedCommonRunSplice profile)
      (cycle : Nonempty (LocalizedCommonRunParallelArmCycle splice))
  | crossedArmCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : LocalizedAlignedCommonRunSplice profile)
      (cycle : Nonempty (LocalizedCommonRunCrossedArmCycle splice))
  | cleanFourArms
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : LocalizedAlignedCommonRunSplice profile)
      (clean : Nonempty (LocalizedCommonRunCleanFourArms splice))
      (mergeState : LocalizedCommonRunMergeArmState splice)
      (splitState : LocalizedCommonRunSplitArmState splice)
      (certificate : LocalizedCommonRunEndpointChiralCertificate
        splice mergeState splitState)
  | alignedBubbleCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (bubble : Nonempty (LocalizedAlignedBubblePrimalCycle profile))
  | strictlyShorterMixedPortCycles
      (descent : Nonempty
        (LocalizedStrictlyShorterMixedPortCycles pair oldCross face))
  | orderInversionPrimalCycle
      (descent : Nonempty
        (LocalizedOrderInversionPrimalCycle pair oldCross face))

/-- Two-sided facial geometry refines every endpoint-rotation resolution to
the complete local chiral normal form. -/
theorem LocalizedFusionChainRotationResolution.nonempty_chiralResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (resolution : LocalizedFusionChainRotationResolution pair oldCross face)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    Nonempty (LocalizedFusionChainChiralResolution pair oldCross face) := by
  cases resolution with
  | parallelArmCycle profile splice cycle =>
      exact ⟨LocalizedFusionChainChiralResolution.parallelArmCycle
        profile splice cycle⟩
  | crossedArmCycle profile splice cycle =>
      exact ⟨LocalizedFusionChainChiralResolution.crossedArmCycle
        profile splice cycle⟩
  | cleanFourArms profile splice clean mergeState splitState
      mergeRotation splitRotation =>
      rcases mergeRotation with ⟨mergeRotation⟩
      rcases splitRotation with ⟨splitRotation⟩
      exact ⟨LocalizedFusionChainChiralResolution.cleanFourArms
        profile splice clean mergeState splitState
          (splice.endpointChiralCertificate mergeState splitState
            mergeRotation splitRotation hcubic hrotation htwoSided)⟩
  | alignedBubbleCycle profile bubble =>
      exact ⟨LocalizedFusionChainChiralResolution.alignedBubbleCycle
        profile bubble⟩
  | strictlyShorterMixedPortCycles descent =>
      exact ⟨
        LocalizedFusionChainChiralResolution.strictlyShorterMixedPortCycles
          descent⟩
  | orderInversionPrimalCycle descent =>
      exact ⟨LocalizedFusionChainChiralResolution.orderInversionPrimalCycle
        descent⟩

/-- A width-at-least-two successor profile reaches the complete local
chiral fusion-chain normal form. -/
theorem LocalizedSuccessorFusionChainProfile.nonempty_chiralResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)}
    {suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3)}
    (successor : LocalizedSuccessorFusionChainProfile oldCross face
      prefixSuccessor suffixSuccessor)
    (hprefix : successor.pair.prefixTrail.IsPath)
    (hsuffix : successor.pair.suffixTrail.IsPath)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    Nonempty (LocalizedFusionChainChiralResolution successor.pair oldCross
      face) := by
  rcases successor.nonempty_rotationResolution hprefix hsuffix hcubic
      hrotation with ⟨resolution⟩
  exact resolution.nonempty_chiralResolution hcubic hrotation htwoSided

/-- The successor-pair trichotomy with its fusion-chain branch refined to
complete endpoint chiral certificates. -/
def LocalizedFusionSuccessorResolution.ChiralOutcome
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    {face : OrbitFace graphData.toRotationSystem}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    (successors : LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion) : Prop :=
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
        Nonempty (LocalizedFusionChainChiralResolution successor.pair cross
          face))

/-- Every resolved successor pair realizes its chiral-certificate-refined
outcome in a cubic cyclic two-sided rotation system. -/
theorem LocalizedFusionSuccessorResolution.finite_chiral_outcome
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    {face : OrbitFace graphData.toRotationSystem}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    (successors : LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    successors.ChiralOutcome := by
  unfold LocalizedFusionSuccessorResolution.ChiralOutcome
  rcases successors.finite_outcome with hdisjoint | hrebase | hprofile
  · exact Or.inl hdisjoint
  · exact Or.inr (Or.inl hrebase)
  · rcases hprofile with ⟨successor⟩
    have hprefix : successor.pair.prefixTrail.IsPath := by
      rw [successor.prefix_eq]
      exact successors.prefix_isPath
    have hsuffix : successor.pair.suffixTrail.IsPath := by
      rw [successor.suffix_eq]
      exact successors.suffix_isPath
    exact Or.inr (Or.inr ⟨successor,
      successor.nonempty_chiralResolution hprefix hsuffix hcubic hrotation
        htwoSided⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
