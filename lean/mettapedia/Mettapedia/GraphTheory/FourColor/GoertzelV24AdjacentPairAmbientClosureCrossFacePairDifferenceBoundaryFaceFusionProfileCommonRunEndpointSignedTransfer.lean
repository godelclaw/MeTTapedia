import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunEndpointChiralResolution
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionSignedTransferMonoid

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
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

/-- A Boolean translation by the difference of two labels carries the
first label exactly to the second. -/
theorem boolRoutePermutation_xor_apply_left (first second : Bool) :
    boolRoutePermutation (Bool.xor first second) first = second := by
  cases first <;> cases second <;> rfl

/-- Coordinatewise Boolean differences give the unique four-state
translation carrying one signed route state to another. -/
theorem signedRoutePermutation_coordinateDifference_apply
    (firstEndpoint secondEndpoint firstRoute secondRoute : Bool) :
    signedRoutePermutation
        (Bool.xor firstEndpoint secondEndpoint)
        (Bool.xor firstRoute secondRoute)
        (firstEndpoint, firstRoute) =
      (secondEndpoint, secondRoute) := by
  simp only [signedRoutePermutation_apply,
    boolRoutePermutation_xor_apply_left]

/-- The change of the selected incident-face side between the two
oriented trunk endpoints. -/
def LocalizedAlignedCommonRunSplice.ambientEndpointSideFlip
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) : Bool :=
  Bool.xor splice.mergeTrunkFaceSide splice.splitTrunkFaceSide

/-- The signed route state at the common trunk's merge endpoint. -/
def LocalizedAlignedCommonRunSplice.ambientMergeEndpointState
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (mergeState : LocalizedCommonRunMergeArmState splice)
    (mergeRotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem mergeState.ambientOutgoingDarts) :
    Bool × Bool :=
  (splice.mergeTrunkFaceSide,
    mergeState.ambientTrunkFaceRoute mergeRotation)

/-- The signed route state at the common trunk's split endpoint. -/
def LocalizedAlignedCommonRunSplice.ambientSplitEndpointState
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (splitState : LocalizedCommonRunSplitArmState splice)
    (splitRotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem splitState.ambientOutgoingDarts) :
    Bool × Bool :=
  (splice.splitTrunkFaceSide,
    splitState.ambientTrunkFaceRoute splitRotation)

/-- Canonical four-state transfer across an oriented common trunk. Its
two bits are the exact side and route coordinate differences. -/
def LocalizedAlignedCommonRunSplice.ambientEndpointSignedTransfer
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
      graphData.toRotationSystem splitState.ambientOutgoingDarts) :
    Equiv.Perm (Bool × Bool) :=
  signedRoutePermutation splice.ambientEndpointSideFlip
    (splice.ambientEndpointRouteFlip mergeState splitState
      mergeRotation splitRotation)

/-- The canonical transfer carries the actual merge endpoint state to the
actual split endpoint state. -/
theorem LocalizedAlignedCommonRunSplice.ambientEndpointSignedTransfer_apply_mergeState
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
      graphData.toRotationSystem splitState.ambientOutgoingDarts) :
    splice.ambientEndpointSignedTransfer mergeState splitState
        mergeRotation splitRotation
        (splice.ambientMergeEndpointState mergeState mergeRotation) =
      splice.ambientSplitEndpointState splitState splitRotation := by
  exact signedRoutePermutation_coordinateDifference_apply
    splice.mergeTrunkFaceSide splice.splitTrunkFaceSide
    (mergeState.ambientTrunkFaceRoute mergeRotation)
    (splitState.ambientTrunkFaceRoute splitRotation)

/-- Read the canonical transfer directly from a chiral certificate. -/
def LocalizedCommonRunEndpointChiralCertificate.signedTransfer
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    {mergeState : LocalizedCommonRunMergeArmState splice}
    {splitState : LocalizedCommonRunSplitArmState splice}
    (certificate : LocalizedCommonRunEndpointChiralCertificate splice
      mergeState splitState) : Equiv.Perm (Bool × Bool) :=
  splice.ambientEndpointSignedTransfer mergeState splitState
    certificate.mergeRotation certificate.splitRotation

/-- Facial transport forces the endpoint-side translation bit to be odd. -/
theorem LocalizedCommonRunEndpointChiralCertificate.endpointSideFlip_eq_true
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    {mergeState : LocalizedCommonRunMergeArmState splice}
    {splitState : LocalizedCommonRunSplitArmState splice}
    (certificate : LocalizedCommonRunEndpointChiralCertificate splice
      mergeState splitState) :
    splice.ambientEndpointSideFlip = true := by
  unfold LocalizedAlignedCommonRunSplice.ambientEndpointSideFlip
  rw [certificate.trunkFaceSide_complement]
  cases splice.mergeTrunkFaceSide <;> rfl

/-- The certificate reduces the whole four-state transfer to one finite
frame-parity bit: endpoint transport always flips, while route transport
is precisely the endpoint-frame parity. -/
theorem LocalizedCommonRunEndpointChiralCertificate.signedTransfer_eq_frameParity
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    {mergeState : LocalizedCommonRunMergeArmState splice}
    {splitState : LocalizedCommonRunSplitArmState splice}
    (certificate : LocalizedCommonRunEndpointChiralCertificate splice
      mergeState splitState) :
    certificate.signedTransfer =
      signedRoutePermutation true
        (RotationSystem.threeArmEndpointFrameParity
          mergeState.ambientRouteOrderFlipped
          splitState.ambientRouteOrderFlipped
          certificate.mergeRotation.orientation
          certificate.splitRotation.orientation) := by
  unfold LocalizedCommonRunEndpointChiralCertificate.signedTransfer
    LocalizedAlignedCommonRunSplice.ambientEndpointSignedTransfer
  rw [certificate.endpointSideFlip_eq_true,
    certificate.routeFlip_eq_frameParity]

/-- The certificate transfer maps its concrete endpoint states. -/
theorem LocalizedCommonRunEndpointChiralCertificate.signedTransfer_apply_mergeState
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    {mergeState : LocalizedCommonRunMergeArmState splice}
    {splitState : LocalizedCommonRunSplitArmState splice}
    (certificate : LocalizedCommonRunEndpointChiralCertificate splice
      mergeState splitState) :
    certificate.signedTransfer
        (splice.ambientMergeEndpointState mergeState
          certificate.mergeRotation) =
      splice.ambientSplitEndpointState splitState
        certificate.splitRotation := by
  exact splice.ambientEndpointSignedTransfer_apply_mergeState mergeState
    splitState certificate.mergeRotation certificate.splitRotation

/-- Every state has its endpoint coordinate complemented by the clean
common-run transfer. -/
theorem LocalizedCommonRunEndpointChiralCertificate.signedTransfer_apply_fst
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    {mergeState : LocalizedCommonRunMergeArmState splice}
    {splitState : LocalizedCommonRunSplitArmState splice}
    (certificate : LocalizedCommonRunEndpointChiralCertificate splice
      mergeState splitState)
    (state : Bool × Bool) :
    (certificate.signedTransfer state).1 = !state.1 := by
  rw [certificate.signedTransfer_eq_frameParity]
  rcases state with ⟨endpoint, route⟩
  cases endpoint <;> rfl

/-- The clean common-run signed transfer is never the identity, regardless
of its route-frame parity. -/
theorem LocalizedCommonRunEndpointChiralCertificate.signedTransfer_ne_refl
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    {mergeState : LocalizedCommonRunMergeArmState splice}
    {splitState : LocalizedCommonRunSplitArmState splice}
    (certificate : LocalizedCommonRunEndpointChiralCertificate splice
      mergeState splitState) :
    certificate.signedTransfer ≠ Equiv.refl (Bool × Bool) := by
  intro hidentity
  have hvalue := congrArg
    (fun transfer : Equiv.Perm (Bool × Bool) =>
      (transfer (false, false)).1) hidentity
  rw [certificate.signedTransfer_apply_fst] at hvalue
  simp at hvalue

/-- There are exactly two possible clean common-run transfers: the
endpoint-only flip and the diagonal endpoint-and-route flip. -/
theorem LocalizedCommonRunEndpointChiralCertificate.signedTransfer_classification
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    {mergeState : LocalizedCommonRunMergeArmState splice}
    {splitState : LocalizedCommonRunSplitArmState splice}
    (certificate : LocalizedCommonRunEndpointChiralCertificate splice
      mergeState splitState) :
    certificate.signedTransfer = signedRoutePermutation true false ∨
      certificate.signedTransfer = signedRoutePermutation true true := by
  rw [certificate.signedTransfer_eq_frameParity]
  cases RotationSystem.threeArmEndpointFrameParity
      mergeState.ambientRouteOrderFlipped
      splitState.ambientRouteOrderFlipped
      certificate.mergeRotation.orientation
      certificate.splitRotation.orientation <;> simp

/-- Every clean common-run transfer is an involution. -/
theorem LocalizedCommonRunEndpointChiralCertificate.signedTransfer_sq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    {mergeState : LocalizedCommonRunMergeArmState splice}
    {splitState : LocalizedCommonRunSplitArmState splice}
    (certificate : LocalizedCommonRunEndpointChiralCertificate splice
      mergeState splitState) :
    certificate.signedTransfer * certificate.signedTransfer =
      Equiv.refl (Bool × Bool) := by
  rcases certificate.signedTransfer_classification with htransfer | htransfer
  · rw [htransfer]
    rw [← signedRoutePermutation_xor true true false false]
    rfl
  · rw [htransfer]
    rw [← signedRoutePermutation_xor true true true true]
    rfl

/-- The fusion-chain normal form with its clean branch carrying the
canonical endpoint transfer and a proof that this transfer is nonidentity. -/
inductive LocalizedFusionChainSignedTransferResolution
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
      (transfer_ne_refl : certificate.signedTransfer ≠
        Equiv.refl (Bool × Bool))
  | alignedBubbleCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (bubble : Nonempty (LocalizedAlignedBubblePrimalCycle profile))
  | strictlyShorterMixedPortCycles
      (descent : Nonempty
        (LocalizedStrictlyShorterMixedPortCycles pair oldCross face))
  | orderInversionPrimalCycle
      (descent : Nonempty
        (LocalizedOrderInversionPrimalCycle pair oldCross face))

/-- Every chiral fusion-chain resolution exposes a nonidentity transfer in
its clean branch. -/
theorem LocalizedFusionChainChiralResolution.nonempty_signedTransferResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (resolution : LocalizedFusionChainChiralResolution pair oldCross face) :
    Nonempty (LocalizedFusionChainSignedTransferResolution pair oldCross
      face) := by
  cases resolution with
  | parallelArmCycle profile splice cycle =>
      exact ⟨LocalizedFusionChainSignedTransferResolution.parallelArmCycle
        profile splice cycle⟩
  | crossedArmCycle profile splice cycle =>
      exact ⟨LocalizedFusionChainSignedTransferResolution.crossedArmCycle
        profile splice cycle⟩
  | cleanFourArms profile splice clean mergeState splitState certificate =>
      exact ⟨LocalizedFusionChainSignedTransferResolution.cleanFourArms
        profile splice clean mergeState splitState certificate
          certificate.signedTransfer_ne_refl⟩
  | alignedBubbleCycle profile bubble =>
      exact ⟨LocalizedFusionChainSignedTransferResolution.alignedBubbleCycle
        profile bubble⟩
  | strictlyShorterMixedPortCycles descent =>
      exact ⟨
        LocalizedFusionChainSignedTransferResolution.strictlyShorterMixedPortCycles
          descent⟩
  | orderInversionPrimalCycle descent =>
      exact ⟨
        LocalizedFusionChainSignedTransferResolution.orderInversionPrimalCycle
          descent⟩

/-- A width-at-least-two successor profile reaches the signed-transfer
fusion-chain normal form. -/
theorem LocalizedSuccessorFusionChainProfile.nonempty_signedTransferResolution
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
    (hrotation :
      GoertzelV24FaceDualConnectedness.VertexRotationCyclic
        graphData.toRotationSystem)
    (htwoSided :
      GoertzelV24OrbitFaceTwoSided.OrbitFacesTwoSided
        graphData.toRotationSystem) :
    Nonempty (LocalizedFusionChainSignedTransferResolution successor.pair
      oldCross face) := by
  rcases successor.nonempty_chiralResolution hprefix hsuffix hcubic
      hrotation htwoSided with ⟨resolution⟩
  exact resolution.nonempty_signedTransferResolution

/-- The successor trichotomy with a nonidentity canonical transfer exposed
in every clean fusion-chain branch. -/
def LocalizedFusionSuccessorResolution.SignedTransferOutcome
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
        Nonempty (LocalizedFusionChainSignedTransferResolution
          successor.pair cross face))

/-- Every resolved successor pair realizes the signed-transfer-refined
outcome in a cubic cyclic two-sided rotation system. -/
theorem LocalizedFusionSuccessorResolution.finite_signedTransfer_outcome
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
    (hrotation :
      GoertzelV24FaceDualConnectedness.VertexRotationCyclic
        graphData.toRotationSystem)
    (htwoSided :
      GoertzelV24OrbitFaceTwoSided.OrbitFacesTwoSided
        graphData.toRotationSystem) :
    successors.SignedTransferOutcome := by
  unfold LocalizedFusionSuccessorResolution.SignedTransferOutcome
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
      successor.nonempty_signedTransferResolution hprefix hsuffix hcubic
        hrotation htwoSided⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
