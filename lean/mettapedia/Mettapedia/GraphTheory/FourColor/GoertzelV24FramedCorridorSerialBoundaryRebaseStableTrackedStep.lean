import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedState

/-!
# Reading the old tracked block on stable serial-rebase coordinates

The predecessor residual state of a serial boundary rebase now lives on six
fixed slots.  This file gives that state its graph-free interpretation against
an incoming corridor profile and proves that, on every actual source slot, it
recovers literal old-prefix reachability exactly.

This closes the old/old block of the stable recurrence.  It deliberately does
not classify the two newly displayed successor crossings: interactions of
those crossings with the accumulated prefix remain the next source-local
attachment obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

namespace SourceTrail

namespace AnnularEmbedding

/-- Interpret any supported tracked residual state through the two-port
connectivity stored in an incoming bounded corridor profile. -/
def boundedSupportedProfileFactoredTrackedStep
    {Interface : Type*}
    {faceFragmentBound : Nat}
    (state : TrackedColorPair →
      BoundedSupportedPortResidualCode Interface (Fin 2))
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (pair : TrackedColorPair)
    (left right : Interface) : Prop :=
  SupportedPortResidualFactoredReachability (state pair)
    (fun leftPort rightPort =>
      profile.profile.strandConnected pair (.inl leftPort) (.inl rightPort) =
        true)
    left right

/-- The specialization to the uniform six predecessor slots. -/
abbrev boundedSerialBoundaryRebaseStableProfileFactoredTrackedStep :=
  @boundedSupportedProfileFactoredTrackedStep
    BoundedSerialBoundaryRebaseOldAttachmentSlot

/-- Padding along a partial decoder preserves the residual-or-port relation
whenever both stable coordinates decode. -/
theorem boundedSerialBoundaryRebaseStableProfileFactoredTrackedStep_pad_iff
    {Interface Stable : Type*} {faceFragmentBound : Nat}
    (decode : Stable → Option Interface)
    (code : TrackedColorPair →
      BoundedSupportedPortResidualCode Interface (Fin 2))
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (pair : TrackedColorPair)
    (left right : Stable)
    (leftInterface rightInterface : Interface)
    (hleft : decode left = some leftInterface)
    (hright : decode right = some rightInterface) :
    boundedSupportedProfileFactoredTrackedStep
        (fun tracked => padSupportedPortResidualCode decode (code tracked))
        profile pair left right ↔
      boundedSupportedProfileFactoredTrackedStep code profile pair
        leftInterface rightInterface := by
  simp [boundedSupportedProfileFactoredTrackedStep,
    SupportedPortResidualFactoredReachability,
    PortResidualFactoredReachability, padSupportedPortResidualCode,
    hleft, hright]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableTrackedStepEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- On encoded actual source roles, the stable predecessor state plus the
incoming complete profile is exactly literal old-prefix reachability. -/
theorem sourceCorridorSerialBoundaryRebaseStableProfileFactoredTrackedStep_slot_iff
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0)
    (pair : TrackedColorPair)
    (left right : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    boundedSupportedProfileFactoredTrackedStep
        (sourceCorridorSerialBoundaryRebaseStableSupportedTrackedCodeAt
          realization hcubic hrotation htwoSided hunique offset color)
        (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
          hrotation htwoSided hunique offset color hcolor)
        pair
        (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot left)
        (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot right) ↔
      (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
            hcubic hrotation htwoSided hunique offset left)
          (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
            hcubic hrotation htwoSided hunique offset right) := by
  change
    boundedSupportedProfileFactoredTrackedStep
        (fun tracked => padSupportedPortResidualCode
          (sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot? offset)
          (sourceCorridorSerialBoundaryRebaseSupportedTrackedCodeAt realization
            hcubic hrotation htwoSided hunique offset color tracked))
        (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
          hrotation htwoSided hunique offset color hcolor)
        pair
        (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot left)
        (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot right) ↔ _
  rw [boundedSerialBoundaryRebaseStableProfileFactoredTrackedStep_pad_iff
    (sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot? offset)
    (sourceCorridorSerialBoundaryRebaseSupportedTrackedCodeAt realization
      hcubic hrotation htwoSided hunique offset color)
    (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
      htwoSided hunique offset color hcolor)
    pair
    (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot left)
    (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot right)
    left right
    (sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot?_slot offset
      left)
    (sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot?_slot offset
      right)]
  exact
    (sourceCorridorSerialBoundaryRebaseTrackedReachable_iff_residualProfileFactored
      realization hcubic hrotation htwoSided hunique offset color hcolor pair
        left right).symm

end

end AnnularEmbedding

end SourceTrail


end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
