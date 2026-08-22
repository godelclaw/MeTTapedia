import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseResidualProfileFactor
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseTrackedStepCode

/-!
# Reading the tracked rebase step from the preceding residual state

The finite tracked rebase step stores the accumulated old-prefix component
relation on an at-most-eight-edge switch.  The preceding development already
stores exactly the same old-prefix information on the six literal attachment
roles, factored through the two displayed input ports with an explicit
port-free residual.

This file joins those presentations.  Every old attachment role has a named
coordinate in the eight-edge switch, and the old component matrix at any two
such coordinates is exactly the residual-aware relation computed from the
incoming profile and its finite residual code.

This removes an apparent duplication of state.  It does not yet classify the
two remaining switch coordinates or construct the alternating Cell/rebase
recurrence on a common carrier.  The occurrence-sensitive facial recurrence
also remains separate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseTrackedStepStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The coordinate of one exact old-attachment role in the finite rebase
switch. -/
noncomputable def sourceCorridorSerialBoundaryRebaseOldAttachmentCoordinateAt
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
    (hnext : offset.val + 1 < blockLength - 3)
    (role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    Fin (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext
        (fun _ => 0)).vertexCount.val :=
  carrierCoordinate
    (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
      hrotation htwoSided hunique offset hnext)
    ⟨sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization hcubic
        hrotation htwoSided hunique offset role,
      sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt_mem_finiteSwitch
        realization hcubic hrotation htwoSided hunique offset hnext role⟩

/-- On the six literal old-role coordinates, the old matrix stored by the
finite switch step is exactly the preceding residual-aware state interpreted
through the incoming two-port profile. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_oldRole_iff_residualProfileFactored
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
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0)
    (pair : TrackedColorPair)
    (left right : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).oldComponent pair
          (sourceCorridorSerialBoundaryRebaseOldAttachmentCoordinateAt
            realization hcubic hrotation htwoSided hunique offset hnext left)
          (sourceCorridorSerialBoundaryRebaseOldAttachmentCoordinateAt
            realization hcubic hrotation htwoSided hunique offset hnext right) =
        true ↔
      sourceCorridorSerialBoundaryRebaseResidualProfileFactoredTrackedStep
        realization hcubic hrotation htwoSided hunique offset color hcolor pair
          left right := by
  rw [sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_oldComponent_eq_true_iff]
  have hleft :
      ((carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext)).symm
          (sourceCorridorSerialBoundaryRebaseOldAttachmentCoordinateAt
            realization hcubic hrotation htwoSided hunique offset hnext
              left)).1 =
        sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
          hcubic hrotation htwoSided hunique offset left := by
    change
      ((carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext)).symm
          ((carrierCoordinate
            (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
              hcubic hrotation htwoSided hunique offset hnext))
            ⟨sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
                hcubic hrotation htwoSided hunique offset left,
              sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt_mem_finiteSwitch
                realization hcubic hrotation htwoSided hunique offset hnext
                  left⟩)).1 = _
    rw [Equiv.symm_apply_apply]
  have hright :
      ((carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext)).symm
          (sourceCorridorSerialBoundaryRebaseOldAttachmentCoordinateAt
            realization hcubic hrotation htwoSided hunique offset hnext
              right)).1 =
        sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
          hcubic hrotation htwoSided hunique offset right := by
    change
      ((carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext)).symm
          ((carrierCoordinate
            (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
              hcubic hrotation htwoSided hunique offset hnext))
            ⟨sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
                hcubic hrotation htwoSided hunique offset right,
              sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt_mem_finiteSwitch
                realization hcubic hrotation htwoSided hunique offset hnext
                  right⟩)).1 = _
    rw [Equiv.symm_apply_apply]
  rw [hleft, hright]
  exact sourceCorridorSerialBoundaryRebaseTrackedReachable_iff_residualProfileFactored
    realization hcubic hrotation htwoSided hunique offset color hcolor pair
      left right

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
