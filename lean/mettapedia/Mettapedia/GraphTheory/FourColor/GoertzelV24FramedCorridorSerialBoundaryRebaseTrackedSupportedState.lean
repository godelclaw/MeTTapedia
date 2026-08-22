import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseTrackedStepState
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphSupportedPortResidualFactorContraction

/-!
# Support-sensitive predecessor tracked state for a serial rebase

The tracked predecessor residual code has the same support boundary as its
facial analogue.  Component reachability is reflexive at every coordinate,
including an isolated edge, while an attachment to a persistent port is
valid only when both endpoints occur in the tracked graph support.

This file conservatively refines the three tracked-colour residual codes with
exact interface and port activity.  Forgetting those bits recovers the
existing residual code definitionally.  The result supplies the tracked
support input needed by a later finite union update; it does not claim that
the complete alternating Cell/rebase recurrence is closed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseTrackedSupportedStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Exact support-sensitive tracked residual state for all three tracked
colour pairs. -/
abbrev SourceCorridorSerialBoundaryRebaseSupportedTrackedCode
    {blockLength : Nat} (offset : Fin (blockLength - 3)) :=
  TrackedColorPair →
    BoundedSupportedPortResidualCode
      (SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) (Fin 2)

/-- Extract the supported tracked state of the accumulated prefix. -/
noncomputable def sourceCorridorSerialBoundaryRebaseSupportedTrackedCodeAt
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
    (color : G.edgeSet → Color) :
    SourceCorridorSerialBoundaryRebaseSupportedTrackedCode offset :=
  fun pair =>
    exactSupportedPortResidualCode
      (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2)
      (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
        hcubic hrotation htwoSided hunique offset)
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing)

/-- Forgetting activity recovers the existing tracked residual code for each
tracked colour pair. -/
theorem sourceCorridorSerialBoundaryRebaseSupportedTrackedCodeAt_toResidual
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
    (pair : TrackedColorPair) :
    (sourceCorridorSerialBoundaryRebaseSupportedTrackedCodeAt realization
      hcubic hrotation htwoSided hunique offset color pair
      ).toBoundedPortResidualCode =
      sourceCorridorSerialBoundaryRebaseResidualTrackedCodeAt realization
        hcubic hrotation htwoSided hunique offset color pair :=
  rfl

/-- A stored old-role activity bit is exactly support membership of its
literal edge in the corresponding old regional tracked graph. -/
theorem sourceCorridorSerialBoundaryRebaseSupportedTrackedCodeAt_interfaceActive_iff
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
    (pair : TrackedColorPair)
    (role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    (sourceCorridorSerialBoundaryRebaseSupportedTrackedCodeAt realization
      hcubic hrotation htwoSided hunique offset color pair
      ).interfaceActive role = true ↔
      sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization hcubic
          hrotation htwoSided hunique offset role ∈
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).support := by
  exact
    exactSupportedPortResidualCode_interfaceActive_eq_true_iff
      (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2)
      (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
        hcubic hrotation htwoSided hunique offset)
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing)
      role

/-- A stored persistent-port activity bit is exactly support membership of
the corresponding outgoing crossing in the old tracked graph. -/
theorem sourceCorridorSerialBoundaryRebaseSupportedTrackedCodeAt_portActive_iff
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
    (pair : TrackedColorPair) (port : Fin 2) :
    (sourceCorridorSerialBoundaryRebaseSupportedTrackedCodeAt realization
      hcubic hrotation htwoSided hunique offset color pair).portActive port =
        true ↔
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
          offset).nextLocalLayerPrefixCrossing port ∈
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).support := by
  exact
    exactSupportedPortResidualCode_portActive_eq_true_iff
      (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2)
      (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
        hcubic hrotation htwoSided hunique offset)
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing)
      port

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
