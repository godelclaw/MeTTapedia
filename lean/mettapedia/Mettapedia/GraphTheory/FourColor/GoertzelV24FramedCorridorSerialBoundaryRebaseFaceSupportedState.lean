import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceStepState
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphSupportedPortResidualFactorContraction

/-!
# Support-sensitive predecessor face state for a serial rebase

The predecessor facial residual code determines reachability on the stable
switch-dart carrier, but reachability is reflexive even at an isolated dart.
A subsequent union update must also know whether an interface dart or a
boundary-fragment representative belongs to the old regional graph support:
the exact attachment relation is support-sensitive.

This file adds those finite activity bits to the already verified predecessor
state.  Its underlying residual code is definitionally the existing code, and
the new bits are proved to be exactly literal support membership.  Hence this
is a conservative state refinement, not a new geometric hypothesis or a
completed successor decoder.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceSupportedStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The predecessor facial residual state with exact support activity on the
stable switch-dart carrier and its canonical boundary-fragment ports. -/
abbrev SourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt
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
    (hnext : offset.val + 1 < blockLength - 3) :=
  BoundedSupportedPortResidualCode
    (SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
      hcubic hrotation htwoSided hunique offset hnext)
    (SourceCorridorSerialBoundaryRebaseFacePortAt realization hcubic hrotation
      htwoSided hunique offset)

/-- Extract the exact support-sensitive predecessor facial state. -/
noncomputable def sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt
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
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext :=
  exactSupportedPortResidualCode
    (faceRegionalDartGraph embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges)
    Subtype.val
    (sourceCorridorSerialBoundaryRebaseFacePortDartAt realization hcubic
      hrotation htwoSided hunique offset)

/-- Forgetting support activity recovers the previously verified predecessor
residual state definitionally. -/
theorem sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt_toResidual
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
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).toBoundedPortResidualCode =
      sourceCorridorSerialBoundaryRebaseResidualFaceCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext :=
  rfl

/-- The stored switch activity bit is exactly support membership in the old
regional face-dart graph. -/
theorem sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt_interfaceActive_iff
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
    (occurrence :
      SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
        hcubic hrotation htwoSided hunique offset hnext) :
    (sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).interfaceActive occurrence =
        true ↔
      occurrence.1 ∈
        (faceRegionalDartGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges).support := by
  exact
    exactSupportedPortResidualCode_interfaceActive_eq_true_iff
      (faceRegionalDartGraph embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges)
      Subtype.val
      (sourceCorridorSerialBoundaryRebaseFacePortDartAt realization hcubic
        hrotation htwoSided hunique offset)
      occurrence

/-- The stored predecessor-port activity bit is exactly support membership of
that fragment's canonical dart representative. -/
theorem sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt_portActive_iff
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
    (port : SourceCorridorSerialBoundaryRebaseFacePortAt realization hcubic
      hrotation htwoSided hunique offset) :
    (sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).portActive port = true ↔
      sourceCorridorSerialBoundaryRebaseFacePortDartAt realization hcubic
          hrotation htwoSided hunique offset port ∈
        (faceRegionalDartGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges).support := by
  exact
    exactSupportedPortResidualCode_portActive_eq_true_iff
      (faceRegionalDartGraph embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges)
      Subtype.val
      (sourceCorridorSerialBoundaryRebaseFacePortDartAt realization hcubic
        hrotation htwoSided hunique offset)
      port

/-- Every coordinate of a per-face finite rebase step reads its old support
activity from the same stable supported residual state. -/
theorem sourceCorridorSerialBoundaryRebaseFaceStepCoordinate_oldActive_iff
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).localCode.vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).interfaceActive
        (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate) =
        true ↔
      (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
        hcubic hrotation htwoSided hunique offset hnext root coordinate).1 ∈
        (faceRegionalDartGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges).support := by
  exact
    sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt_interfaceActive_iff
      realization hcubic hrotation htwoSided hunique offset hnext
      (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
        hcubic hrotation htwoSided hunique offset hnext root coordinate)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
