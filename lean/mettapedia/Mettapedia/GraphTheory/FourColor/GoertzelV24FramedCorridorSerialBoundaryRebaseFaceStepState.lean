import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceResidualProfileFactor

/-!
# Reading the facial rebase step from the predecessor residual state

The finite facial rebase step is organized on the cyclic switch positions of
one ambient face.  The predecessor residual state instead uses the stable
global carrier of literal dart occurrences.  These are two coordinate systems
for the same occurrence-sensitive data.

This file joins them.  Each finite step coordinate is sent to its literal
switch dart, and the stored `oldComponent` bit is proved equivalent to the
already verified predecessor residual-or-boundary-port relation.  Thus the old
matrix is not an additional unconstrained history field.

This is the predecessor-state equation only.  It does not yet compute the
successor residual bits or the continuation, port-incidence, and capped-length
coordinates of the complete five-field profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceStepStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The literal switch-dart occurrence denoted by one coordinate of the
per-face finite rebase step. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt
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
    SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
      hcubic hrotation htwoSided hunique offset hnext :=
  ((sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartEquivAt realization
      hcubic hrotation htwoSided hunique offset hnext root)
    ((carrierCoordinate
      (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root)).symm
      coordinate)).1

/-- On every pair of coordinates of one facial switch code, the accumulated
old-prefix matrix is exactly the predecessor residual state interpreted through
the named boundary-fragment ports. -/
theorem sourceCorridorSerialBoundaryRebaseFaceStepCodeAt_oldComponent_iff_residualFactored
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
    (left right : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).localCode.vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root).oldComponent left right =
        true ↔
      sourceCorridorSerialBoundaryRebaseResidualFaceFactoredStep realization
        hcubic hrotation htwoSided hunique offset hnext
        (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
          hcubic hrotation htwoSided hunique offset hnext root left)
        (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
          hcubic hrotation htwoSided hunique offset hnext root right) := by
  rw [sourceCorridorSerialBoundaryRebaseFaceStepCodeAt_oldComponent_eq_true_iff]
  let RS := embedded.cellulation.rotation.toRotationSystem
  let region :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let leftPosition := (carrierCoordinate carrier).symm left
  let rightPosition := (carrierCoordinate carrier).symm right
  have hpositionDart (first second : Fin (RS.faceOrbit root).card) :
      (faceRegionalAmbientPositionGraph RS root region).Reachable first second ↔
        (faceRegionalDartGraph RS region).Reachable
          (faceCycleDart RS root first) (faceCycleDart RS root second) := by
    exact
      (faceRegionalAmbientPositionGraph_reachable_iff_dartOrbit RS root region
        first second).trans
        (faceRegionalDartGraph_reachable_iff_induce_faceOrbit RS root region
          (faceCycleDartOrbitEquiv RS root first)
          (faceCycleDartOrbitEquiv RS root second)).symm
  have hleftDart :
      (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
        hcubic hrotation htwoSided hunique offset hnext root left).1 =
        faceCycleDart RS root leftPosition.1 := by
    change
      (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartOccurrenceAt
        realization hcubic hrotation htwoSided hunique offset hnext root
          leftPosition).1.1 = _
    rfl
  have hrightDart :
      (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
        hcubic hrotation htwoSided hunique offset hnext root right).1 =
        faceCycleDart RS root rightPosition.1 := by
    change
      (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartOccurrenceAt
        realization hcubic hrotation htwoSided hunique offset hnext root
          rightPosition).1.1 = _
    rfl
  rw [hpositionDart leftPosition.1 rightPosition.1]
  rw [← hleftDart, ← hrightDart]
  exact sourceCorridorSerialBoundaryRebaseFaceReachable_iff_residualFactored
    realization hcubic hrotation htwoSided hunique offset hnext
    (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
      hcubic hrotation htwoSided hunique offset hnext root left)
    (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
      hcubic hrotation htwoSided hunique offset hnext root right)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
