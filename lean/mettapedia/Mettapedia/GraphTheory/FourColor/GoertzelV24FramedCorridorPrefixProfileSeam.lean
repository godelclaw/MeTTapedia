import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixBoundaryProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileSeamResidual

/-!
# The exact seam term for a source corridor Cell

The cumulative region after one source Cell is the old prefix together with
the next central hexagon boundary.  This file specializes the exact
three-factor connectivity and face-progress decompositions to that literal
step.  The residual factor is kept visible; no two-factor coverage claim is
made.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorPrefixProfile
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TerminalProfileFaceUpdate
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileSeamEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- The cumulative edge region before the displayed source Cell. -/
def localLayerLeftPrefixRegion
    (_interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) : Finset G.edgeSet :=
  corridorPrefixEdgeRegion
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    (leftInterior.center.val + 1)

/-- The literal edge boundary of the central hexagon newly exposed by the
source Cell step. -/
def localLayerCellBoundaryRegion
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) : Finset G.edgeSet :=
  orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
    interface.nextCenterLayerFace.1

/-- The cumulative edge region after the displayed source Cell. -/
def localLayerRightPrefixRegion
    (_interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) : Finset G.edgeSet :=
  corridorPrefixEdgeRegion
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    (leftInterior.center.val + 2)

theorem localLayerRightPrefixRegion_eq_left_union_cell
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerRightPrefixRegion =
      interface.localLayerLeftPrefixRegion ∪
        interface.localLayerCellBoundaryRegion := by
  simpa [localLayerRightPrefixRegion, localLayerLeftPrefixRegion,
    localLayerCellBoundaryRegion] using
    interface.localLayerRightPrefixEdgeRegion_eq_left_union_nextCenterBoundary

/-- The tracked adjacency factor crossing between the old cumulative prefix
and the newly exposed source hexagon. -/
def localLayerTrackedSeamGraph
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (C : G.edgeSet → Color) (a b : Color) : SimpleGraph G.edgeSet :=
  regionalTrackedSeamGraph
    embedded.cellulation.rotation.toRotationSystem
    interface.localLayerLeftPrefixRegion
    interface.localLayerCellBoundaryRegion C a b

/-- The source Cell's outgoing tracked graph is exactly old-prefix, local
hexagon, and the explicit residual seam factor. -/
theorem localLayerRightPrefixTrackedGraph_eq_three_factor
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (C : G.edgeSet → Color) (a b : Color) :
    regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        interface.localLayerRightPrefixRegion C a b =
      (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          interface.localLayerLeftPrefixRegion C a b ⊔
        regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          interface.localLayerCellBoundaryRegion C a b) ⊔
        interface.localLayerTrackedSeamGraph C a b := by
  rw [interface.localLayerRightPrefixRegion_eq_left_union_cell]
  exact regionalTrackedEdgeGraph_union_eq_sup_sup_seam
    embedded.cellulation.rotation.toRotationSystem
    interface.localLayerLeftPrefixRegion
    interface.localLayerCellBoundaryRegion C a b

/-- The face-progress factor crossing between the old cumulative prefix and
the newly exposed source hexagon, on one actual face-cycle carrier. -/
def localLayerFaceSeamGraph
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (root : embedded.cellulation.rotation.toRotationSystem.D) :=
  faceRegionalSeamGraph
    embedded.cellulation.rotation.toRotationSystem root
    interface.localLayerLeftPrefixRegion
    interface.localLayerCellBoundaryRegion

/-- The outgoing occurrence-sensitive face graph has the same exact
three-factor decomposition as tracked connectivity. -/
theorem localLayerRightPrefixFaceGraph_eq_three_factor
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        interface.localLayerRightPrefixRegion =
      (faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          interface.localLayerLeftPrefixRegion ⊔
        faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          interface.localLayerCellBoundaryRegion) ⊔
        interface.localLayerFaceSeamGraph root := by
  rw [interface.localLayerRightPrefixRegion_eq_left_union_cell]
  exact faceRegionalAmbientPositionGraph_union_eq_sup_sup_seam _ _ _ _

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
