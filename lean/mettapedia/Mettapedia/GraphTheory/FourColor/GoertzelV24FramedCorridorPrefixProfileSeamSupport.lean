import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceBoundaryAdjacency
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileSeamCorners

/-!
# Support localization for a source corridor-prefix seam

An edge of the cumulative old prefix that is adjacent to an edge of the new
Cell cannot come from an earlier corridor face.  Otherwise the generic cubic
corner theorem would make that earlier face dual-adjacent to the new Cell,
contradicting inducedness of the corridor.  Thus every residual seam turn is
localized at the immediately preceding source hexagon.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CubicFaceBoundaryAdjacency
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorPrefixProfile
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileSeamSupportEdgeSetDecidableEq :
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

/-- Any old-prefix edge adjacent to an edge of the newly exposed Cell already
lies on the immediately preceding corridor face.  Earlier prefix faces are
excluded by the corridor's inducedness in the full facial dual. -/
theorem leftPrefixEdge_mem_previousFaceBoundary_of_adj_cellBoundary
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    {leftEdge rightEdge : G.edgeSet}
    (hleft : leftEdge ∈ interface.localLayerLeftPrefixRegion)
    (hright : rightEdge ∈ interface.localLayerCellBoundaryRegion)
    (hadj : embedded.cellulation.rotation.toRotationSystem.edgeAdjacencyGraph.Adj
      leftEdge rightEdge) :
    leftEdge ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem
      (realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center).1 := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let corridor := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton
  have hleftPrefix : leftEdge ∈ corridorPrefixEdgeRegion corridor
      (leftInterior.center.val + 1) := by
    simpa [localLayerLeftPrefixRegion, corridor] using hleft
  have hrightCell : rightEdge ∈ orbitFaceBoundary RS
      (corridor.faceAt (nextCorridorInterior leftInterior hnext).center).1 := by
    simpa [localLayerCellBoundaryRegion, nextCenterLayerFace, RS, corridor]
      using hright
  rw [mem_corridorPrefixEdgeRegion_iff] at hleftPrefix
  rcases hleftPrefix with ⟨position, hposition, hleftPosition⟩
  by_cases hcenter : position = leftInterior.center
  · subst position
    exact hleftPosition
  · have hbefore : position.val < leftInterior.center.val := by omega
    have hseparated : position.val + 1 <
        (nextCorridorInterior leftInterior hnext).center.val := by
      change position.val + 1 < leftInterior.center.val + 1
      omega
    have hfacesNe : (corridor.faceAt position).1 ≠
        (corridor.faceAt
          (nextCorridorInterior leftInterior hnext).center).1 := by
      intro hfaces
      have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
      have hvalues := congrArg Fin.val hindices
      change position.val = leftInterior.center.val + 1 at hvalues
      omega
    have hdual := interiorDualGraph_adj_of_edgeAdjacencyGraph_adj
      RS hcubic hrotation htwoSided hfacesNe hleftPosition hrightCell hadj
    exact (corridor.separated_not_adjacent position
      (nextCorridorInterior leftInterior hnext).center hseparated hdual).elim

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
