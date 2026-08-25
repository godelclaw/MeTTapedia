import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseLocality
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellPortalCompleteness
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier

/-!
# Strict historical Cell internal-overlap exclusion

In the two-cap source laboratory, a literal Cell has exactly two vertices and
exactly one internal bond.  If that bond were also internal to a strict
historical Cell, the two Cell vertex sides would coincide.  Their computed
four-edge boundaries would then coincide as well.

At least one outgoing portal of the successor Cell is a genuine boundary
edge.  Equality of the two boundaries would put that same primal edge on a
historical Cell face and on the successor's outgoing corridor face.  Those
faces are separated along the clean corridor, contradicting the facial-dual
geodesic condition.  This excludes the internal/internal part of the
`pastCellOverlap` obligation.  It does not yet classify the cases in which the
shared edge crosses one of the two Cell sides.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellInternalOverlap

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseLocality
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance serialCellInternalOverlapOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A strict historical Cell and the successor Cell cannot share an edge
which is internal to both two-vertex sides. -/
theorem not_common_internalEdge_of_lt_next
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (prior : Fin (blockLength - 3))
    (hprior : prior.val < offset.val)
    {edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (hpriorRegion : edge ∈
      sourceLocalLayerCellRegionAt corridor hunique prior)
    (hpriorNotCrossing : edge ∉ vertexSetCrossingEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        (sourceLocalLayerInteriorAt prior)
        (sourceLocalLayerInteriorAt_hasNext prior)))
    (hnextRegion : edge ∈ sourceLocalLayerCellRegionAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext))
    (hnextNotCrossing : edge ∉ vertexSetCrossingEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        (sourceLocalLayerInteriorAt (sourceLocalLayerNextOffset offset hnext))
        (sourceLocalLayerInteriorAt_hasNext
          (sourceLocalLayerNextOffset offset hnext)))) : False := by
  let target := sourceLocalLayerNextOffset offset hnext
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  have hsideEq :=
    sourceLocalLayerCellVertexSideAt_eq_of_common_internalEdge graphData
      minimal caps coloring web corridor hunique prior target hpriorRegion
        hpriorNotCrossing (by simpa [target] using hnextRegion)
          (by simpa [target] using hnextNotCrossing)
  rcases exists_sourceLocalLayerRightCrossingAt_mem_cellCrossing graphData
      minimal caps coloring web corridor hunique target with
    ⟨newStep, hnewCrossing⟩
  have holdCrossing :
      sourceLocalLayerRightCrossingAt corridor hunique target newStep ∈
        vertexSetCrossingEdges web.annular.RS
          (sourceLocalLayerCellVertexSide corridor hunique
            (sourceLocalLayerInteriorAt prior)
            (sourceLocalLayerInteriorAt_hasNext prior)) := by
    rw [hsideEq]
    exact hnewCrossing
  have hnewFace :
      sourceLocalLayerRightCrossingAt corridor hunique target newStep ∈
        orbitFaceBoundary web.annular.RS
          (skeleton.faceAt
            (nextCorridorInterior (sourceLocalLayerInteriorAt target)
              (sourceLocalLayerInteriorAt_hasNext target)).center).1 := by
    simpa [skeleton] using
      sourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary corridor
        hunique target newStep
  rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique prior
      holdCrossing with ⟨oldStep, hedge⟩ | ⟨oldStep, hedge⟩
  · let oldCenter := (sourceLocalLayerInteriorAt prior).center
    let newCenter :=
      (nextCorridorInterior (sourceLocalLayerInteriorAt target)
        (sourceLocalLayerInteriorAt_hasNext target)).center
    have holdFace :
        sourceLocalLayerRightCrossingAt corridor hunique target newStep ∈
          orbitFaceBoundary web.annular.RS
            (skeleton.faceAt oldCenter).1 := by
      rw [hedge]
      simpa [oldCenter, skeleton] using
        sourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary corridor hunique
          prior oldStep
    have hcentersNe : oldCenter ≠ newCenter := by
      intro hsame
      have hvalues := congrArg Fin.val hsame
      change prior.val + 1 = target.val + 2 at hvalues
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal] at hvalues
      omega
    have hfacesNe : (skeleton.faceAt oldCenter).1 ≠
        (skeleton.faceAt newCenter).1 := by
      intro hsame
      exact hcentersNe (skeleton.faceAt_injective (Subtype.ext hsame))
    have hadj :=
      interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (orbitFace_incidence_le_two web.annular.RS) hfacesNe holdFace
          (by simpa [newCenter, skeleton] using hnewFace)
    have hseparated : oldCenter.val + 1 < newCenter.val := by
      change prior.val + 1 + 1 < target.val + 2
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal]
      omega
    exact (skeleton.separated_not_adjacent oldCenter newCenter hseparated) hadj
  · let oldCenter :=
      (nextCorridorInterior (sourceLocalLayerInteriorAt prior)
        (sourceLocalLayerInteriorAt_hasNext prior)).center
    let newCenter :=
      (nextCorridorInterior (sourceLocalLayerInteriorAt target)
        (sourceLocalLayerInteriorAt_hasNext target)).center
    have holdFace :
        sourceLocalLayerRightCrossingAt corridor hunique target newStep ∈
          orbitFaceBoundary web.annular.RS
            (skeleton.faceAt oldCenter).1 := by
      rw [hedge]
      simpa [oldCenter, skeleton] using
        sourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary corridor
          hunique prior oldStep
    have hcentersNe : oldCenter ≠ newCenter := by
      intro hsame
      have hvalues := congrArg Fin.val hsame
      change prior.val + 2 = target.val + 2 at hvalues
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal] at hvalues
      omega
    have hfacesNe : (skeleton.faceAt oldCenter).1 ≠
        (skeleton.faceAt newCenter).1 := by
      intro hsame
      exact hcentersNe (skeleton.faceAt_injective (Subtype.ext hsame))
    have hadj :=
      interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (orbitFace_incidence_le_two web.annular.RS) hfacesNe holdFace
          (by simpa [newCenter, skeleton] using hnewFace)
    have hseparated : oldCenter.val + 1 < newCenter.val := by
      change prior.val + 2 + 1 < target.val + 2
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal]
      omega
    exact (skeleton.separated_not_adjacent oldCenter newCenter hseparated) hadj

end

end GoertzelV24ClosedWebLocalLayerSerialCellInternalOverlap

end Mettapedia.GraphTheory.FourColor
