import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFiniteClosure

/-!
# Finite outgoing face fragments of a pointwise-selected Cell

The selected finite facial closure acts on literal dart coordinates, while
the outgoing profile is indexed by occurrence-sensitive regional fragments.
Every outgoing fragment has a canonical dart over one of the two selected
outgoing cut edges and therefore lies in the twenty-four-slot carrier.

Equality of actual outgoing fragments is consequently decided exactly by the
graph-free finite closure.  No quotient-face or bare-edge identification is
used.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputFragment

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteClosure
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceFiniteOutputFragmentEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Actual occurrence-sensitive fragments of the selected pre-rebase output
cut. -/
abbrev PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :=
  BoundaryRegionalFragment formation.annular.RS
    (indexedCrossingEdgeSet
      (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset))
    (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset)

/-- The canonical cut-dart occurrence of a selected outgoing fragment,
regarded as an element of the common transition carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt
      formation corridor hinterior offset) :
    {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset} :=
  let cut := indexedCrossingEdgeSet
    (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
      hinterior offset)
  let region :=
    pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset
  let occurrence := boundaryRegionalFragmentDartOccurrence formation.annular.RS
    cut region fragment
  ⟨occurrence.1, Finset.mem_union_right _
    (mem_closedDartCarrier_of_edge_mem formation.annular.RS cut occurrence.1
      occurrence.2)⟩

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt_val
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt
      formation corridor hinterior offset) :
    (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
      formation corridor hinterior offset fragment).1 =
      (boundaryRegionalFragmentDartOccurrence formation.annular.RS
        (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
            hinterior offset))
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
          corridor hinterior offset) fragment).1 :=
  rfl

/-- Equality of actual selected outgoing regional fragments is exactly
reachability of their coordinates in the finite facial closure. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceOutputFragment_eq_iff_finiteClosure
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (left right :
      PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation
        corridor hinterior offset) :
    left = right ↔
      Relation.ReflTransGen
        (PointwiseSelectedSourceLocalLayerSerialFaceFiniteComponentStep
          (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
            formation corridor hinterior offset hcell)
          (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation
            corridor hinterior offset hcell))
        (carrierCoordinate
          (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
            formation corridor hinterior offset)
          (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
            formation corridor hinterior offset left))
        (carrierCoordinate
          (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
            formation corridor hinterior offset)
          (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
            formation corridor hinterior offset right)) := by
  let cut := indexedCrossingEdgeSet
    (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
      hinterior offset)
  let region :=
    pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset
  let leftDart :=
    pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
      formation corridor hinterior offset left
  let rightDart :=
    pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
      formation corridor hinterior offset right
  rw [← boundaryRegionalFragmentDartOccurrence_reachable_iff_eq
    formation.annular.RS cut region left right]
  simpa [cut, region, leftDart, rightDart] using
    (pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
      formation corridor hinterior offset hcell leftDart rightDart)

end

end GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputFragment

end Mettapedia.GraphTheory.FourColor
