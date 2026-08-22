import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure

/-!
# Finite coordinates for the outgoing face fragments of one source Cell

The finite facial closure acts on literal darts, whereas the outgoing
profile is indexed by occurrence-sensitive regional face fragments.  Every
such fragment contains a canonical dart over one of the two outgoing cut
edges, hence that dart lies in the twenty-four-slot transition carrier.

This file proves that equality of two actual outgoing fragments is exactly
reachability of their finite coordinates in the graph-free Cell closure.
It is the first outgoing decoder theorem.  It does not identify ambient
orbit faces, compute port incidence, or add the distinct-edge caps of merged
components.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFaceFiniteOutputFragmentEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The actual occurrence-sensitive fragments of the pre-rebase output cut. -/
abbrev SourceLocalLayerSerialFaceOutputFragmentAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :=
  BoundaryRegionalFragment web.annular.RS
    (indexedCrossingEdgeSet
      (sourceLocalLayerRightCrossingAt corridor hunique offset))
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)

/-- The canonical cut-dart occurrence of an outgoing fragment, regarded as
an element of the common source-Cell transition carrier. -/
noncomputable def sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset} :=
  let cut := indexedCrossingEdgeSet
    (sourceLocalLayerRightCrossingAt corridor hunique offset)
  let region := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
    offset
  let occurrence := boundaryRegionalFragmentDartOccurrence web.annular.RS cut
    region fragment
  ⟨occurrence.1, Finset.mem_union_right _
    (mem_closedDartCarrier_of_edge_mem web.annular.RS cut occurrence.1
      occurrence.2)⟩

@[simp]
theorem sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt_val
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
      offset fragment).1 =
      (boundaryRegionalFragmentDartOccurrence web.annular.RS
        (indexedCrossingEdgeSet
          (sourceLocalLayerRightCrossingAt corridor hunique offset))
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        fragment).1 :=
  rfl

/-- Equality of actual outgoing regional fragments is decided by the fixed
finite facial closure.  This remains occurrence-sensitive on a one-sided
opened carrier: no quotient-face or bare-edge identification is used. -/
theorem sourceLocalLayerSerialFaceOutputFragment_eq_iff_finiteClosure
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcellBound :
      (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    left = right ↔
      Relation.ReflTransGen
        (SourceLocalLayerSerialFaceFiniteComponentStep
          (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique
            offset hcellBound)
          (sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
            hcellBound))
        (carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)
          (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
            hunique offset left))
        (carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)
          (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
            hunique offset right)) := by
  let cut := indexedCrossingEdgeSet
    (sourceLocalLayerRightCrossingAt corridor hunique offset)
  let region := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
    offset
  let leftDart := sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
    corridor hunique offset left
  let rightDart := sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
    corridor hunique offset right
  rw [← boundaryRegionalFragmentDartOccurrence_reachable_iff_eq
    web.annular.RS cut region left right]
  simpa [cut, region, leftDart, rightDart] using
    (sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
      corridor hunique offset hcellBound leftDart rightDart)

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment

end Mettapedia.GraphTheory.FourColor
