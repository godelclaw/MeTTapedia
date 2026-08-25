import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalProfileColorCongruence

/-!
# Color splice for an arbitrary literal Cell witness

An arbitrary positive entry of the source Cell `Count` supplies its own
literal open-Cell coloring.  The cumulative prefix may carry a different
coloring.  This file performs the exact algebraic splice: the Cell coloring is
used on the literal Cell region and the prefix coloring elsewhere.

The compatibility premise is stated on the actual intersection of the two
finite regions.  This is deliberately stronger and more explicit than mere
agreement of two displayed color words.  A later geometric theorem must prove
that the source boundary profile supplies this premise; it may not be hidden
inside the splice definition.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellColorSplice

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexSlabConnectivityProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellColorSpliceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The two color functions agree wherever the accumulated predecessor and
the new literal Cell both retain the same ambient edge. -/
def SourceLocalLayerSerialCellColorsCompatibleAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color) : Prop :=
  ∀ edge,
    edge ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset →
    edge ∈ sourceLocalLayerCellRegionAt corridor hunique offset →
      prefixColor edge = cellColor edge

/-- Use the literal Cell witness on the new Cell and the accumulated-prefix
coloring everywhere else. -/
def sourceLocalLayerSerialCellSplicedColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color) : G.edgeSet → Color :=
  fun edge =>
    if edge ∈ sourceLocalLayerCellRegionAt corridor hunique offset then
      cellColor edge
    else
      prefixColor edge

/-- The splice is definitionally the Cell coloring on every Cell edge. -/
theorem sourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color) {edge : G.edgeSet}
    (hedge : edge ∈ sourceLocalLayerCellRegionAt corridor hunique offset) :
    sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
        prefixColor cellColor edge = cellColor edge := by
  simp [sourceLocalLayerSerialCellSplicedColorAt, hedge]

/-- Under the explicit overlap premise, the splice leaves the complete
accumulated-prefix region unchanged. -/
theorem sourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset prefixColor cellColor)
    {edge : G.edgeSet}
    (hedge : edge ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) :
    sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
        prefixColor cellColor edge = prefixColor edge := by
  by_cases hcell : edge ∈ sourceLocalLayerCellRegionAt corridor hunique offset
  · rw [sourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem corridor
      hunique offset prefixColor cellColor hcell]
    exact (hcompatible edge hedge hcell).symm
  · simp [sourceLocalLayerSerialCellSplicedColorAt, hcell]

/-- In particular the outgoing displayed colors come from the positive-Count
Cell witness. -/
theorem sourceLocalLayerSerialCellSplicedColorAt_rightCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color) (step : Fin 2) :
    sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
        prefixColor cellColor
        (sourceLocalLayerRightCrossingAt corridor hunique offset step) =
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) := by
  exact sourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem corridor
    hunique offset prefixColor cellColor
      (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset step)

/-- The graph semantics reconstructed from the prefix state is unchanged by
the splice.  This is the exact tracked half of prefix compatibility. -/
theorem regionalTrackedEdgeGraph_spliced_eq_prefix
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset prefixColor cellColor)
    (first second : Color) :
    regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          prefixColor cellColor) first second =
      regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        prefixColor first second := by
  ext left right
  simp only [regionalTrackedEdgeGraph, RotationSystem.trackedEdgeGraph]
  constructor
  · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
    exact ⟨⟨hadj,
      (sourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem corridor
        hunique offset prefixColor cellColor hcompatible hleft) ▸ hleftTracked,
      (sourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem corridor
        hunique offset prefixColor cellColor hcompatible hright) ▸ hrightTracked⟩,
      hleft, hright⟩
  · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
    exact ⟨⟨hadj,
      (sourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem corridor
        hunique offset prefixColor cellColor hcompatible hleft).symm ▸
          hleftTracked,
      (sourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem corridor
        hunique offset prefixColor cellColor hcompatible hright).symm ▸
          hrightTracked⟩,
      hleft, hright⟩

end

end GoertzelV24ClosedWebLocalLayerSerialCellColorSplice

end Mettapedia.GraphTheory.FourColor
