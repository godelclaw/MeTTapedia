import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedSeamCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationEndpointInjective

/-!
# Internal edge geometry of the pointwise-selected Cell

In the two-cap minimal-counterexample laboratory, the selected literal Cell
has exactly two vertices.  Consequently its non-crossing regional part is a
single edge, that edge has exactly the two Cell vertices as endpoints, and at
least one selected outgoing portal genuinely crosses the Cell boundary.

These statements use only the corrected pointwise selector and the restricted
interior-face uniqueness receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellInternal

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FacialPentagonCap
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphRotationEndpointInjective
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedLocalCellInternalOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Two non-crossing edges of one selected two-vertex Cell are equal. -/
theorem pointwiseSelectedSourceLocalLayerCellRegionAt_internalEdge_subsingleton
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    {first second :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (hfirstRegion : first ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior offset)
    (hfirstNotCrossing : first ∉ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior offset))
    (hsecondRegion : second ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior offset)
    (hsecondNotCrossing : second ∉ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior offset)) :
    first = second := by
  let side := pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
    corridor hinterior offset
  apply edge_eq_of_mem_region_not_mem_crossing_of_card_eq_two
    web.annular.RS (endpoints_injective web.annular.cellulation.rotation) side
  · simpa [side] using
      pointwiseSelectedSourceLocalLayerCellVertexSideAt_card_eq_two graphData
        minimal caps coloring web corridor hinterior offset
  · simpa [pointwiseSelectedSourceLocalLayerCellRegionAt_eq_vertexSetRegionEdges,
      side] using hfirstRegion
  · simpa [side] using hfirstNotCrossing
  · simpa [pointwiseSelectedSourceLocalLayerCellRegionAt_eq_vertexSetRegionEdges,
      side] using hsecondRegion
  · simpa [side] using hsecondNotCrossing

/-- A non-crossing regional edge has exactly the two selected Cell vertices
as endpoints. -/
theorem pointwiseSelectedSourceLocalLayerCellRegionAt_internalEdge_endpoints_eq_side
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    {edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (hregion : edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior offset)
    (hnotCrossing : edge ∉ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior offset)) :
    web.annular.RS.endpoints edge =
      pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior offset := by
  let side := pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
    corridor hinterior offset
  have hsubset := endpoints_subset_of_mem_region_not_mem_crossing
    web.annular.RS side
      (by simpa [pointwiseSelectedSourceLocalLayerCellRegionAt_eq_vertexSetRegionEdges,
        side] using hregion)
      (by simpa [side] using hnotCrossing)
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [web.annular.RS.endpoints_card_two]
  simpa [side] using
    (pointwiseSelectedSourceLocalLayerCellVertexSideAt_card_eq_two graphData
      minimal caps coloring web corridor hinterior offset).le

/-- A common internal edge rigidly identifies the two selected Cell sides. -/
theorem pointwiseSelectedSourceLocalLayerCellVertexSideAt_eq_of_common_internalEdge
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (first second : Fin (blockLength - 3))
    {edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (hfirstRegion : edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior first)
    (hfirstNotCrossing : edge ∉ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior first))
    (hsecondRegion : edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior second)
    (hsecondNotCrossing : edge ∉ vertexSetCrossingEdges web.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
        corridor hinterior second)) :
    pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation corridor
        hinterior first =
      pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation corridor
        hinterior second := by
  rw [← pointwiseSelectedSourceLocalLayerCellRegionAt_internalEdge_endpoints_eq_side
      graphData minimal caps coloring web corridor hinterior first hfirstRegion
        hfirstNotCrossing,
    ← pointwiseSelectedSourceLocalLayerCellRegionAt_internalEdge_endpoints_eq_side
      graphData minimal caps coloring web corridor hinterior second hsecondRegion
        hsecondNotCrossing]

/-- At least one selected outgoing portal genuinely crosses the Cell side. -/
theorem exists_pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_cellCrossing
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    ∃ step : Fin 2,
      pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation corridor
          hinterior offset step ∈
        vertexSetCrossingEdges web.annular.RS
          (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
            corridor hinterior offset) := by
  let zero : Fin 2 := ⟨0, by omega⟩
  let one : Fin 2 := ⟨1, by omega⟩
  by_contra hnone
  push Not at hnone
  have heq :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_internalEdge_subsingleton
      graphData minimal caps coloring web corridor hinterior offset
      (pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing
        web.toFormation corridor hinterior offset zero)
      (hnone zero)
      (pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing
        web.toFormation corridor hinterior offset one)
      (hnone one)
  have hsteps :=
    pointwiseSelectedSourceLocalLayerRightCrossingAt_injective web.toFormation
      corridor hinterior offset heq
  exact (by decide : zero ≠ one) hsteps

end

end GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellInternal

end Mettapedia.GraphTheory.FourColor
