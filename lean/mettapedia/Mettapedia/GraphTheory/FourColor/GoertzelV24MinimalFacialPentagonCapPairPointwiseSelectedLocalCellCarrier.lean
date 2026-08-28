import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedLocalCellCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFacialPentagonCapPairNoSmallCut

/-!
# Exact selected Cell carrier in the two-cap source laboratory

On the opening of a graph-backed vertex-minimal Tait counterexample, the
cyclic alternative for a pointwise-selected four-edge Cell wall is impossible.
Both named pentagonal caps lie on the retained side, so cap closure turns such
a cycle into a forbidden one-sided cut of size four in the closed carrier.

The canonical selected Cell at every serial offset therefore has exactly two
vertices and at most six regional edges.  These are the finite-carrier facts
consumed by the rooted Cell transition.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Formation.LocalLayerPair
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24CubicFourEdgeConnectedSides
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24MinimalFacialPentagonCapPairNoSmallCut
open GoertzelV24SelectedDualPathTransversal
open GoertzelV24SelectedDualPathTransversal.SeparatedAlignedSelectedDualTransversals
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A selected literal Cell side in the two-cap minimal-counterexample
laboratory cannot contain a primal cycle. -/
theorem not_pointwiseSelectedLocalLayerCell_hasCycleOnSide
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (layers : GoertzelV24ClosedWebAtGoodWord.Formation.LocalLayerPair
      web.toFormation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      web.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior)) :
    ¬ HasCycleOnSide
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph
      (fun vertex => vertex ∈
        layers.pointwiseSelectedLocalLayerCellVertexSide
          hinterior boundary) := by
  intro hcycle
  let capPair := caps.toFacialPentagonCapPair.toPentagonCapPair
  let side := layers.pointwiseSelectedLocalLayerCellVertexSide
    hinterior boundary
  apply false_of_openGraph_oneSidedCut graphData minimal caps
    (crossingEdgeFinset capPair.openGraph (fun vertex => vertex ∈ side))
    (fun vertex => vertex ∈ side)
  · intro edge
    exact mem_crossingEdgeFinset_iff
      (G := capPair.openGraph) (fun vertex => vertex ∈ side) edge
  · have hcard :=
      layers.pointwiseSelectedLocalLayerCellVertexSide_crossingEdgeFinset_card_eq_four
        hinterior boundary
    simpa [side, capPair] using hcard.le
  · simpa [side, capPair] using hcycle
  · intro step
    change ¬ (capPair.boundaryData.innerStub step ∈ side)
    intro hinside
    let pair := layers.pointwiseSelectedLocalLayerPair hinterior
    have hnotKept : capPair.boundaryData.innerStub step ∉
        pair.componentSide boundary.component := by
      simpa [side, pointwiseSelectedLocalLayerCellVertexSide, pair] using hinside
    apply hnotKept
    have hkept :=
      layers.pointwiseSelectedLocalLayerPair_innerHole_vertex_mem_componentSide
        hinterior boundary
        (innerBoundaryDart capPair.boundaryData web.boundary_wellFormed step)
        (innerBoundaryDart_on_innerHole web.annular
          web.boundary_wellFormed step)
    simpa [pair] using hkept
  · intro step
    change ¬ (capPair.boundaryData.outerStub step ∈ side)
    intro hinside
    let pair := layers.pointwiseSelectedLocalLayerPair hinterior
    have hnotKept : capPair.boundaryData.outerStub step ∉
        pair.componentSide boundary.component := by
      simpa [side, pointwiseSelectedLocalLayerCellVertexSide, pair] using hinside
    apply hnotKept
    have hkept :=
      layers.pointwiseSelectedLocalLayerPair_outerHole_vertex_mem_componentSide
        hinterior boundary
        (outerBoundaryDart capPair.boundaryData web.boundary_wellFormed step)
        (outerBoundaryDart_on_outerHole web.annular
          web.boundary_wellFormed step)
    simpa [pair] using hkept

/-- Sharp two-vertex form of the selected literal Cell carrier. -/
theorem pointwiseSelectedLocalLayerCellVertexSide_card_eq_two
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (layers : GoertzelV24ClosedWebAtGoodWord.Formation.LocalLayerPair
      web.toFormation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      web.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior)) :
    (layers.pointwiseSelectedLocalLayerCellVertexSide
      hinterior boundary).card = 2 := by
  rcases layers.pointwiseSelectedLocalLayerCellVertexSide_card_eq_two_or_hasCycleOnSide
      hinterior boundary with hcycle | hcard
  · exact (not_pointwiseSelectedLocalLayerCell_hasCycleOnSide
      graphData minimal caps coloring web corridor hinterior layers boundary
      hcycle).elim
  · exact hcard

/-- Canonical indexed selected Cell sides have exactly two vertices. -/
theorem pointwiseSelectedSourceLocalLayerCellVertexSideAt_card_eq_two
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
    (pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation
      corridor hinterior offset).card = 2 := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt web.toFormation
    corridor hinterior offset
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt web.toFormation
    corridor hinterior offset
  simpa [pointwiseSelectedSourceLocalLayerCellVertexSideAt, layers, boundary] using
    pointwiseSelectedLocalLayerCellVertexSide_card_eq_two
      graphData minimal caps coloring web corridor hinterior layers boundary

/-- The exact selected Count region at every serial offset has at most six
edges, the bound required by the finite rooted Cell-letter carrier. -/
theorem pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six
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
    (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6 := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt web.toFormation
    corridor hinterior offset
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt web.toFormation
    corridor hinterior offset
  rcases layers.pointwiseSelectedLocalLayerCellRegion_card_le_six_or_hasCycleOnSide
      hinterior boundary with hcycle | hcard
  · exact (not_pointwiseSelectedLocalLayerCell_hasCycleOnSide
      graphData minimal caps coloring web corridor hinterior layers boundary
      hcycle).elim
  · rw [pointwiseSelectedSourceLocalLayerCellRegionAt_eq_vertexSetRegionEdges]
    simpa [pointwiseSelectedSourceLocalLayerCellVertexSideAt, layers, boundary]
      using hcard

end

end GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier

end Mettapedia.GraphTheory.FourColor
