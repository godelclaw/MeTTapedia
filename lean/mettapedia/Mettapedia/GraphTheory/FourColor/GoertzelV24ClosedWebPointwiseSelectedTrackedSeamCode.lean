import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedTransitionCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalSlitRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileConnectivityUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileVertexSideSeam

/-!
# Finite tracked seam code for a pointwise-selected Cell

Adjoining one literal selected Cell to a terminal-aware cumulative prefix
creates two local tracked factors: the tracked graph inside the Cell and the
residual seam between the old region and that Cell.  Both factors live on the
same twenty-one-edge carrier constructed from the selected four-edge boundary.

The key localization theorem below proves that every non-isolated seam edge
lies in the closed adjacency neighbourhood of the two selected outgoing
crossings.  Thus the finite code preserves complete reachability for both
factors without using the historical global shared-edge selector.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SelectedDualPathTransversal
open GoertzelV24SelectedDualPathTransversal.SeparatedAlignedSelectedDualTransversals
open GoertzelV24SimpleGraphSupResidual
open GoertzelV24TerminalProfileConnectivityUpdate
open GoertzelV24TerminalProfileSeamResidual
open GoertzelV24TerminalProfileVertexSideSeam
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedTrackedSeamCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

/-- Residual tracked adjacency between the selected terminal-aware prefix and
one literal selected Cell. -/
def pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) :
    SimpleGraph G.edgeSet :=
  regionalTrackedSeamGraph formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset)
    (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset)
    color first second

/-- Adjoining one selected Cell is exactly predecessor graph, Cell graph, and
their residual seam. -/
theorem pointwiseSelectedSourceLocalLayerSerialPreRebaseTrackedGraph_eq_three_factor
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) :
    regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
          formation corridor hinterior offset) color first second =
      (regionalTrackedEdgeGraph formation.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            formation corridor hinterior offset) color first second ⊔
        regionalTrackedEdgeGraph formation.annular.RS
          (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
            hinterior offset) color first second) ⊔
        pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt formation
          corridor hinterior offset color first second := by
  rw [← pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell
    formation corridor hinterior offset]
  exact regionalTrackedEdgeGraph_union_eq_sup_sup_seam
    formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset)
    (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset) color first second

/-- Every edge crossing the selected Cell side is one of the two incoming or
two outgoing selected crossings. -/
theorem pointwiseSelectedSourceLocalLayerCellCrossingAt_eq_left_or_right
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) {edge : G.edgeSet}
    (hedge : edge ∈ vertexSetCrossingEdges formation.annular.RS
      (pointwiseSelectedSourceLocalLayerCellVertexSideAt formation corridor
        hinterior offset)) :
    (∃ step : Fin 2,
      edge = pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset step) ∨
    (∃ step : Fin 2,
      edge = pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset step) := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
    hinterior offset
  have hcut : edge ∈ pair.primalCutEdges
      formation.annular.cellulation.rotation := by
    have hboundary := pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
      formation.annular.cellulation.rotation boundary.component
        boundary.component_boundary
    change edge ∈ vertexSetCrossingEdges formation.annular.RS
      ((pair.componentSide boundary.component)ᶜ) at hedge
    rw [vertexSetCrossingEdges_compl, hboundary] at hedge
    exact hedge
  change edge ∈ pair.crossingSupport at hcut
  rw [pair.mem_crossingSupport_iff] at hcut
  rcases hcut with hleft | hright
  · rcases (pair.left.mem_crossingEdges_iff edge).1 hleft with
      ⟨index, hindex⟩
    let step : Fin 2 := ⟨index.val, by
      simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
        Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
        Formation.LocalLayerPair.firstLayer,
        Formation.LocalLayerPair.firstWalk] using index.isLt⟩
    left
    refine ⟨step, ?_⟩
    simpa [pointwiseSelectedSourceLocalLayerLeftCrossingAt, layers, pair, step]
      using hindex.symm
  · rcases (pair.right.mem_crossingEdges_iff edge).1 hright with
      ⟨index, hindex⟩
    let step : Fin 2 := ⟨index.val, by
      simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
        Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
        Formation.LocalLayerPair.secondLayer,
        Formation.LocalLayerPair.secondWalk] using index.isLt⟩
    right
    refine ⟨step, ?_⟩
    simpa [pointwiseSelectedSourceLocalLayerRightCrossingAt, layers, pair, step]
      using hindex.symm

/-- Every residual tracked adjacency touches one of the two selected outgoing
crossings.  Incoming crossings cannot occur because they are already retained
by the cumulative input. -/
theorem pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt_adj_touches_rightCrossing
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) {x y : G.edgeSet}
    (hadj : (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
      formation corridor hinterior offset color first second).Adj x y) :
    ∃ step : Fin 2,
      x = pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
          hinterior offset step ∨
        y = pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
          hinterior offset step := by
  let inside := pointwiseSelectedSourceLocalLayerCellVertexSideAt formation
    corridor hinterior offset
  have hcell : pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset = vertexSetRegionEdges formation.annular.RS inside := by
    exact pointwiseSelectedSourceLocalLayerCellRegionAt_eq_vertexSetRegionEdges
      formation corridor hinterior offset
  have hlocalized := regionalTrackedSeamGraph_adj_localizes_to_vertexCut
    formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset)
    inside color first second (by
      simpa [pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt,
        hcell] using hadj)
  rcases hlocalized with
    ⟨_hxOld, _hxNotCell, _hyCell, hyNotOld, hyCut⟩ |
      ⟨_hxCell, hxNotOld, hxCut, _hyOld, _hyNotCell⟩
  · rcases pointwiseSelectedSourceLocalLayerCellCrossingAt_eq_left_or_right
      formation corridor hinterior offset hyCut with
      ⟨step, hyLeft⟩ | ⟨step, hyRight⟩
    · have hyMem : y ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
            corridor hinterior offset := by
        rw [hyLeft]
        exact Finset.mem_union_left _
          (pointwiseSelectedSourceLocalLayerSerialInputRegionAt_leftCrossing
            formation corridor hinterior offset step)
      exact (hyNotOld hyMem).elim
    · exact ⟨step, Or.inr hyRight⟩
  · rcases pointwiseSelectedSourceLocalLayerCellCrossingAt_eq_left_or_right
      formation corridor hinterior offset hxCut with
      ⟨step, hxLeft⟩ | ⟨step, hxRight⟩
    · have hxMem : x ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
            corridor hinterior offset := by
        rw [hxLeft]
        exact Finset.mem_union_left _
          (pointwiseSelectedSourceLocalLayerSerialInputRegionAt_leftCrossing
            formation corridor hinterior offset step)
      exact (hxNotOld hxMem).elim
    · exact ⟨step, Or.inl hxRight⟩

/-- Every non-isolated residual seam edge belongs to the fourteen-edge closed
outgoing neighbourhood. -/
theorem pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) :
    (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt formation
      corridor hinterior offset color first second).support ⊆
      pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt formation
        corridor hinterior offset := by
  intro edge hedge
  rcases (SimpleGraph.mem_support _).1 hedge with ⟨neighbor, hadj⟩
  have hambient : formation.annular.RS.edgeAdjacencyGraph.Adj edge neighbor :=
    ((regionalTrackedSeamGraph_adj_iff formation.annular.RS _ _ color first
      second edge neighbor).1 hadj).1.1
  rcases
      pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt_adj_touches_rightCrossing
        formation corridor hinterior offset color first second hadj with
    ⟨step, hedgeRight | hneighborRight⟩
  · apply (formation.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
    exact Or.inl ((mem_indexedCrossingEdgeSet_iff _ _).2
      ⟨step, hedgeRight.symm⟩)
  · apply (formation.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
    exact Or.inr ⟨neighbor,
      (mem_indexedCrossingEdgeSet_iff _ _).2
        ⟨step, hneighborRight.symm⟩, hambient⟩

/-- The selected Cell graph and residual seam transported to one stable
twenty-one-slot coordinate system. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color) :
    BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool) :=
  boundedCarrierGraphFamilyCode
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior offset) 21 5
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      web corridor hinterior offset hcell)
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionPointAt
      web.toFormation corridor hinterior offset)
    (fun factor =>
      if factor.2 then
        pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
          web.toFormation corridor hinterior offset color
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
      else
        regionalTrackedEdgeGraph web.annular.RS
          (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
            corridor hinterior offset) color
          (trackedColorPairColors factor.1).1
          (trackedColorPairColors factor.1).2)

private theorem pointwiseSelectedSourceLocalLayerCellTrackedGraph_support_subset_transitionCarrier
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    (regionalTrackedEdgeGraph formation.annular.RS
      (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset) color
      (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2).support ⊆
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          formation corridor hinterior offset : Set _) := by
  intro edge hedge
  rcases hedge with ⟨neighbor, hadj⟩
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hadj.2.1)

private theorem pointwiseSelectedSourceLocalLayerSerialTrackedSeam_support_subset_transitionCarrier
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt formation
      corridor hinterior offset color (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).support ⊆
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset : Set _) := by
  intro edge hedge
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
      formation corridor hinterior offset color
        (trackedColorPairColors pair).1 (trackedColorPairColors pair).2 hedge))

/-- The common code preserves complete selected-Cell reachability. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt_cell_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color) (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset}) :
    ((pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt
      web corridor hinterior offset hcell color).graph (pair, false)).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (regionalTrackedEdgeGraph web.annular.RS
        (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset) color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    _ 21 5
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      web corridor hinterior offset hcell)
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionPointAt
      web.toFormation corridor hinterior offset) _ (pair, false)
    (pointwiseSelectedSourceLocalLayerCellTrackedGraph_support_subset_transitionCarrier
      web.toFormation corridor hinterior offset color pair) first second

/-- The same common code preserves complete residual-seam reachability. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt_seam_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color) (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset}) :
    ((pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt
      web corridor hinterior offset hcell color).graph (pair, true)).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
        web.toFormation corridor hinterior offset color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    _ 21 5
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      web corridor hinterior offset hcell)
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionPointAt
      web.toFormation corridor hinterior offset) _ (pair, true)
    (pointwiseSelectedSourceLocalLayerSerialTrackedSeam_support_subset_transitionCarrier
      web.toFormation corridor hinterior offset color pair) first second

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
