import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedSeamFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier

/-!
# One finite carrier for the tracked source-Cell transition

The tracked part of one literal serial Cell has two finite local factors: the
Cell itself and the residual seam joining it to the accumulated prefix.  Their
earlier codes used unrelated coordinates.  This file puts both factors on one
common carrier: the six-edge Cell region, the fourteen-edge outgoing seam
carrier, and the retained shared rung.  Hence the common carrier has at most
twenty-one edges.

Five source-ordered points are retained on that carrier: the two incoming
crossings, the two outgoing crossings, and the shared rung terminal.  Both
tracked factors are transported through the same coordinate equivalence, and
their complete ambient reachability is preserved.

This closes a coordinate junction, not the tracked recurrence itself.  The
next theorem must reconstruct the accumulated-prefix component relation on
these coordinates from the incoming profile and its finite attachment state;
it may not store the successor relation as part of a purported local letter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section


local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The Cell, its outgoing residual-seam neighborhood, and the retained seam
rung, all as literal edges of the same opened carrier. -/
noncomputable def sourceLocalLayerSerialTrackedTransitionCarrierAt
    (graphData : Data G)
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
    (offset : Fin (blockLength - 3)) :
    Finset caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet :=
  (sourceLocalLayerCellRegionAt corridor hunique offset ∪
      sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset) ∪
    {sourceLocalLayerSharedRungAt corridor hunique offset}

/-- The common transition carrier has at most `6 + 14 + 1` literal edges. -/
theorem sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
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
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
      web corridor hunique offset).card ≤ 21 := by
  have hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6 :=
    sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps coloring
      web corridor hunique offset
  have hseam :
      (sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset).card
        ≤ 14 :=
    sourceLocalLayerSerialOutgoingEdgeCarrierAt_card_le_fourteen corridor
      hunique offset
  have hunion :
      (sourceLocalLayerCellRegionAt corridor hunique offset ∪
        sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique offset).card
        ≤
      (sourceLocalLayerCellRegionAt corridor hunique offset).card +
        (sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique
          offset).card :=
    Finset.card_union_le _ _
  calc
    (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
      web corridor hunique offset).card
        ≤ (sourceLocalLayerCellRegionAt corridor hunique offset ∪
              sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique
                offset).card + 1 := by
          unfold sourceLocalLayerSerialTrackedTransitionCarrierAt
          simpa using Finset.card_union_le
            (sourceLocalLayerCellRegionAt corridor hunique offset ∪
              sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique
                offset)
            {sourceLocalLayerSharedRungAt corridor hunique offset}
    _ ≤ (sourceLocalLayerCellRegionAt corridor hunique offset).card +
          (sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique
            offset).card + 1 := by
          exact Nat.add_le_add_right hunion 1
    _ ≤ 21 := by omega

/-- Four Cell boundary crossings followed by the retained shared rung. -/
noncomputable def sourceLocalLayerSerialTrackedTransitionPointAt
    (graphData : Data G)
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
    (offset : Fin (blockLength - 3)) :
    Fin 5 → {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset} :=
  fun index => by
    rcases (finSumFinEquiv.symm index : Fin 4 ⊕ Fin 1) with crossing | terminal
    · let point := sourceLocalLayerCellPortAt corridor hunique offset crossing
      refine ⟨point.1, ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ point.2)
    · refine ⟨sourceLocalLayerSharedRungAt corridor hunique offset, ?_⟩
      exact Finset.mem_union_right _ (by simp)

/-- The two finite factors transported through one common coordinate system
for an arbitrary edge-color function.  `false` is the literal Cell factor and
`true` is its residual seam.  The color function is an explicit parameter so
that a later positive-`Count` witness can supply its own local coloring rather
than being forced to reuse the ambient closed-web coloring. -/
noncomputable def sourceLocalLayerSerialTrackedTransitionCodeForColorAt
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
    (color : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet →
      Color) :
    BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool) :=
  let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  boundedCarrierGraphFamilyCode carrier 21 5
    (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      graphData minimal caps coloring web corridor hunique offset)
    (sourceLocalLayerSerialTrackedTransitionPointAt graphData caps coloring web
      corridor hunique offset)
    (fun factor =>
      if factor.2 then
        sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
          color (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
      else
        regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerCellRegionAt corridor hunique offset) color
          (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2)

/-- Ambient-color specialization retained for existing source witnesses. -/
noncomputable def sourceLocalLayerSerialTrackedTransitionCodeAt
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
    (offset : Fin (blockLength - 3)) :
    BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool) :=
  sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal caps
    coloring web corridor hunique offset coloring

private theorem sourceLocalLayerCellTrackedGraph_support_subset_transitionCarrier
    (graphData : Data G)
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
    (color : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet →
      Color)
    (pair : TrackedColorPair) :
    (regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerCellRegionAt corridor hunique offset) color
      (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2).support ⊆
        (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
          coloring web corridor hunique offset : Set _) := by
  intro edge hedge
  rcases hedge with ⟨neighbor, hadj⟩
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hadj.2.1)

private theorem sourceLocalLayerSerialTrackedSeam_support_subset_transitionCarrier
    (graphData : Data G)
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
    (color : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet →
      Color)
    (pair : TrackedColorPair) :
    (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
      color (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).support ⊆
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset : Set _) := by
  intro edge hedge
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (sourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
      corridor hunique offset color (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 hedge))

/-- The color-parametric common code preserves complete Cell reachability. -/
theorem sourceLocalLayerSerialTrackedTransitionCodeForColorAt_cell_reachable_iff
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
    (color : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet →
      Color)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    ((sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal
      caps coloring web corridor hunique offset color).graph
        (pair, false)).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerCellRegionAt corridor hunique offset) color
        (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    _ 21 5
    (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      graphData minimal caps coloring web corridor hunique offset)
    (sourceLocalLayerSerialTrackedTransitionPointAt graphData caps coloring web
      corridor hunique offset) _ (pair, false)
    (sourceLocalLayerCellTrackedGraph_support_subset_transitionCarrier
      graphData caps coloring web corridor hunique offset color pair) first second

/-- The same color-parametric code preserves complete residual-seam
reachability. -/
theorem sourceLocalLayerSerialTrackedTransitionCodeForColorAt_seam_reachable_iff
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
    (color : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet →
      Color)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    ((sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal
      caps coloring web corridor hunique offset color).graph
        (pair, true)).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    _ 21 5
    (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      graphData minimal caps coloring web corridor hunique offset)
    (sourceLocalLayerSerialTrackedTransitionPointAt graphData caps coloring web
      corridor hunique offset) _ (pair, true)
    (sourceLocalLayerSerialTrackedSeam_support_subset_transitionCarrier
      graphData caps coloring web corridor hunique offset color pair) first second

/-- Ambient-color compatibility wrapper for Cell reachability. -/
theorem sourceLocalLayerSerialTrackedTransitionCodeAt_cell_reachable_iff
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
    (offset : Fin (blockLength - 3)) (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    ((sourceLocalLayerSerialTrackedTransitionCodeAt graphData minimal caps
      coloring web corridor hunique offset).graph (pair, false)).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerCellRegionAt corridor hunique offset) coloring
        (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable first.1 second.1 := by
  exact sourceLocalLayerSerialTrackedTransitionCodeForColorAt_cell_reachable_iff
    graphData minimal caps coloring web corridor hunique offset coloring pair
      first second

/-- Ambient-color compatibility wrapper for seam reachability. -/
theorem sourceLocalLayerSerialTrackedTransitionCodeAt_seam_reachable_iff
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
    (offset : Fin (blockLength - 3)) (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    ((sourceLocalLayerSerialTrackedTransitionCodeAt graphData minimal caps
      coloring web corridor hunique offset).graph (pair, true)).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable first.1 second.1 := by
  exact sourceLocalLayerSerialTrackedTransitionCodeForColorAt_seam_reachable_iff
    graphData minimal caps coloring web corridor hunique offset coloring pair
      first second

end

end GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier

end Mettapedia.GraphTheory.FourColor
