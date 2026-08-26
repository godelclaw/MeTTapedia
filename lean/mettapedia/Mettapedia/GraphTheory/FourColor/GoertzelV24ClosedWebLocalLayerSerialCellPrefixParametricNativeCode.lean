import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricTrackedClosure

/-!
# Prefix-parametric native tracked code

The finite tracked code stores uncoloured Cell geometry together with two
partial colour tables.  This file proves that reconstructing its Cell and seam
graphs agrees exactly with the literal prefix/Cell splice for every prefix
colour function, rather than only for the ambient Tait colouring.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricNativeCode

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedBoolColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricTrackedClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24TerminalProfileSeamResidual
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance prefixParametricNativeCodeOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Evaluation of the finite right-biased colour splice at a represented
carrier edge, with an arbitrary prefix colour function. -/
theorem sourceLocalLayerSerialFiniteSplicedColorForColor_codeAt_slot
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
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    SourceLocalLayerSerialFiniteSplicedColor
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          prefixColor)
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset edge) =
      if edge.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset then
        some (cellColor edge.1)
      else if edge.1 ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset then
        some (prefixColor edge.1)
      else none := by
  unfold SourceLocalLayerSerialFiniteSplicedColor
  rw [sourceLocalLayerSerialCarrierColorCodeAt_slot,
    sourceLocalLayerSerialCarrierColorCodeAt_slot]
  by_cases hcell : edge.1 ∈
      sourceLocalLayerCellRegionAt corridor hunique offset
  · simp [hcell]
  · simp [hcell]

/-- The finite splice carries a tracked colour exactly when the represented
edge lies in the prefix/Cell union and its literal spliced colour is tracked. -/
theorem
    sourceLocalLayerSerialCarrierHasTrackedColor_splicedForColor_codeAt_slot_iff
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
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    SourceLocalLayerSerialCarrierHasTrackedColor
        (SourceLocalLayerSerialFiniteSplicedColor
          (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
            corridor hunique offset
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
            prefixColor)
          (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
            corridor hunique offset
            (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor))
        pair
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset edge) ↔
      edge.1 ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∪
            sourceLocalLayerCellRegionAt corridor hunique offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            prefixColor cellColor edge.1) := by
  unfold SourceLocalLayerSerialCarrierHasTrackedColor
  rw [sourceLocalLayerSerialFiniteSplicedColorForColor_codeAt_slot]
  by_cases hcell : edge.1 ∈
      sourceLocalLayerCellRegionAt corridor hunique offset
  · simp [sourceLocalLayerSerialCellSplicedColorAt, hcell]
  · by_cases hold : edge.1 ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset
    · simp [sourceLocalLayerSerialCellSplicedColorAt, hcell, hold]
    · simp [sourceLocalLayerSerialCellSplicedColorAt, hcell, hold]

/-- On the canonical carrier, the reconstructed seam from arbitrary prefix and
Cell colour tables is the literal residual seam of their splice. -/
theorem sourceLocalLayerSerialFiniteTrackedSeamGraphForColorAt_adj_iff
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
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    (SourceLocalLayerSerialFiniteTrackedSeamGraph
      (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
        coloring web corridor hunique offset)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        prefixColor)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
      pair).Adj (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
        (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            prefixColor cellColor)
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Adj first.1 second.1 := by
  unfold SourceLocalLayerSerialFiniteTrackedSeamGraph
  simp only [sourceLocalLayerSerialTrackedGeometryStableSlot_coordinate]
  rw [sourceLocalLayerSerialTrackedGeometryCodeAt_adj_iff,
    sourceLocalLayerSerialCarrierHasTrackedColor_splicedForColor_codeAt_slot_iff,
    sourceLocalLayerSerialCarrierHasTrackedColor_splicedForColor_codeAt_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff]
  unfold sourceLocalLayerSerialTerminalTrackedSeamAt
  rw [regionalTrackedSeamGraph_adj_iff]
  change
    web.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 ∧
      (first.1 ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∪
            sourceLocalLayerCellRegionAt corridor hunique offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            prefixColor cellColor first.1)) ∧
      (second.1 ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∪
            sourceLocalLayerCellRegionAt corridor hunique offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            prefixColor cellColor second.1)) ∧
      ((first.1 ∈
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
          first.1 ∉ sourceLocalLayerCellRegionAt corridor hunique offset ∧
          second.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
          second.1 ∉
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) ∨
        (first.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
          first.1 ∉
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
          second.1 ∈
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
          second.1 ∉ sourceLocalLayerCellRegionAt corridor hunique offset)) ↔
      ((web.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              prefixColor cellColor first.1) ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              prefixColor cellColor second.1)) ∧
        ((first.1 ∈
              sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
            first.1 ∉ sourceLocalLayerCellRegionAt corridor hunique offset ∧
            second.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
            second.1 ∉
              sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) ∨
          (first.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
            first.1 ∉
              sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
            second.1 ∈
              sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
            second.1 ∉ sourceLocalLayerCellRegionAt corridor hunique offset)))
  aesop

/-- Reconstructing the tracked code from arbitrary prefix and Cell colour
tables is exactly the literal spliced tracked code, factor by factor. -/
theorem sourceLocalLayerSerialTrackedCodeOfFiniteColorsForColorAt_graph_eq
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
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (factor : TrackedColorPair × Bool) :
    (sourceLocalLayerSerialTrackedCodeOfFiniteColors
      (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
        coloring web corridor hunique offset)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        prefixColor)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
      ).graph factor =
        (sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal
          caps coloring web corridor hunique offset
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            prefixColor cellColor)).graph factor := by
  let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  let coordinate := carrierCoordinate carrier
  apply SimpleGraph.ext
  funext left right
  apply propext
  let first := coordinate.symm left
  let second := coordinate.symm right
  have hleft : coordinate first = left := coordinate.apply_symm_apply left
  have hright : coordinate second = right := coordinate.apply_symm_apply right
  rw [← hleft, ← hright]
  rcases factor with ⟨pair, seam⟩
  cases seam
  · have hfinite := sourceLocalLayerSerialFiniteCellTrackedGraphAt_adj_iff
      graphData minimal caps coloring web corridor hunique offset cellColor pair
      first second
    have hstored := boundedCarrierGraphFamilyCode_adj_iff carrier 21 5
      (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        graphData minimal caps coloring web corridor hunique offset)
      (sourceLocalLayerSerialTrackedTransitionPointAt graphData caps coloring web
        corridor hunique offset)
      (fun factor : TrackedColorPair × Bool =>
        if factor.2 then
          sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              prefixColor cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
        else
          regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset)
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              prefixColor cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2)
      (pair, false) first second
    have hcellColor : ∀ edge,
        edge ∈ sourceLocalLayerCellRegionAt corridor hunique offset →
          sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            prefixColor cellColor edge = cellColor edge := by
      intro edge hedge
      exact sourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem corridor
        hunique offset prefixColor cellColor hedge
    have hregional :
        regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset)
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              prefixColor cellColor)
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 =
          regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 := by
      ext left right
      simp only [regionalTrackedEdgeGraph, RotationSystem.trackedEdgeGraph]
      constructor
      · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
        exact ⟨⟨hadj, (hcellColor left hleft) ▸ hleftTracked,
          (hcellColor right hright) ▸ hrightTracked⟩, hleft, hright⟩
      · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
        exact ⟨⟨hadj, (hcellColor left hleft).symm ▸ hleftTracked,
          (hcellColor right hright).symm ▸ hrightTracked⟩, hleft, hright⟩
    rw [hregional] at hstored
    exact hfinite.trans (by
      simpa [sourceLocalLayerSerialTrackedCodeOfFiniteColors,
        sourceLocalLayerSerialTrackedTransitionCodeForColorAt, carrier,
        coordinate] using hstored.symm)
  · have hfinite :=
      sourceLocalLayerSerialFiniteTrackedSeamGraphForColorAt_adj_iff graphData
        minimal caps coloring web corridor hunique offset prefixColor cellColor
          pair first second
    have hstored := boundedCarrierGraphFamilyCode_adj_iff carrier 21 5
      (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        graphData minimal caps coloring web corridor hunique offset)
      (sourceLocalLayerSerialTrackedTransitionPointAt graphData caps coloring web
        corridor hunique offset)
      (fun factor : TrackedColorPair × Bool =>
        if factor.2 then
          sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              prefixColor cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
        else
          regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset)
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              prefixColor cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2)
      (pair, true) first second
    exact hfinite.trans (by
      simpa [sourceLocalLayerSerialTrackedCodeOfFiniteColors,
        sourceLocalLayerSerialTrackedTransitionCodeForColorAt, carrier,
        coordinate] using hstored.symm)

/-- Native Boolean reconstruction has the exact literal spliced graph at each
tracked Cell/seam factor, for arbitrary prefix colours. -/
theorem
    sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometryForColorAt_toGraph_eq
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
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (factor : TrackedColorPair × Bool) :
    (sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
        (ofGraphFamilyCode
          (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
            coloring web corridor hunique offset))
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          prefixColor)
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
      ).toGraph factor =
        (sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal
          caps coloring web corridor hunique offset
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            prefixColor cellColor)).graph factor := by
  rw [sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_toGraph,
    sourceLocalLayerSerialTrackedCodeOfFiniteColorsForColorAt_graph_eq]

/-- The whole dependent family code, including its carrier and named points,
is representation-invariant under arbitrary prefix/Cell splicing. -/
theorem sourceLocalLayerSerialTrackedCodeOfFiniteColorsForColorAt_eq
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
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    sourceLocalLayerSerialTrackedCodeOfFiniteColors
      (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
        coloring web corridor hunique offset)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        prefixColor)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor) =
      sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal
        caps coloring web corridor hunique offset
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          prefixColor cellColor) := by
  rw [BoundedCarrierGraphFamilyCode.mk.injEq]
  refine ⟨rfl, HEq.rfl, ?_⟩
  apply heq_of_eq
  funext factor
  exact sourceLocalLayerSerialTrackedCodeOfFiniteColorsForColorAt_graph_eq
    graphData minimal caps coloring web corridor hunique offset prefixColor
      cellColor factor

end

end GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricNativeCode

end Mettapedia.GraphTheory.FourColor
