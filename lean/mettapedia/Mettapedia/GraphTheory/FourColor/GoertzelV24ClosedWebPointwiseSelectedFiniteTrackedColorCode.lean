import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFiniteColorCompatibility

/-!
# Reconstruct selected tracked factors from finite colours

The generic twenty-one-slot colour reconstruction is instantiated here on the
pointwise-selected Cell carrier.  An uncoloured local adjacency graph, the
terminal-prefix colour table, and the literal Cell colour table determine the
tracked Cell graph and residual seam for every tracked colour pair.

Only the generic finite reconstruction combinators are reused from the
historical development.  Every source reflection theorem below is stated on
the pointwise-selected carrier and restricted interior-face receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFiniteTrackedColorCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

/-- The generic stable-slot embedding agrees definitionally with the selected
transition carrier's canonical embedding. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialTrackedGeometryStableSlot_coordinate
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (edge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset}) :
    SourceLocalLayerSerialTrackedGeometryStableSlot
        (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web
          corridor hinterior offset hcell)
        (carrierCoordinate _ edge) =
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt web
        corridor hinterior offset hcell edge := by
  rfl

/-- At a represented slot, the generic tracked-colour predicate recovers exact
selected-region membership and the literal edge colour. -/
theorem pointwiseSelectedSourceLocalLayerSerialCarrierHasTrackedColor_codeAt_slot_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (region : Finset G.edgeSet) (color : G.edgeSet → Color)
    (pair : TrackedColorPair)
    (edge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset}) :
    SourceLocalLayerSerialCarrierHasTrackedColor
        (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
          web.toFormation corridor hinterior offset region color)
        pair
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt web
          corridor hinterior offset hcell edge) ↔
      edge.1 ∈ region ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (color edge.1) := by
  unfold SourceLocalLayerSerialCarrierHasTrackedColor
  rw [pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_slot]
  by_cases hedge : edge.1 ∈ region <;> simp [hedge]

/-- A represented stable slot is active exactly when its selected edge belongs
to the region encoded by the table. -/
theorem pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (region : Finset G.edgeSet) (color : G.edgeSet → Color)
    (edge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset}) :
    (∃ value,
      pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
          corridor hinterior offset region color
          (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt web
            corridor hinterior offset hcell edge) = some value) ↔
      edge.1 ∈ region := by
  rw [pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_slot]
  by_cases hedge : edge.1 ∈ region <;> simp [hedge]

/-- `none` records exact selected-region non-membership. -/
theorem pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (region : Finset G.edgeSet) (color : G.edgeSet → Color)
    (edge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset}) :
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset region color
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt web
          corridor hinterior offset hcell edge) = none ↔
      edge.1 ∉ region := by
  rw [pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_slot]
  by_cases hedge : edge.1 ∈ region <;> simp [hedge]

/-- The generic finite splice carries the literal selected spliced colour on
the union of the terminal prefix and Cell regions. -/
theorem pointwiseSelectedSourceLocalLayerSerialFiniteSplicedColorForColorAt_codeAt_slot
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor cellColor : G.edgeSet → Color)
    (edge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset}) :
    SourceLocalLayerSerialFiniteSplicedColor
        (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
          web.toFormation corridor hinterior offset
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            web.toFormation corridor hinterior offset) prefixColor)
        (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
          web.toFormation corridor hinterior offset
          (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
            corridor hinterior offset) cellColor)
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt web
          corridor hinterior offset hcell edge) =
      if edge.1 ∈ pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
          corridor hinterior offset then
        some (cellColor edge.1)
      else if edge.1 ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            web.toFormation corridor hinterior offset then
        some (prefixColor edge.1)
      else none := by
  unfold SourceLocalLayerSerialFiniteSplicedColor
  rw [pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_slot,
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_slot]
  by_cases hedge : edge.1 ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior offset <;> simp [hedge]

/-- The finite splice has a tracked colour exactly on the literal selected
union and with the literal spliced colour. -/
theorem pointwiseSelectedSourceLocalLayerSerialCarrierHasTrackedColor_spliced_codeAt_slot_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor cellColor : G.edgeSet → Color) (pair : TrackedColorPair)
    (edge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset}) :
    SourceLocalLayerSerialCarrierHasTrackedColor
        (SourceLocalLayerSerialFiniteSplicedColor
          (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
            web.toFormation corridor hinterior offset
            (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior offset) prefixColor)
          (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
            web.toFormation corridor hinterior offset
            (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
              corridor hinterior offset) cellColor))
        pair
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt web
          corridor hinterior offset hcell edge) ↔
      edge.1 ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior offset ∪
            pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
              corridor hinterior offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
            web.toFormation corridor hinterior offset prefixColor cellColor
            edge.1) := by
  unfold SourceLocalLayerSerialCarrierHasTrackedColor
  rw [pointwiseSelectedSourceLocalLayerSerialFiniteSplicedColorForColorAt_codeAt_slot]
  by_cases hnew : edge.1 ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior offset
  · simp [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt, hnew]
  · by_cases hold : edge.1 ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior offset
    · simp [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt, hnew,
        hold]
    · simp [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt, hnew,
        hold]

/-- Finite reconstruction of the selected Cell tracked graph is exact. -/
theorem pointwiseSelectedSourceLocalLayerSerialFiniteCellTrackedGraphAt_adj_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (cellColor : G.edgeSet → Color) (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset}) :
    (SourceLocalLayerSerialFiniteCellTrackedGraph
      (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web
        corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset) cellColor)
      pair).Adj (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
        (regionalTrackedEdgeGraph web.annular.RS
          (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
            corridor hinterior offset) cellColor
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Adj first.1 second.1 := by
  change
    ((pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web corridor
        hinterior offset hcell).graph ()).Adj
        (carrierCoordinate _ first) (carrierCoordinate _ second) ∧
      SourceLocalLayerSerialCarrierHasTrackedColor
        (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
          web.toFormation corridor hinterior offset
          (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
            corridor hinterior offset) cellColor)
        pair
        (SourceLocalLayerSerialTrackedGeometryStableSlot
          (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web
            corridor hinterior offset hcell) (carrierCoordinate _ first)) ∧
      SourceLocalLayerSerialCarrierHasTrackedColor
        (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
          web.toFormation corridor hinterior offset
          (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
            corridor hinterior offset) cellColor)
        pair
        (SourceLocalLayerSerialTrackedGeometryStableSlot
          (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web
            corridor hinterior offset hcell) (carrierCoordinate _ second)) ↔ _
  rw [pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt_adj_iff,
    pointwiseSelectedSourceLocalLayerSerialTrackedGeometryStableSlot_coordinate,
    pointwiseSelectedSourceLocalLayerSerialTrackedGeometryStableSlot_coordinate,
    pointwiseSelectedSourceLocalLayerSerialCarrierHasTrackedColor_codeAt_slot_iff,
    pointwiseSelectedSourceLocalLayerSerialCarrierHasTrackedColor_codeAt_slot_iff]
  change
    web.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 ∧
      (first.1 ∈ pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
          corridor hinterior offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (cellColor first.1)) ∧
      (second.1 ∈ pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
          corridor hinterior offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (cellColor second.1)) ↔
      ((web.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 (cellColor first.1) ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 (cellColor second.1)) ∧
        first.1 ∈ pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
          corridor hinterior offset ∧
        second.1 ∈ pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
          corridor hinterior offset)
  aesop

/-- Finite reconstruction of the residual selected seam is exact for arbitrary
prefix and Cell colour functions. -/
theorem pointwiseSelectedSourceLocalLayerSerialFiniteTrackedSeamGraphAt_adj_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor cellColor : G.edgeSet → Color) (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset}) :
    (SourceLocalLayerSerialFiniteTrackedSeamGraph
      (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web
        corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior offset) prefixColor)
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset) cellColor)
      pair).Adj (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
        (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
          web.toFormation corridor hinterior offset
          (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
            web.toFormation corridor hinterior offset prefixColor cellColor)
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Adj first.1 second.1 := by
  unfold SourceLocalLayerSerialFiniteTrackedSeamGraph
  simp only [pointwiseSelectedSourceLocalLayerSerialTrackedGeometryStableSlot_coordinate]
  rw [pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt_adj_iff,
    pointwiseSelectedSourceLocalLayerSerialCarrierHasTrackedColor_spliced_codeAt_slot_iff,
    pointwiseSelectedSourceLocalLayerSerialCarrierHasTrackedColor_spliced_codeAt_slot_iff,
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff,
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff,
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff,
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff]
  unfold pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
  rw [regionalTrackedSeamGraph_adj_iff]
  change
    web.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 ∧
      (first.1 ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior offset ∪
            pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
              corridor hinterior offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
            web.toFormation corridor hinterior offset prefixColor cellColor
            first.1)) ∧
      (second.1 ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior offset ∪
            pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
              corridor hinterior offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
            web.toFormation corridor hinterior offset prefixColor cellColor
            second.1)) ∧
      ((first.1 ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior offset ∧
          first.1 ∉ pointwiseSelectedSourceLocalLayerCellRegionAt
            web.toFormation corridor hinterior offset ∧
          second.1 ∈ pointwiseSelectedSourceLocalLayerCellRegionAt
            web.toFormation corridor hinterior offset ∧
          second.1 ∉
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior offset) ∨
        (first.1 ∈ pointwiseSelectedSourceLocalLayerCellRegionAt
            web.toFormation corridor hinterior offset ∧
          first.1 ∉
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior offset ∧
          second.1 ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior offset ∧
          second.1 ∉ pointwiseSelectedSourceLocalLayerCellRegionAt
            web.toFormation corridor hinterior offset)) ↔
      ((web.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
              web.toFormation corridor hinterior offset prefixColor cellColor
              first.1) ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
              web.toFormation corridor hinterior offset prefixColor cellColor
              second.1)) ∧
        ((first.1 ∈
              pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                web.toFormation corridor hinterior offset ∧
            first.1 ∉ pointwiseSelectedSourceLocalLayerCellRegionAt
              web.toFormation corridor hinterior offset ∧
            second.1 ∈ pointwiseSelectedSourceLocalLayerCellRegionAt
              web.toFormation corridor hinterior offset ∧
            second.1 ∉
              pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                web.toFormation corridor hinterior offset) ∨
          (first.1 ∈ pointwiseSelectedSourceLocalLayerCellRegionAt
              web.toFormation corridor hinterior offset ∧
            first.1 ∉
              pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                web.toFormation corridor hinterior offset ∧
            second.1 ∈
              pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                web.toFormation corridor hinterior offset ∧
            second.1 ∉ pointwiseSelectedSourceLocalLayerCellRegionAt
              web.toFormation corridor hinterior offset)))
  aesop

/-- Complete selected tracked transition reconstructed from prefix-independent
geometry and two finite colour tables. -/
def pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColors
    (geometry : BoundedCarrierGraphFamilyCode 21 5 Unit)
    (prefixCode cellCode :
      PointwiseSelectedSourceLocalLayerSerialCarrierColorCode) :
    BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool) :=
  sourceLocalLayerSerialTrackedCodeOfFiniteColors geometry prefixCode cellCode

/-- Executable Boolean reflection of the selected reconstructed transition. -/
def pointwiseSelectedSourceLocalLayerSerialTrackedBoolCodeOfFiniteColors
    (geometry : BoundedCarrierGraphFamilyCode 21 5 Unit)
    (prefixCode cellCode :
      PointwiseSelectedSourceLocalLayerSerialCarrierColorCode) :
    BoundedCarrierBoolGraphFamilyCode 21 5 (TrackedColorPair × Bool) :=
  ofGraphFamilyCode
    (pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColors geometry
      prefixCode cellCode)

/-- On literal selected source data, every reconstructed factor is exactly the
canonical Cell-or-seam factor for the spliced colour function. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_graph_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor cellColor : G.edgeSet → Color)
    (factor : TrackedColorPair × Bool) :
    (pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColors
      (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web
        corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior offset) prefixColor)
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset) cellColor)).graph factor =
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt
        web corridor hinterior offset hcell
        (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
          corridor hinterior offset prefixColor cellColor)).graph factor := by
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior offset
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
  · have hfinite :=
      pointwiseSelectedSourceLocalLayerSerialFiniteCellTrackedGraphAt_adj_iff
        web corridor hinterior offset hcell cellColor pair first second
    have hstored := boundedCarrierGraphFamilyCode_adj_iff carrier 21 5
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        web corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionPointAt
        web.toFormation corridor hinterior offset)
      (fun factor : TrackedColorPair × Bool =>
        if factor.2 then
          pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
            web.toFormation corridor hinterior offset
            (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
              web.toFormation corridor hinterior offset prefixColor cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
        else
          regionalTrackedEdgeGraph web.annular.RS
            (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
              corridor hinterior offset)
            (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
              web.toFormation corridor hinterior offset prefixColor cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2)
      (pair, false) first second
    have hcellColor : ∀ edge,
        edge ∈ pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
          corridor hinterior offset →
        pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
          corridor hinterior offset prefixColor cellColor edge =
            cellColor edge := by
      intro edge hedge
      exact pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
        web.toFormation corridor hinterior offset prefixColor cellColor hedge
    have hregional :
        regionalTrackedEdgeGraph web.annular.RS
            (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
              corridor hinterior offset)
            (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
              web.toFormation corridor hinterior offset prefixColor cellColor)
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 =
          regionalTrackedEdgeGraph web.annular.RS
            (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
              corridor hinterior offset) cellColor
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 := by
      ext localLeft localRight
      simp only [regionalTrackedEdgeGraph, RotationSystem.trackedEdgeGraph]
      constructor
      · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleftMem, hrightMem⟩
        exact ⟨⟨hadj, (hcellColor localLeft hleftMem) ▸ hleftTracked,
          (hcellColor localRight hrightMem) ▸ hrightTracked⟩,
          hleftMem, hrightMem⟩
      · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleftMem, hrightMem⟩
        exact ⟨⟨hadj, (hcellColor localLeft hleftMem).symm ▸ hleftTracked,
          (hcellColor localRight hrightMem).symm ▸ hrightTracked⟩,
          hleftMem, hrightMem⟩
    rw [hregional] at hstored
    exact hfinite.trans (by
      simpa [pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColors,
        sourceLocalLayerSerialTrackedCodeOfFiniteColors,
        pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt,
        carrier, coordinate] using hstored.symm)
  · have hfinite :=
      pointwiseSelectedSourceLocalLayerSerialFiniteTrackedSeamGraphAt_adj_iff
        web corridor hinterior offset hcell prefixColor cellColor pair first
          second
    have hstored := boundedCarrierGraphFamilyCode_adj_iff carrier 21 5
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        web corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionPointAt
        web.toFormation corridor hinterior offset)
      (fun factor : TrackedColorPair × Bool =>
        if factor.2 then
          pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
            web.toFormation corridor hinterior offset
            (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
              web.toFormation corridor hinterior offset prefixColor cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
        else
          regionalTrackedEdgeGraph web.annular.RS
            (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
              corridor hinterior offset)
            (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
              web.toFormation corridor hinterior offset prefixColor cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2)
      (pair, true) first second
    exact hfinite.trans (by
      simpa [pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColors,
        sourceLocalLayerSerialTrackedCodeOfFiniteColors,
        pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt,
        carrier, coordinate] using hstored.symm)

/-- Consequently the selected finite reconstruction preserves complete
component reachability in both tracked factors. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor cellColor : G.edgeSet → Color)
    (factor : TrackedColorPair × Bool)
    (left right : Fin
      (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web corridor
        hinterior offset hcell).vertexCount.val) :
    ((pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColors
      (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web corridor
        hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior offset) prefixColor)
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset) cellColor)).graph factor).Reachable left right ↔
      ((pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt
        web corridor hinterior offset hcell
        (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
          corridor hinterior offset prefixColor cellColor)).graph factor).Reachable
        left right := by
  rw [pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_graph_eq]
  rfl

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
