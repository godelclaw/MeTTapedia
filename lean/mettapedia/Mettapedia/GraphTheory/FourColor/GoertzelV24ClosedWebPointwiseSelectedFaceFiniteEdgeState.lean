import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputCap

/-!
# Finite selected primal-edge identity state

Facial closure runs on dart occurrences, while capped progress counts distinct
primal edges.  This file extracts, for the selected twenty-four-slot carrier,
the two finite observables needed to bridge them: equality of underlying
primal edges and membership in the newly adjoined Cell.

The fixed graph-free state type is shared with the generic finite decoder.
Only its source extraction and reflection theorems are pointwise-selected.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceFiniteEdgeState

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceFiniteEdgeStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Extract selected edge identity and literal Cell membership, padding unused
slots with `false`. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6) :
    SourceLocalLayerSerialFaceFiniteEdgeState := by
  classical
  let decode :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionDartAtSlot? formation
      corridor hinterior offset hcell
  exact {
    samePrimalEdge := fun left right =>
      match decode left, decode right with
      | some leftDart, some rightDart =>
          decide (formation.annular.RS.edgeOf leftDart.1 =
            formation.annular.RS.edgeOf rightDart.1)
      | _, _ => false
    cellPresent := fun slot =>
      match decode slot with
      | some dart => decide (formation.annular.RS.edgeOf dart.1 ∈
          pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
            hinterior offset)
      | none => false }

/-- On represented selected slots, the finite table is exact primal-edge
equality. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt_samePrimalEdge_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (left right : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    (pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation
      corridor hinterior offset hcell).samePrimalEdge
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell left)
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell right) = true ↔
      formation.annular.RS.edgeOf left.1 =
        formation.annular.RS.edgeOf right.1 := by
  classical
  simp [pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt]

/-- On a represented selected slot, the new-region bit is exact literal Cell
membership. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt_cellPresent_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (dart : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    (pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation
      corridor hinterior offset hcell).cellPresent
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell dart) = true ↔
      formation.annular.RS.edgeOf dart.1 ∈
        pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset := by
  classical
  simp [pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt]

/-- Predecessor and Cell presence jointly decide exact selected pre-rebase
output membership. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputPresent_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (dart : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation
          corridor hinterior offset hcell).interfacePresent
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell dart) = true ∨
      (pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation
          corridor hinterior offset hcell).cellPresent
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell dart) = true ↔
      formation.annular.RS.edgeOf dart.1 ∈
        pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
          corridor hinterior offset := by
  rw [pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_interfacePresent,
    pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt_cellPresent_iff,
    ← pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell
      formation corridor hinterior offset]
  simp

end

end GoertzelV24ClosedWebPointwiseSelectedFaceFiniteEdgeState

end Mettapedia.GraphTheory.FourColor
