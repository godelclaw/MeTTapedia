import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedSeamCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceRegionalDartCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceRegionalDartSeam

/-!
# Facial transition carrier for a pointwise-selected Cell

The occurrence-sensitive facial update has the same two local factors as the
tracked update: the literal Cell face graph and the residual seam to the
terminal-aware prefix.  Darts over the at-most-six Cell edges and the closed
facial neighbourhood of the two selected outgoing crossings form a common
carrier of at most twenty-four darts.

All crossings are the pointwise-selected primal edges.  No global
shared-interior-edge selector enters this carrier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24RotationFaceRegionalDartSeam
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileVertexSideSeam
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceTransitionCarrierEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

/-- The occurrence-sensitive residual seam between the selected terminal
prefix and Cell. -/
def pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : SimpleGraph formation.annular.RS.D :=
  faceRegionalDartSeamGraph formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset)
    (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior
      offset)

/-- The selected pre-rebase facial graph is exactly predecessor, Cell, and
their residual facial seam. -/
theorem pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    faceRegionalDartGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
          formation corridor hinterior offset) =
      (faceRegionalDartGraph formation.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            formation corridor hinterior offset) ⊔
        faceRegionalDartGraph formation.annular.RS
          (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
            hinterior offset)) ⊔
        pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt formation
          corridor hinterior offset := by
  rw [← pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell
    formation corridor hinterior offset]
  exact faceRegionalDartGraph_union_eq_sup_sup_seam _ _ _

/-- Consecutive literal face darts over distinct primal edges are adjacent in
the edge-adjacency graph. -/
private theorem edgeAdjacencyGraph_adj_of_faceDartStep_of_edge_ne
    (RS : RotationSystem V G.edgeSet) {left right : RS.D}
    (hstep : right = RS.phi left ∨ left = RS.phi right)
    (hne : RS.edgeOf left ≠ RS.edgeOf right) :
    RS.edgeAdjacencyGraph.Adj (RS.edgeOf left) (RS.edgeOf right) := by
  rcases hstep with hforward | hbackward
  · apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hne
    · apply (RS.mem_incidentEdges_iff).2
      exact ⟨RS.alpha left, RS.edge_alpha left,
        (RS.vert_phi_eq_vert_alpha left).symm⟩
    · apply (RS.mem_incidentEdges_iff).2
      exact ⟨right, rfl, by simp [hforward]⟩
  · apply SimpleGraph.Adj.symm
    apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hne.symm
    · apply (RS.mem_incidentEdges_iff).2
      exact ⟨RS.alpha right, RS.edge_alpha right,
        (RS.vert_phi_eq_vert_alpha right).symm⟩
    · apply (RS.mem_incidentEdges_iff).2
      exact ⟨left, rfl, by simp [hbackward]⟩

/-- Every residual facial adjacency touches one selected outgoing crossing. -/
theorem pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt_adj_touches_rightCrossing
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) {left right : formation.annular.RS.D}
    (hadj : (pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt
      formation corridor hinterior offset).Adj left right) :
    ∃ step : Fin 2,
      formation.annular.RS.edgeOf left =
          pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
            hinterior offset step ∨
        formation.annular.RS.edgeOf right =
          pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
            hinterior offset step := by
  let inside := pointwiseSelectedSourceLocalLayerCellVertexSideAt formation
    corridor hinterior offset
  have hcell : pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset = vertexSetRegionEdges formation.annular.RS inside :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_eq_vertexSetRegionEdges
      formation corridor hinterior offset
  have hseam : (faceRegionalDartSeamGraph formation.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
        corridor hinterior offset)
      (vertexSetRegionEdges formation.annular.RS inside)).Adj left right := by
    simpa [pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt,
      hcell] using hadj
  rcases (faceRegionalDartSeamGraph_adj_iff formation.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
        corridor hinterior offset)
      (vertexSetRegionEdges formation.annular.RS inside) left right).1 hseam with
    ⟨_hne, hstep, hforward | hbackward⟩
  · have hedgeNe : formation.annular.RS.edgeOf left ≠
        formation.annular.RS.edgeOf right := by
      intro hedge
      apply hforward.2.1
      rw [hedge]
      exact hforward.2.2.1
    have hedgeAdj := edgeAdjacencyGraph_adj_of_faceDartStep_of_edge_ne
      formation.annular.RS hstep hedgeNe
    have hrightCut := mem_vertexSetCrossingEdges_of_adjacent_not_mem_region
      formation.annular.RS inside hedgeAdj hforward.2.1 hforward.2.2.1
    have hrightNotOld := hforward.2.2.2
    rcases pointwiseSelectedSourceLocalLayerCellCrossingAt_eq_left_or_right
      formation corridor hinterior offset hrightCut with
      ⟨step, hrightLeft⟩ | ⟨step, hrightRight⟩
    · have hrightMem : formation.annular.RS.edgeOf right ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
            corridor hinterior offset := by
        rw [hrightLeft]
        exact Finset.mem_union_left _
          (pointwiseSelectedSourceLocalLayerSerialInputRegionAt_leftCrossing
            formation corridor hinterior offset step)
      exact (hrightNotOld hrightMem).elim
    · exact ⟨step, Or.inr hrightRight⟩
  · have hedgeNe : formation.annular.RS.edgeOf left ≠
        formation.annular.RS.edgeOf right := by
      intro hedge
      apply hbackward.2.1
      rw [hedge]
      exact hbackward.2.2.1
    have hedgeAdj := edgeAdjacencyGraph_adj_of_faceDartStep_of_edge_ne
      formation.annular.RS hstep hedgeNe
    have hleftCut := mem_vertexSetCrossingEdges_of_adjacent_not_mem_region
      formation.annular.RS inside hedgeAdj.symm hbackward.2.2.2 hbackward.1
    have hleftNotOld := hbackward.2.1
    rcases pointwiseSelectedSourceLocalLayerCellCrossingAt_eq_left_or_right
      formation corridor hinterior offset hleftCut with
      ⟨step, hleftLeft⟩ | ⟨step, hleftRight⟩
    · have hleftMem : formation.annular.RS.edgeOf left ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
            corridor hinterior offset := by
        rw [hleftLeft]
        exact Finset.mem_union_left _
          (pointwiseSelectedSourceLocalLayerSerialInputRegionAt_leftCrossing
            formation corridor hinterior offset step)
      exact (hleftNotOld hleftMem).elim
    · exact ⟨step, Or.inl hleftRight⟩

/-- Root-independent closed dart neighbourhood of the two selected outgoing
crossings. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceOutgoingDartCarrierAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : Finset formation.annular.RS.D :=
  closedDartCarrier formation.annular.RS
    (indexedCrossingEdgeSet
      (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset))

/-- The selected outgoing facial carrier has at most twelve darts. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceOutgoingDartCarrierAt_card_le_twelve
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    (pointwiseSelectedSourceLocalLayerSerialFaceOutgoingDartCarrierAt formation
      corridor hinterior offset).card ≤ 12 := by
  calc
    (pointwiseSelectedSourceLocalLayerSerialFaceOutgoingDartCarrierAt formation
      corridor hinterior offset).card ≤ 6 *
        (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
            hinterior offset)).card :=
      closedDartCarrier_card_le_six_mul formation.annular.RS _
    _ ≤ 6 * 2 := Nat.mul_le_mul_left 6
      (card_indexedCrossingEdgeSet_le
        (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
          hinterior offset))
    _ = 12 := by norm_num

/-- Every non-isolated facial seam dart belongs to the outgoing closed dart
carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt_support_subset_outgoingCarrier
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    (pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt formation
      corridor hinterior offset).support ⊆
      (pointwiseSelectedSourceLocalLayerSerialFaceOutgoingDartCarrierAt
        formation corridor hinterior offset : Set formation.annular.RS.D) := by
  intro dart hdart
  rcases (SimpleGraph.mem_support _).1 hdart with ⟨neighbor, hadj⟩
  rcases
      pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt_adj_touches_rightCrossing
        formation corridor hinterior offset hadj with
    ⟨step, hdartRight | hneighborRight⟩
  · apply mem_closedDartCarrier_of_edge_mem
    exact (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, hdartRight.symm⟩
  · have hstep :=
      (faceRegionalDartSeamGraph_adj_iff formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset)
        (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset) dart neighbor).1 hadj |>.2.1
    apply mem_closedDartCarrier_of_face_neighbor_of_edge_mem
      formation.annular.RS _ neighbor dart
    · exact (mem_indexedCrossingEdgeSet_iff _ _).2
        ⟨step, hneighborRight.symm⟩
    · rcases hstep with hforward | hbackward
      · apply Or.inr
        apply formation.annular.RS.phi.injective
        simpa using hforward.symm
      · exact Or.inl hbackward

/-- Darts over the selected Cell together with the outgoing facial seam
neighbourhood. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : Finset formation.annular.RS.D :=
  dartsOnEdges formation.annular.RS
      (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset) ∪
    pointwiseSelectedSourceLocalLayerSerialFaceOutgoingDartCarrierAt formation
      corridor hinterior offset

/-- The selected facial transition carrier fits twenty-four stable slots. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6) :
    (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior offset).card ≤ 24 := by
  calc
    (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior offset).card ≤
        (dartsOnEdges formation.annular.RS
          (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
            hinterior offset)).card +
        (pointwiseSelectedSourceLocalLayerSerialFaceOutgoingDartCarrierAt
          formation corridor hinterior offset).card := Finset.card_union_le _ _
    _ ≤ 2 * (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset).card + 12 := Nat.add_le_add
      (dartsOnEdges_card_le_two_mul formation.annular.RS _)
      (pointwiseSelectedSourceLocalLayerSerialFaceOutgoingDartCarrierAt_card_le_twelve
        formation corridor hinterior offset)
    _ ≤ 24 := by omega

private theorem pointwiseSelectedSourceLocalLayerCellFaceDartGraph_support_subset_transitionCarrier
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    (faceRegionalDartGraph formation.annular.RS
      (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset)).support ⊆
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset : Set formation.annular.RS.D) := by
  intro dart hdart
  rcases (SimpleGraph.mem_support _).1 hdart with ⟨neighbor, hadj⟩
  exact Finset.mem_union_left _
    ((mem_dartsOnEdges_iff formation.annular.RS _ dart).2 hadj.2.2.1)

private theorem pointwiseSelectedSourceLocalLayerFaceDartSeam_support_subset_transitionCarrier
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    (pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt formation
      corridor hinterior offset).support ⊆
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset : Set formation.annular.RS.D) := by
  intro dart hdart
  exact Finset.mem_union_right _
    (pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt_support_subset_outgoingCarrier
      formation corridor hinterior offset hdart)

/-- Cell and seam facial graphs transported through one common twenty-four-slot
coordinate system. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6) :
    BoundedCarrierGraphFamilyCode 24 0 Bool :=
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior offset
  boundedCarrierGraphFamilyCode carrier 24 0
    (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
      formation corridor hinterior offset hcell)
    (fun index => Fin.elim0 index)
    (fun seam => if seam then
      pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt formation
        corridor hinterior offset
    else
      faceRegionalDartGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset))

/-- The common selected code preserves complete Cell facial reachability. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt_cell_reachable_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (first second : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    ((pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation
      corridor hinterior offset hcell).graph false).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (faceRegionalDartGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset)).Reachable first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    _ 24 0
    (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
      formation corridor hinterior offset hcell)
    (fun index => Fin.elim0 index) _ false
    (pointwiseSelectedSourceLocalLayerCellFaceDartGraph_support_subset_transitionCarrier
      formation corridor hinterior offset) first second

/-- The same selected code preserves complete residual facial-seam
reachability. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt_seam_reachable_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (first second : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    ((pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation
      corridor hinterior offset hcell).graph true).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt formation
        corridor hinterior offset).Reachable first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    _ 24 0
    (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
      formation corridor hinterior offset hcell)
    (fun index => Fin.elim0 index) _ true
    (pointwiseSelectedSourceLocalLayerFaceDartSeam_support_subset_transitionCarrier
      formation corridor hinterior offset) first second

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
