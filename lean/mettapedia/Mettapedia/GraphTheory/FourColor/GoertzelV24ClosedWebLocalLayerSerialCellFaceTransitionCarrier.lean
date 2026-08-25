import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicEdgeAdjacencyNeighborhood
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceDartFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellPortalCompleteness
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceRegionalDartCarrier

/-!
# One finite literal-dart carrier for an actual source-Cell facial transition

The exact facial update has two local factors: the literal Cell face graph and
the residual seam joining it to the accumulated prefix.  This file puts both
on one root-independent carrier.  The Cell contributes the two darts over each
of its at most six edges; portal completeness puts the seam in the closed
face-permutation neighbourhood of the two outgoing crossings.  Hence the
common carrier has at most twenty-four literal darts.

The bound is stated from the honest local premise `cellRegion.card <= 6`.
This file does not manufacture that geometric premise, encode predecessor
attachments, compute capped face progress, or assert a deterministic successor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

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

local instance closedWebLocalLayerSerialCellFaceTransitionCarrierEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Consecutive literal face darts over distinct primal edges give adjacent
vertices of the edge-adjacency graph. -/
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

/-- Every dart in the closed facial neighborhood of a selected edge lies
over that edge or over an edge adjacent to it.  This is the exact bridge from
the occurrence-sensitive facial carrier to the coarser edge-adjacency
carrier; it uses no cubicity or two-sidedness assumption. -/
theorem edgeOf_mem_edgeAdjacencyClosedCarrier_of_mem_closedDartCarrier
    (RS : RotationSystem V G.edgeSet) (edges : Finset G.edgeSet)
    (dart : RS.D) (hdart : dart ∈ closedDartCarrier RS edges) :
    RS.edgeOf dart ∈ RS.edgeAdjacencyClosedCarrier edges := by
  rw [closedDartCarrier, Finset.mem_biUnion] at hdart
  rcases hdart with ⟨base, hbase, hdart⟩
  rw [Finset.mem_insert, mem_faceDartNeighbors_iff] at hdart
  rcases hdart with heq | hforward | hbackward
  · subst dart
    exact (RS.mem_edgeAdjacencyClosedCarrier_iff edges _).2
      (Or.inl ((mem_dartsOnEdges_iff RS edges base).1 hbase))
  · by_cases hedge : RS.edgeOf base = RS.edgeOf dart
    · exact (RS.mem_edgeAdjacencyClosedCarrier_iff edges _).2
        (Or.inl (hedge ▸ (mem_dartsOnEdges_iff RS edges base).1 hbase))
    · have hadj := edgeAdjacencyGraph_adj_of_faceDartStep_of_edge_ne
        RS (Or.inl hforward) hedge
      exact (RS.mem_edgeAdjacencyClosedCarrier_iff edges _).2
        (Or.inr ⟨RS.edgeOf base,
          (mem_dartsOnEdges_iff RS edges base).1 hbase, hadj.symm⟩)
  · have hstep : base = RS.phi dart := by
      rw [hbackward]
      simp
    by_cases hedge : RS.edgeOf dart = RS.edgeOf base
    · exact (RS.mem_edgeAdjacencyClosedCarrier_iff edges _).2
        (Or.inl (hedge ▸ (mem_dartsOnEdges_iff RS edges base).1 hbase))
    · have hadj := edgeAdjacencyGraph_adj_of_faceDartStep_of_edge_ne
        RS (Or.inl hstep) hedge
      exact (RS.mem_edgeAdjacencyClosedCarrier_iff edges _).2
        (Or.inr ⟨RS.edgeOf base,
          (mem_dartsOnEdges_iff RS edges base).1 hbase, hadj⟩)

/-- Every adjacency of the root-independent literal-dart seam touches one of
the two named outgoing source crossings. -/
theorem sourceLocalLayerSerialTerminalFaceDartSeamAt_adj_touches_rightCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) {left right : web.annular.RS.D}
    (hadj : (sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique
      offset).Adj left right) :
    ∃ step : Fin 2,
      web.annular.RS.edgeOf left =
          sourceLocalLayerRightCrossingAt corridor hunique offset step ∨
        web.annular.RS.edgeOf right =
          sourceLocalLayerRightCrossingAt corridor hunique offset step := by
  let inside := sourceLocalLayerCellVertexSide corridor hunique
    (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)
  have hcell : sourceLocalLayerCellRegionAt corridor hunique offset =
      vertexSetRegionEdges web.annular.RS inside := by
    have hside := sourceLocalLayerCellVertexSide_eq_retained_compl
      corridor hunique (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)
    exact congrArg (vertexSetRegionEdges web.annular.RS) hside.symm
  have hseam : (faceRegionalDartSeamGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      (vertexSetRegionEdges web.annular.RS inside)).Adj left right := by
    simpa [sourceLocalLayerSerialTerminalFaceDartSeamAt, hcell] using hadj
  rcases (faceRegionalDartSeamGraph_adj_iff web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      (vertexSetRegionEdges web.annular.RS inside) left right).1 hseam with
    ⟨_hne, hstep, hforward | hbackward⟩
  · have hedgeNe : web.annular.RS.edgeOf left ≠
        web.annular.RS.edgeOf right := by
      intro hedge
      apply hforward.2.1
      rw [hedge]
      exact hforward.2.2.1
    have hedgeAdj := edgeAdjacencyGraph_adj_of_faceDartStep_of_edge_ne
      web.annular.RS hstep hedgeNe
    have hrightCut := mem_vertexSetCrossingEdges_of_adjacent_not_mem_region
      web.annular.RS inside hedgeAdj hforward.2.1 hforward.2.2.1
    have hrightNotOld := hforward.2.2.2
    rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique
      offset hrightCut with ⟨step, hrightLeft⟩ | ⟨step, hrightRight⟩
    · have hrightMem : web.annular.RS.edgeOf right ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset := by
        rw [hrightLeft]
        exact Finset.mem_union_left _
          (sourceLocalLayerSerialInputRegionAt_leftCrossing corridor hunique
            offset step)
      exact (hrightNotOld hrightMem).elim
    · exact ⟨step, Or.inr hrightRight⟩
  · have hedgeNe : web.annular.RS.edgeOf left ≠
        web.annular.RS.edgeOf right := by
      intro hedge
      apply hbackward.2.1
      rw [hedge]
      exact hbackward.2.2.1
    have hedgeAdj := edgeAdjacencyGraph_adj_of_faceDartStep_of_edge_ne
      web.annular.RS hstep hedgeNe
    have hleftCut := mem_vertexSetCrossingEdges_of_adjacent_not_mem_region
      web.annular.RS inside hedgeAdj.symm hbackward.2.2.2 hbackward.1
    have hleftNotOld := hbackward.2.1
    rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique
      offset hleftCut with ⟨step, hleftLeft⟩ | ⟨step, hleftRight⟩
    · have hleftMem : web.annular.RS.edgeOf left ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset := by
        rw [hleftLeft]
        exact Finset.mem_union_left _
          (sourceLocalLayerSerialInputRegionAt_leftCrossing corridor hunique
            offset step)
      exact (hleftNotOld hleftMem).elim
    · exact ⟨step, Or.inl hleftRight⟩

/-- Root-independent closed dart neighbourhood of the two outgoing crossings. -/
def sourceLocalLayerSerialFaceOutgoingDartCarrierAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) : Finset web.annular.RS.D :=
  closedDartCarrier web.annular.RS
    (indexedCrossingEdgeSet
      (sourceLocalLayerRightCrossingAt corridor hunique offset))

/-- The outgoing literal-dart seam carrier has at most twelve positions. -/
theorem sourceLocalLayerSerialFaceOutgoingDartCarrierAt_card_le_twelve
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialFaceOutgoingDartCarrierAt corridor hunique offset
      ).card ≤ 12 := by
  calc
    (sourceLocalLayerSerialFaceOutgoingDartCarrierAt corridor hunique offset
      ).card ≤ 6 *
        (indexedCrossingEdgeSet
          (sourceLocalLayerRightCrossingAt corridor hunique offset)).card :=
      closedDartCarrier_card_le_six_mul web.annular.RS _
    _ ≤ 6 * 2 := Nat.mul_le_mul_left 6
      (card_indexedCrossingEdgeSet_le
        (sourceLocalLayerRightCrossingAt corridor hunique offset))
    _ = 12 := by norm_num

/-- Every non-isolated literal-dart seam occurrence lies in the outgoing
closed dart carrier. -/
theorem sourceLocalLayerSerialTerminalFaceDartSeamAt_support_subset_outgoingCarrier
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset
      ).support ⊆
      (sourceLocalLayerSerialFaceOutgoingDartCarrierAt corridor hunique offset :
        Set web.annular.RS.D) := by
  intro dart hdart
  rcases (SimpleGraph.mem_support _).1 hdart with ⟨neighbor, hadj⟩
  rcases sourceLocalLayerSerialTerminalFaceDartSeamAt_adj_touches_rightCrossing
      corridor hunique offset hadj with
    ⟨step, hdartRight | hneighborRight⟩
  · apply mem_closedDartCarrier_of_edge_mem
    exact (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, hdartRight.symm⟩
  · have hstep :=
      (faceRegionalDartSeamGraph_adj_iff web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        (sourceLocalLayerCellRegionAt corridor hunique offset) dart neighbor).1
        hadj |>.2.1
    apply mem_closedDartCarrier_of_face_neighbor_of_edge_mem
      web.annular.RS _ neighbor dart
    · exact (mem_indexedCrossingEdgeSet_iff _ _).2
        ⟨step, hneighborRight.symm⟩
    · rcases hstep with hforward | hbackward
      · apply Or.inr
        apply web.annular.RS.phi.injective
        simpa using hforward.symm
      · exact Or.inl hbackward

/-- Darts over the literal Cell together with the outgoing seam neighbourhood. -/
def sourceLocalLayerSerialFaceTransitionCarrierAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) : Finset web.annular.RS.D :=
  dartsOnEdges web.annular.RS
      (sourceLocalLayerCellRegionAt corridor hunique offset) ∪
    sourceLocalLayerSerialFaceOutgoingDartCarrierAt corridor hunique offset

/-- If the literal Cell has at most six edges, its common facial transition
carrier has at most twenty-four literal darts. -/
theorem sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
      ).card ≤ 24 := by
  calc
    (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
      ).card ≤
        (dartsOnEdges web.annular.RS
          (sourceLocalLayerCellRegionAt corridor hunique offset)).card +
        (sourceLocalLayerSerialFaceOutgoingDartCarrierAt corridor hunique offset
          ).card := Finset.card_union_le _ _
    _ ≤ 2 * (sourceLocalLayerCellRegionAt corridor hunique offset).card +
          12 := Nat.add_le_add
      (dartsOnEdges_card_le_two_mul web.annular.RS _)
      (sourceLocalLayerSerialFaceOutgoingDartCarrierAt_card_le_twelve corridor
        hunique offset)
    _ ≤ 24 := by omega

/-- The literal Cell facial factor is supported on the common transition
carrier. -/
theorem sourceLocalLayerCellFaceDartGraph_support_subset_transitionCarrier
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerCellRegionAt corridor hunique offset)).support ⊆
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset :
        Set web.annular.RS.D) := by
  intro dart hdart
  rcases (SimpleGraph.mem_support _).1 hdart with ⟨neighbor, hadj⟩
  exact Finset.mem_union_left _
    ((mem_dartsOnEdges_iff web.annular.RS _ dart).2 hadj.2.2.1)

/-- The residual facial seam factor is supported on the common transition
carrier. -/
theorem sourceLocalLayerFaceDartSeam_support_subset_transitionCarrier
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset
      ).support ⊆
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset :
        Set web.annular.RS.D) := by
  intro dart hdart
  exact Finset.mem_union_right _
    (sourceLocalLayerSerialTerminalFaceDartSeamAt_support_subset_outgoingCarrier
      corridor hunique offset hdart)

/-- Cell and residual seam face graphs transported through one common
twenty-four-slot coordinate system.  `false` selects the Cell and `true` the
seam. -/
def sourceLocalLayerSerialFaceTransitionCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    BoundedCarrierGraphFamilyCode 24 0 Bool :=
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  boundedCarrierGraphFamilyCode carrier 24 0
    (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour corridor
      hunique offset hcell)
    (fun index => Fin.elim0 index)
    (fun seam => if seam then
      sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset
    else
      faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerCellRegionAt corridor hunique offset))

/-- The common code preserves complete literal-Cell facial reachability. -/
theorem sourceLocalLayerSerialFaceTransitionCodeAt_cell_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (first second : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    ((sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset hcell
      ).graph false).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerCellRegionAt corridor hunique offset)).Reachable
          first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    _ 24 0
    (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour corridor
      hunique offset hcell)
    (fun index => Fin.elim0 index) _ false
    (sourceLocalLayerCellFaceDartGraph_support_subset_transitionCarrier corridor
      hunique offset) first second

/-- The same common code preserves complete literal-dart seam reachability. -/
theorem sourceLocalLayerSerialFaceTransitionCodeAt_seam_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (first second : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    ((sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset hcell
      ).graph true).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset
        ).Reachable first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    _ 24 0
    (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour corridor
      hunique offset hcell)
    (fun index => Fin.elim0 index) _ true
    (sourceLocalLayerFaceDartSeam_support_subset_transitionCarrier corridor
      hunique offset) first second

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
