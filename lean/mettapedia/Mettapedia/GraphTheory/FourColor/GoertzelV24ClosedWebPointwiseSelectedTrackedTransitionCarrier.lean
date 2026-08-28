import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFiniteTrackedLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedSerialTerminalProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicEdgeAdjacencyNeighborhood
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedBoundaryCounts
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpace
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalBoundaryProfileFiniteState

/-!
# Common tracked rolling carrier for a pointwise-selected Cell

The tracked rolling update uses one coordinate system for the six-edge Cell,
the closed edge-adjacency neighborhood of its two outgoing crossings, and the
retained rung terminal.  The three pieces have sizes at most `6`, `14`, and
`1`, hence fit the stable twenty-one-slot ABI.

All geometry in this file is built from the pointwise-selected crossings.
The old global shared-edge selector does not occur in the carrier or its five
distinguished coordinates.
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
open GoertzelV24FramedBoundaryCounts
open GoertzelV24HexCorridorSkeleton
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedTrackedTransitionCarrierEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

/-- The graph-backed annular carrier is uniformly subcubic: boundary stubs
have degree one and every other vertex has degree three. -/
theorem pointwiseSelected_annularRS_incidentEdges_card_le_three
    {data : AnnularBoundaryData G 5} (formation : Formation data) (vertex : V) :
    (formation.annular.RS.incidentEdges vertex).card ≤ 3 := by
  have hincident : formation.annular.RS.incidentEdges vertex =
      incidentEdgeFinset G vertex := by
    ext edge
    rw [mem_toRotationSystem_incidentEdges_iff]
    simp [incidentEdgeFinset]
  rw [hincident]
  by_cases hinner : ∃ inner : Fin 5, vertex = data.innerStub inner
  · rcases hinner with ⟨inner, rfl⟩
    rw [formation.boundary_wellFormed.inner_stub_degree_one]
    omega
  · by_cases houter : ∃ outer : Fin 5, vertex = data.outerStub outer
    · rcases houter with ⟨outer, rfl⟩
      rw [formation.boundary_wellFormed.outer_stub_degree_one]
      omega
    · rw [formation.boundary_wellFormed.cubic_elsewhere vertex
          (fun inner heq => hinner ⟨inner, heq⟩)
          (fun outer heq => houter ⟨outer, heq⟩)]

/-- The two outgoing crossings together with their complete ambient
edge-adjacency neighborhoods. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  formation.annular.RS.edgeAdjacencyClosedCarrier
    (indexedCrossingEdgeSet
      (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset))

/-- Two selected outgoing crossings have a closed subcubic neighborhood of
cardinality at most fourteen. -/
theorem pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt_card_le_fourteen
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    (pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt formation
      corridor hinterior offset).card ≤ 14 := by
  calc
    (pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt
        formation corridor hinterior offset).card ≤
        7 * (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerRightCrossingAt formation
            corridor hinterior offset)).card := by
      exact formation.annular.RS
        |>.edgeAdjacencyClosedCarrier_card_le_seven_mul_of_incidentEdges_card_le_three
          (pointwiseSelected_annularRS_incidentEdges_card_le_three formation) _
    _ ≤ 7 * 2 := Nat.mul_le_mul_left 7
      (card_indexedCrossingEdgeSet_le
        (pointwiseSelectedSourceLocalLayerRightCrossingAt formation
          corridor hinterior offset))
    _ = 14 := by norm_num

/-- One outgoing selected crossing as a live point of the fourteen-edge
neighborhood carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialOutgoingCrossingPointAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt formation
        corridor hinterior offset} := by
  refine ⟨pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
    hinterior offset step, ?_⟩
  apply (formation.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).2
  exact Or.inl ((mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, rfl⟩)

/-- The exact common carrier used by the selected tracked Cell update. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior
      offset ∪
    pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt formation
      corridor hinterior offset) ∪
  {pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor hinterior
    offset}

/-- The common selected transition carrier fits the stable twenty-one slots. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6) :
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      formation corridor hinterior offset).card ≤ 21 := by
  have hseam :=
    pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt_card_le_fourteen
      formation corridor hinterior offset
  have hunion := Finset.card_union_le
    (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset)
    (pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt
      formation corridor hinterior offset)
  calc
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset).card ≤
        (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
            hinterior offset ∪
          pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt
            formation corridor hinterior offset).card + 1 := by
      unfold pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      simpa using Finset.card_union_le
        (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
            hinterior offset ∪
          pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt
            formation corridor hinterior offset)
        {pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor
          hinterior offset}
    _ ≤ (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset).card +
        (pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt
          formation corridor hinterior offset).card + 1 :=
      Nat.add_le_add_right hunion 1
    _ ≤ 21 := by omega

/-- Four selected Cell crossings followed by the retained shared rung. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedTransitionPointAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    Fin 5 → {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset} :=
  fun index => by
    rcases (finSumFinEquiv.symm index : Fin 4 ⊕ Fin 1) with crossing | terminal
    · let point := pointwiseSelectedSourceLocalLayerCellPortAt formation corridor
        hinterior offset crossing
      exact ⟨point.1, Finset.mem_union_left _ (Finset.mem_union_left _ point.2)⟩
    · exact ⟨pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor
          hinterior offset,
        Finset.mem_union_right _ (by simp)⟩

/-- Prefix-independent uncoloured geometry on the common selected carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6) :
    BoundedCarrierGraphFamilyCode 21 5 Unit :=
  boundedCarrierGraphFamilyCode
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      formation corridor hinterior offset) 21 5
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      formation corridor hinterior offset hcell)
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionPointAt
      formation corridor hinterior offset)
    (fun _ => formation.annular.RS.edgeAdjacencyGraph)

/-- The selected geometry code remembers the exact live carrier cardinality. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt_vertexCount_eq
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6) :
    (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt formation corridor
      hinterior offset hcell).vertexCount.val =
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset).card := by
  rfl

/-- The uncoloured code preserves literal ambient edge adjacency exactly. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt_adj_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6)
    (first second : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset}) :
    ((pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt formation corridor
      hinterior offset hcell).graph ()).Adj
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      formation.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_adj_iff _ 21 5
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      formation corridor hinterior offset hcell)
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionPointAt
      formation corridor hinterior offset)
    (fun _ => formation.annular.RS.edgeAdjacencyGraph) () first second

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
