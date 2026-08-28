import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedLocalCellCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexSlabConnectivityProfile

/-!
# Finite tracked letter for a pointwise-selected literal Cell

The four distinguished points of the selected Cell carrier are its two
incoming and two outgoing primal crossings, in literal left-then-right path
order.  A six-slot family code then records all three two-colour regional
graphs on the exact selected edge carrier.

Unlike the historical source-local letter, this construction uses only the
pointwise selected primal edges and the restricted annular interior-face
receipt.  No global unique-shared-edge hypothesis is retained.
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
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFiniteTrackedLetterEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

/-- The selected Cell's two incoming and two outgoing crossings, embedded as
the four distinguished points of its exact regional edge carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerCellPortAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    Fin 4 → {edge // edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset} :=
  fun index => by
    rcases (finSumFinEquiv.symm index : Fin 2 ⊕ Fin 2) with left | right
    · exact ⟨pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
          hinterior offset left,
        pointwiseSelectedSourceLocalLayerCellRegionAt_leftCrossing formation
          corridor hinterior offset left⟩
    · exact ⟨pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
          hinterior offset right,
        pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing formation
          corridor hinterior offset right⟩

/-- The common six-edge code for all three tracked-colour graphs on one
pointwise-selected literal Cell. -/
noncomputable def pointwiseSelectedSourceLocalLayerCellTrackedFamilyCodeAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (coloring : G.EdgeColoring Color)
    (hfinite : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6) :
    BoundedCarrierGraphFamilyCode 6 4 TrackedColorPair :=
  let region := pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
    hinterior offset
  boundedCarrierGraphFamilyCode region 6 4 hfinite
    (pointwiseSelectedSourceLocalLayerCellPortAt formation corridor hinterior
      offset)
    (fun pair =>
      let colors := trackedColorPairColors pair
      regionalTrackedEdgeGraph formation.annular.RS region coloring
        colors.1 colors.2)

/-- The code stores the exact selected regional carrier size. -/
theorem pointwiseSelectedSourceLocalLayerCellTrackedFamilyCodeAt_vertexCount_eq
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (coloring : G.EdgeColoring Color)
    (hfinite : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6) :
    (pointwiseSelectedSourceLocalLayerCellTrackedFamilyCodeAt formation corridor
      hinterior offset coloring hfinite).vertexCount.val =
      (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset).card := by
  rfl

/-- Each of the first two distinguished slots is the corresponding incoming
selected crossing. -/
theorem pointwiseSelectedSourceLocalLayerCellPortAt_left
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    (pointwiseSelectedSourceLocalLayerCellPortAt formation corridor hinterior
      offset (finSumFinEquiv (Sum.inl step : Fin 2 ⊕ Fin 2))).1 =
        pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
          hinterior offset step := by
  simp [pointwiseSelectedSourceLocalLayerCellPortAt]

/-- Each of the final two distinguished slots is the corresponding outgoing
selected crossing. -/
theorem pointwiseSelectedSourceLocalLayerCellPortAt_right
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    (pointwiseSelectedSourceLocalLayerCellPortAt formation corridor hinterior
      offset (finSumFinEquiv (Sum.inr step : Fin 2 ⊕ Fin 2))).1 =
        pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
          hinterior offset step := by
  simp [pointwiseSelectedSourceLocalLayerCellPortAt]

/-- The finite family represents every tracked adjacency on the selected
regional carrier exactly. -/
theorem pointwiseSelectedSourceLocalLayerCellTrackedFamilyCodeAt_adj_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (coloring : G.EdgeColoring Color)
    (hfinite : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset}) :
    ((pointwiseSelectedSourceLocalLayerCellTrackedFamilyCodeAt formation
      corridor hinterior offset coloring hfinite).graph pair).Adj
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset) coloring (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2).Adj first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_adj_iff _ 6 4 hfinite
    (pointwiseSelectedSourceLocalLayerCellPortAt formation corridor hinterior
      offset)
    (fun trackedPair =>
      let colors := trackedColorPairColors trackedPair
      regionalTrackedEdgeGraph formation.annular.RS _ coloring
        colors.1 colors.2)
    pair first second

/-- Complete regional tracked reachability is preserved by the finite code,
not merely its adjacency table. -/
theorem pointwiseSelectedSourceLocalLayerCellTrackedFamilyCodeAt_reachable_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (coloring : G.EdgeColoring Color)
    (hfinite : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset}) :
    ((pointwiseSelectedSourceLocalLayerCellTrackedFamilyCodeAt formation
      corridor hinterior offset coloring hfinite).graph pair).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset) coloring (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2).Reachable first.1 second.1 := by
  refine boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    _ 6 4 hfinite
    (pointwiseSelectedSourceLocalLayerCellPortAt formation corridor hinterior
      offset)
    (fun trackedPair =>
      let colors := trackedColorPairColors trackedPair
      regionalTrackedEdgeGraph formation.annular.RS _ coloring
        colors.1 colors.2)
    pair ?_ first second
  intro edge hedge
  rcases hedge with ⟨other, hadj⟩
  exact hadj.2.1

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
