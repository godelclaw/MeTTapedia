import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedTransitionCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceTransitionCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedBoundaryRebase

/-!
# Bounded interaction carrier for a selected Cell and rebase

The rooted rolling state must remember the cumulative prefix on every local
edge or dart which the next boundary rebase can inspect.  In the corrected
pointwise-selected geometry this carrier is the current Cell-transition
carrier together with the closed neighborhood of the four rebase roles.

The established fixed ABI remains valid: at most forty-nine tracked edges
and forty-eight facial darts.  These bounds use only the selected local Cell
bound, subcubic incidence, and the four-role rebase switch.  No global
unique-shared-edge hypothesis occurs.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24RotationFaceRegionalDartCarrier
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedCellRebaseInteractionCarrierEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

open Instance.LocalLayerFormation

/-- The four changed rebase edges together with every ambient edge adjacent
to one of them. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseTrackedCollarAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Finset G.edgeSet :=
  formation.annular.RS.edgeAdjacencyClosedCarrier
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
      corridor hinterior offset hnext)

/-- Four switch edges in a subcubic carrier have a closed edge neighborhood
of size at most twenty-eight. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseTrackedCollarAt_card_le_twentyEight
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseTrackedCollarAt formation
      corridor hinterior offset hnext).card ≤ 28 := by
  calc
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseTrackedCollarAt formation
      corridor hinterior offset hnext).card ≤
        7 * (pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt
          formation corridor hinterior offset hnext).card := by
      exact formation.annular.RS
        |>.edgeAdjacencyClosedCarrier_card_le_seven_mul_of_incidentEdges_card_le_three
          (pointwiseSelected_annularRS_incidentEdges_card_le_three formation) _
    _ ≤ 7 * 4 := Nat.mul_le_mul_left 7
      (card_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_le_four
        formation corridor hinterior offset hnext)
    _ = 28 := by norm_num

/-- Every dart whose primal edge is one of the four changed rebase edges. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Finset formation.annular.RS.D :=
  dartsOnEdges formation.annular.RS
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation corridor
      hinterior offset hnext)

/-- There are at most two darts over each of the four changed edges. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt_card_le_eight
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt formation
      corridor hinterior offset hnext).card ≤ 8 := by
  calc
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt formation
      corridor hinterior offset hnext).card ≤
        2 * (pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
          corridor hinterior offset hnext).card := by
      exact dartsOnEdges_card_le_two_mul formation.annular.RS _
    _ ≤ 2 * 4 := Nat.mul_le_mul_left 2
      (card_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_le_four
        formation corridor hinterior offset hnext)
    _ = 8 := by norm_num

/-- The one-step facial collar: every changed dart and its two face
neighbors. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Finset formation.annular.RS.D :=
  (pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt formation
    corridor hinterior offset hnext).biUnion fun dart =>
      {dart, formation.annular.RS.phi dart,
        formation.annular.RS.phi.symm dart}

/-- The selected facial computation collar has at most twenty-four darts. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt_card_le_twentyFour
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
      corridor hinterior offset hnext).card ≤ 24 := by
  let changed :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt formation
      corridor hinterior offset hnext
  calc
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
      corridor hinterior offset hnext).card ≤ changed.card * 3 := by
      apply Finset.card_biUnion_le_card_mul
      intro dart hdart
      exact (Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ <| (Finset.card_insert_le _ _).trans_eq <| by
          rw [Finset.card_singleton])
    _ ≤ 8 * 3 := Nat.mul_le_mul_right 3
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt_card_le_eight
        formation corridor hinterior offset hnext)
    _ = 24 := by norm_num

/-- The complete tracked interaction carrier for one selected literal Cell
and its following boundary rebase. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Finset G.edgeSet :=
  pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      formation corridor hinterior offset ∪
    pointwiseSelectedSourceLocalLayerBoundaryRebaseTrackedCollarAt formation corridor
      hinterior offset hnext

/-- Every current tracked Cell coordinate is retained by the complete
interaction carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_subset_interaction
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset ⊆
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        formation corridor hinterior offset hnext := by
  exact Finset.subset_union_left

/-- The selected tracked interaction carrier fits the established
forty-nine-slot ABI. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6) :
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      formation corridor hinterior offset hnext).card ≤ 49 := by
  calc
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      formation corridor hinterior offset hnext).card ≤
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          formation corridor hinterior offset).card +
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseTrackedCollarAt formation
          corridor hinterior offset hnext).card := Finset.card_union_le _ _
    _ ≤ 21 + 28 := Nat.add_le_add
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        formation corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseTrackedCollarAt_card_le_twentyEight
        formation corridor hinterior offset hnext)
    _ = 49 := by norm_num

/-- The complete facial-dart interaction carrier for the same selected Cell
and rebase. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Finset formation.annular.RS.D :=
  pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior offset ∪
    pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
      corridor hinterior offset hnext

/-- Every current facial Cell coordinate is retained by the complete
interaction carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_subset_interaction
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset ⊆
      pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        formation corridor hinterior offset hnext := by
  exact Finset.subset_union_left

/-- The selected facial interaction carrier fits the established
forty-eight-slot ABI. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6) :
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      formation corridor hinterior offset hnext).card ≤ 48 := by
  calc
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      formation corridor hinterior offset hnext).card ≤
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
          corridor hinterior offset).card +
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
          corridor hinterior offset hnext).card := Finset.card_union_le _ _
    _ ≤ 24 + 24 := Nat.add_le_add
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
        formation corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt_card_le_twentyFour
        formation corridor hinterior offset hnext)
    _ = 48 := by norm_num

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
