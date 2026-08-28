import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFacePrefixAttachmentState
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphThreeFactorContraction

/-!
# Finite facial closure of one pointwise-selected Cell

The selected predecessor, literal Cell, and residual seam are the three exact
factors of the pre-rebase facial graph.  The predecessor attachment state and
the two local graphs already use the same twenty-four-slot carrier.  This file
proves that their graph-free finite closure recovers complete facial
reachability after adjoining the Cell.

Thus the cumulative prefix is no longer consulted as a graph after its finite
attachment state has been extracted.  Outgoing fragment decoding and capped
progress remain separate projections of this closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceFiniteClosure

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SimpleGraphThreeFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceFiniteClosureEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Embed a live selected-code coordinate in the fixed twenty-four-slot
predecessor carrier. -/
def pointwiseSelectedSourceLocalLayerSerialFaceFiniteStableSlot
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool) :
    Fin code.vertexCount.val → Fin 24 :=
  fun coordinate => Fin.castLE (Nat.le_of_lt_succ code.vertexCount.isLt)
    coordinate

/-- The graph-free facial component step.  The first factor is reconstructed
from the finite predecessor state; `false` selects the Cell graph and `true`
the residual seam. -/
def PointwiseSelectedSourceLocalLayerSerialFaceFiniteComponentStep
    (state : PointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) : Prop :=
  SupportedPortResidualFactoredReachability
      state.toBoundedSupportedPortResidualCode
      (fun leftPort rightPort : Fin 4 => leftPort = rightPort)
      (pointwiseSelectedSourceLocalLayerSerialFaceFiniteStableSlot code left)
      (pointwiseSelectedSourceLocalLayerSerialFaceFiniteStableSlot code right) ∨
    (code.graph false).Reachable left right ∨
    (code.graph true).Reachable left right

/-- Every nontrivial switch among the selected predecessor, Cell, and seam
occurs on their common literal-dart carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_transitionCarrierClosure
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (left right : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    (faceRegionalDartGraph formation.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
        corridor hinterior offset)).Reachable left.1 right.1 ↔
      Relation.ReflTransGen
        (SelectedThreeFactorComponentStep
          (faceRegionalDartGraph formation.annular.RS
            (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              formation corridor hinterior offset))
          (faceRegionalDartGraph formation.annular.RS
            (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
              hinterior offset))
          (pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt
            formation corridor hinterior offset)
          (fun dart => dart ∈
            pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
              formation corridor hinterior offset)) left right := by
  rw [pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor
    formation corridor hinterior offset]
  apply reachable_sup_sup_iff_subtype_threeFactorComponentClosure
  · intro x middle y _hx hy _hprefix hcell
    exact
      pointwiseSelectedSourceLocalLayerCellFaceDartGraph_support_subset_transitionCarrier
        formation corridor hinterior offset
        (SimpleGraph.mem_support_of_reachable hy hcell)
  · intro x middle y _hx hy _hprefix hseam
    exact
      pointwiseSelectedSourceLocalLayerFaceDartSeam_support_subset_transitionCarrier
        formation corridor hinterior offset
        (SimpleGraph.mem_support_of_reachable hy hseam)
  · intro x middle y _hx hy _hcell hseam
    exact
      pointwiseSelectedSourceLocalLayerFaceDartSeam_support_subset_transitionCarrier
        formation corridor hinterior offset
        (SimpleGraph.mem_support_of_reachable hy hseam)

/-- Complete facial reachability after adjoining the selected literal Cell is
the closure of a graph-free relation on at most twenty-four coordinates. -/
theorem pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
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
    (faceRegionalDartGraph formation.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
        corridor hinterior offset)).Reachable left.1 right.1 ↔
      Relation.ReflTransGen
        (PointwiseSelectedSourceLocalLayerSerialFaceFiniteComponentStep
          (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
            formation corridor hinterior offset hcell)
          (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation
            corridor hinterior offset hcell))
        (carrierCoordinate
          (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
            formation corridor hinterior offset) left)
        (carrierCoordinate
          (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
            formation corridor hinterior offset) right) := by
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt
    formation corridor hinterior offset hcell
  let state :=
    pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation
      corridor hinterior offset hcell
  rw [pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_transitionCarrierClosure
    formation corridor hinterior offset left right]
  have hslot (dart : {dart // dart ∈ carrier}) :
      pointwiseSelectedSourceLocalLayerSerialFaceFiniteStableSlot code
          (coordinate dart) =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell dart := by
    rfl
  have hstep (first second : {dart // dart ∈ carrier}) :
      SelectedThreeFactorComponentStep
          (faceRegionalDartGraph formation.annular.RS
            (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              formation corridor hinterior offset))
          (faceRegionalDartGraph formation.annular.RS
            (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
              hinterior offset))
          (pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt
            formation corridor hinterior offset)
          (fun dart => dart ∈ carrier) first second ↔
        PointwiseSelectedSourceLocalLayerSerialFaceFiniteComponentStep state code
          (coordinate first) (coordinate second) := by
    simp only [SelectedThreeFactorComponentStep,
      PointwiseSelectedSourceLocalLayerSerialFaceFiniteComponentStep]
    rw [hslot first, hslot second]
    constructor
    · rintro (hprefix | hcellStep | hseam)
      · exact Or.inl
          ((pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
            formation corridor hinterior offset hcell first second).2 hprefix)
      · exact Or.inr (Or.inl
          ((pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt_cell_reachable_iff
            formation corridor hinterior offset hcell first second).2 hcellStep))
      · exact Or.inr (Or.inr
          ((pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt_seam_reachable_iff
            formation corridor hinterior offset hcell first second).2 hseam))
    · rintro (hprefix | hcellStep | hseam)
      · exact Or.inl
          ((pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
            formation corridor hinterior offset hcell first second).1 hprefix)
      · exact Or.inr (Or.inl
          ((pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt_cell_reachable_iff
            formation corridor hinterior offset hcell first second).1 hcellStep))
      · exact Or.inr (Or.inr
          ((pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt_seam_reachable_iff
            formation corridor hinterior offset hcell first second).1 hseam))
  constructor
  · intro hclosure
    exact Relation.ReflTransGen.lift coordinate
      (fun first second h => (hstep first second).1 h) hclosure
  · intro hclosure
    have hlift := Relation.ReflTransGen.lift coordinate.symm
      (fun first second h =>
        (hstep (coordinate.symm first) (coordinate.symm second)).2 (by
          simpa using h)) hclosure
    simpa [coordinate, carrier] using hlift

end

end GoertzelV24ClosedWebPointwiseSelectedFaceFiniteClosure

end Mettapedia.GraphTheory.FourColor
