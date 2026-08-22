import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFacePrefixAttachmentState
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphThreeFactorContraction

/-!
# Finite facial closure of one literal source Cell

The predecessor, literal Cell, and residual seam are the three exact factors
of one facial source transition.  The predecessor attachment state and the two
local factor graphs already live on the same fixed twenty-four-slot carrier.

This file closes that coordinate junction.  It first proves that every switch
among the three literal factors occurs on the common carrier.  It then
transports the complete three-factor closure to a graph-free relation on the
finite code.  Consequently the unbounded predecessor is consulted only
through its finite attachment state, even when a face leaves and re-enters the
local Cell neighbourhood.

This is not yet the outgoing facial profile decoder or a full one-Cell support
letter.  Face continuation, port incidence, and capped progress still have to
be projected from this closure jointly.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
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

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

local instance closedWebLocalLayerSerialCellFaceFiniteClosureEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Embed a live coordinate of the transition code in its fixed
twenty-four-slot predecessor-state carrier. -/
def sourceLocalLayerSerialFaceFiniteStableSlot
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool) :
    Fin code.vertexCount.val → Fin 24 :=
  fun coordinate => Fin.castLE (Nat.le_of_lt_succ code.vertexCount.isLt)
    coordinate

/-- The graph-free facial component step for one literal Cell.  The first
factor is reconstructed from the finite predecessor state; `false` selects
the coded Cell graph and `true` the coded residual seam. -/
def SourceLocalLayerSerialFaceFiniteComponentStep
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) : Prop :=
  SupportedPortResidualFactoredReachability
      state.toBoundedSupportedPortResidualCode
      (fun leftPort rightPort : Fin 4 => leftPort = rightPort)
      (sourceLocalLayerSerialFaceFiniteStableSlot code left)
      (sourceLocalLayerSerialFaceFiniteStableSlot code right) ∨
    (code.graph false).Reachable left right ∨
    (code.graph true).Reachable left right

/-- Every nontrivial switch among predecessor, Cell, and seam occurs on the
common literal-dart transition carrier. -/
theorem sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_transitionCarrierClosure
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (left right : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    (faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      ).Reachable left.1 right.1 ↔
      Relation.ReflTransGen
        (SelectedThreeFactorComponentStep
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
              offset))
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset))
          (sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset)
          (fun dart => dart ∈
            sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset)) left right := by
  rw [sourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor corridor
    hunique offset]
  apply reachable_sup_sup_iff_subtype_threeFactorComponentClosure
  · intro x middle y _hx hy _hprefix hcell
    exact sourceLocalLayerCellFaceDartGraph_support_subset_transitionCarrier
      corridor hunique offset (SimpleGraph.mem_support_of_reachable hy hcell)
  · intro x middle y _hx hy _hprefix hseam
    exact sourceLocalLayerFaceDartSeam_support_subset_transitionCarrier
      corridor hunique offset (SimpleGraph.mem_support_of_reachable hy hseam)
  · intro x middle y _hx hy _hcell hseam
    exact sourceLocalLayerFaceDartSeam_support_subset_transitionCarrier
      corridor hunique offset (SimpleGraph.mem_support_of_reachable hy hseam)

/-- Complete facial reachability after adjoining one literal source Cell is
the closure of a graph-free relation on at most twenty-four coordinates. -/
theorem sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcellBound :
      (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    (faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      ).Reachable left.1 right.1 ↔
      Relation.ReflTransGen
        (SourceLocalLayerSerialFaceFiniteComponentStep
          (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique
            offset hcellBound)
          (sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
            hcellBound))
        (carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset) left)
        (carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset) right) := by
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcellBound
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcellBound
  rw [sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_transitionCarrierClosure
    corridor hunique offset left right]
  have hslot (dart : {dart // dart ∈ carrier}) :
      sourceLocalLayerSerialFaceFiniteStableSlot code (coordinate dart) =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcellBound dart := by
    rfl
  have hstep (first second : {dart // dart ∈ carrier}) :
      SelectedThreeFactorComponentStep
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
              offset))
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset))
          (sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset)
          (fun dart => dart ∈ carrier) first second ↔
        SourceLocalLayerSerialFaceFiniteComponentStep state code
          (coordinate first) (coordinate second) := by
    simp only [SelectedThreeFactorComponentStep,
      SourceLocalLayerSerialFaceFiniteComponentStep]
    rw [hslot first, hslot second]
    constructor
    · rintro (hprefix | hcell | hseam)
      · exact Or.inl
          ((sourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
            corridor hunique offset hcellBound first second).2 hprefix)
      · exact Or.inr (Or.inl
          ((sourceLocalLayerSerialFaceTransitionCodeAt_cell_reachable_iff
            corridor hunique offset hcellBound first second).2 hcell))
      · exact Or.inr (Or.inr
          ((sourceLocalLayerSerialFaceTransitionCodeAt_seam_reachable_iff
            corridor hunique offset hcellBound first second).2 hseam))
    · rintro (hprefix | hcell | hseam)
      · exact Or.inl
          ((sourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
            corridor hunique offset hcellBound first second).1 hprefix)
      · exact Or.inr (Or.inl
          ((sourceLocalLayerSerialFaceTransitionCodeAt_cell_reachable_iff
            corridor hunique offset hcellBound first second).1 hcell))
      · exact Or.inr (Or.inr
          ((sourceLocalLayerSerialFaceTransitionCodeAt_seam_reachable_iff
            corridor hunique offset hcellBound first second).1 hseam))
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

end GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure

end Mettapedia.GraphTheory.FourColor
