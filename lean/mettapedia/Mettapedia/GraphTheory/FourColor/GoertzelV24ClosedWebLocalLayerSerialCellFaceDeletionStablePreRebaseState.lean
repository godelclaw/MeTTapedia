import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePrefixState
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorUpdate

/-!
# The deletion-stable facial state after one literal Cell

The cumulative facial prefix is represented by its exact interface/exterior
factor on the rolling twenty-four-dart carrier.  The literal Cell face graph
and its residual seam are supported wholly on that carrier, so adjoining them
changes only the direct-adjacency row of the factor.

This file implements that finite recurrence and proves it exact before the
boundary-rebase deletion.  In particular, every later carrier mask can be
interpreted from the updated code.  The capped number of distinct primal edges
on each resulting face component is deliberately not claimed here; it is the
next weighted refinement of this exact connectivity factor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePreRebaseState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePrefixState
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance faceDeletionStablePreRebaseEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The two prefix-independent facial graph factors of one source Cell. -/
noncomputable def sourceLocalLayerSerialFaceLocalGraphAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    SimpleGraph web.annular.RS.D :=
  faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerCellRegionAt corridor hunique offset) ⊔
    sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset

/-- The executable adjacency row supplied by the existing common Cell/seam
carrier code. -/
def sourceLocalLayerSerialFaceLocalAdjacencyAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
      offset hcell
    Fin code.vertexCount.val → Fin code.vertexCount.val → Bool :=
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
    offset hcell
  fun left right => by
    classical
    exact decide (((code.graph false) ⊔ (code.graph true)).Adj left right)

/-- Update the deletion-stable prefix factor by adjoining the literal Cell
and residual facial seam on its bounded carrier. -/
noncomputable def sourceLocalLayerSerialFaceDeletionStablePreRebaseStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    SourceLocalLayerSerialFaceDeletionStablePrefixState :=
  let prefixState :=
    sourceLocalLayerSerialFaceDeletionStablePrefixStateAt corridor hunique
      offset hcell
  { vertexCount := prefixState.vertexCount
    code := fun _ =>
      addInterfaceAdjacency (prefixState.code ())
        (sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset
          hcell) }

private theorem sourceLocalLayerSerialFaceLocalGraph_support_subset_carrier
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialFaceLocalGraphAt corridor hunique offset).support ⊆
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset :
        Set web.annular.RS.D) := by
  intro dart hdart
  rcases hdart with ⟨neighbor, hadj⟩
  change
    (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerCellRegionAt corridor hunique offset) ⊔
      sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset).Adj
        dart neighbor at hadj
  rw [SimpleGraph.sup_adj] at hadj
  rcases hadj with hcell | hseam
  · exact sourceLocalLayerCellFaceDartGraph_support_subset_transitionCarrier
      corridor hunique offset ⟨neighbor, hcell⟩
  · exact sourceLocalLayerFaceDartSeam_support_subset_transitionCarrier
      corridor hunique offset ⟨neighbor, hseam⟩

private theorem sourceLocalLayerSerialFaceLocalGraph_support_subset_range
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let dartAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (sourceLocalLayerSerialFaceLocalGraphAt corridor hunique offset).support ⊆
      Set.range dartAt := by
  dsimp only
  intro dart hdart
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  have hcarrier : dart ∈ carrier :=
    sourceLocalLayerSerialFaceLocalGraph_support_subset_carrier corridor hunique
      offset hdart
  refine ⟨carrierCoordinate carrier ⟨dart, hcarrier⟩, ?_⟩
  simp [carrier]

private theorem sourceLocalLayerSerialFaceLocalAdjacency_exact
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card) :
    sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset hcell
        left right = true ↔
      let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
        hunique offset
      let dartAt := fun slot : Fin carrier.card =>
        ((carrierCoordinate carrier).symm slot).1
      (sourceLocalLayerSerialFaceLocalGraphAt corridor hunique offset).Adj
        (dartAt left) (dartAt right) := by
  classical
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let localCode := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
    offset hcell
  let first : {dart // dart ∈ carrier} := (carrierCoordinate carrier).symm left
  let second : {dart // dart ∈ carrier} :=
    (carrierCoordinate carrier).symm right
  have hcellIff :
      (localCode.graph false).Adj left right ↔
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerCellRegionAt corridor hunique offset)).Adj
            first.1 second.1 := by
    have h := boundedCarrierGraphFamilyCode_adj_iff carrier 24 0
      (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
        corridor hunique offset hcell)
      (fun index => Fin.elim0 index)
      (fun seam => if seam then
        sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset
      else
        faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerCellRegionAt corridor hunique offset))
      false first second
    simpa [localCode, sourceLocalLayerSerialFaceTransitionCodeAt, first, second]
      using h
  have hseamIff :
      (localCode.graph true).Adj left right ↔
        (sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset
          ).Adj first.1 second.1 := by
    have h := boundedCarrierGraphFamilyCode_adj_iff carrier 24 0
      (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
        corridor hunique offset hcell)
      (fun index => Fin.elim0 index)
      (fun seam => if seam then
        sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset
      else
        faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerCellRegionAt corridor hunique offset))
      true first second
    simpa [localCode, sourceLocalLayerSerialFaceTransitionCodeAt, first, second]
      using h
  change decide (((localCode.graph false) ⊔ (localCode.graph true)).Adj
    left right) = true ↔ _
  rw [decide_eq_true_eq, SimpleGraph.sup_adj,
    sourceLocalLayerSerialFaceLocalGraphAt, SimpleGraph.sup_adj]
  exact or_congr hcellIff hseamIff

/-- The cumulative update is exactly the pre-rebase facial graph's
interface/exterior code, row by row. -/
theorem sourceLocalLayerSerialFaceDeletionStablePreRebaseStateAt_code_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let dartAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (sourceLocalLayerSerialFaceDeletionStablePreRebaseStateAt corridor hunique
        offset hcell).code () =
      exactInterfaceExteriorCode
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset))
        dartAt := by
  dsimp only
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let dartAt := fun slot : Fin carrier.card =>
    ((carrierCoordinate carrier).symm slot).1
  let prefixGraph := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
  let localGraph := sourceLocalLayerSerialFaceLocalGraphAt corridor hunique
    offset
  have hupdate := addInterfaceAdjacency_exact_code_eq prefixGraph localGraph
    dartAt
    (sourceLocalLayerSerialFaceLocalGraph_support_subset_range corridor hunique
      offset)
    (sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset hcell)
    (sourceLocalLayerSerialFaceLocalAdjacency_exact corridor hunique offset
      hcell)
  change addInterfaceAdjacency
      (exactInterfaceExteriorCode prefixGraph dartAt)
      (sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset hcell) =
    _
  rw [sourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor corridor
    hunique offset, sup_assoc]
  exact hupdate

/-- The updated finite code presents exactly one interface/exterior step of
the literal pre-rebase facial graph. -/
theorem sourceLocalLayerSerialFaceDeletionStablePreRebaseStateAt_step_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card) :
    InterfaceExteriorFactoredStep
        ((sourceLocalLayerSerialFaceDeletionStablePreRebaseStateAt corridor
          hunique offset hcell).code ()) left right ↔
      let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
        hunique offset
      let dartAt := fun slot : Fin carrier.card =>
        ((carrierCoordinate carrier).symm slot).1
      InterfaceExteriorStep
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset))
        dartAt left right := by
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let dartAt := fun slot : Fin carrier.card =>
    ((carrierCoordinate carrier).symm slot).1
  let prefixGraph := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
  let localGraph := sourceLocalLayerSerialFaceLocalGraphAt corridor hunique
    offset
  have hupdate := addInterfaceAdjacency_exact_step_iff prefixGraph localGraph
    dartAt
    (sourceLocalLayerSerialFaceLocalGraph_support_subset_range corridor hunique
      offset)
    (sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset hcell)
    (sourceLocalLayerSerialFaceLocalAdjacency_exact corridor hunique offset
      hcell) left right
  change InterfaceExteriorFactoredStep
      (addInterfaceAdjacency
        (exactInterfaceExteriorCode prefixGraph dartAt)
        (sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset
          hcell)) left right ↔ _
  rw [sourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor corridor
    hunique offset, sup_assoc]
  exact hupdate

/-- Every carrier mask is reconstructed from the updated state.  This is the
mask-stable facial recurrence consumed by the boundary-rebase step. -/
theorem sourceLocalLayerSerialFaceDeletionStablePreRebaseStateAt_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (removed : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card → Bool)
    (left right : SurvivingInterfaceSlot
      (fun slot : Fin
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
            ).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)).symm slot).1)
      removed) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let graph := faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    let dartAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (restrictedByMask graph dartAt removed).Reachable
        (dartAt left.1) (dartAt right.1) ↔
      Relation.ReflTransGen
        (fun first second : SurvivingInterfaceSlot dartAt removed =>
          InterfaceExteriorFactoredStep
            ((sourceLocalLayerSerialFaceDeletionStablePreRebaseStateAt corridor
              hunique offset hcell).code ())
            first.1 second.1)
        left right := by
  dsimp only
  rw [restrictedByMask_reachable_iff_interfaceExteriorClosure]
  constructor
  · intro hclosure
    exact hclosure.mono fun first second hstep =>
      (sourceLocalLayerSerialFaceDeletionStablePreRebaseStateAt_step_iff
        corridor hunique offset hcell first.1 second.1).2 hstep
  · intro hclosure
    exact hclosure.mono fun first second hstep =>
      (sourceLocalLayerSerialFaceDeletionStablePreRebaseStateAt_step_iff
        corridor hunique offset hcell first.1 second.1).1 hstep

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePreRebaseState

end Mettapedia.GraphTheory.FourColor
