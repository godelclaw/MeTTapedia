import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorUpdate

/-!
# The deletion-stable tracked state after one literal Cell

The cumulative prefix already carries a mask-independent interface code: it
records equality, direct adjacency, and attachment through components strictly
outside the twenty-one-edge transition carrier.  The literal Cell and its
residual seam are supported wholly on that carrier.  Therefore adjoining them
changes only the direct-adjacency table.

This file implements that recurrence with the existing finite Cell/seam code
and proves it exact for the source graph.  It is the tracked-connectivity
coordinate before the boundary-rebase deletion.  No reachable-closure count or
full heterogeneous transfer letter is claimed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance trackedDeletionStablePreRebaseEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance trackedDeletionStablePreRebaseOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The two prefix-independent tracked graph factors of one source Cell. -/
noncomputable def sourceLocalLayerSerialTrackedLocalGraphForColorAt
    (caps : OrientedFacialPentagonCapPair (G := G) graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    SimpleGraph
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet :=
  regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerCellRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2 ⊔
    sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset color
      (trackedColorPairColors pair).1 (trackedColorPairColors pair).2

/-- The executable adjacency row supplied by the existing common Cell/seam
carrier code. -/
def sourceLocalLayerSerialTrackedLocalAdjacencyForColorAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let code := sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData
      minimal caps coloring web corridor hunique offset color
    Fin code.vertexCount.val → Fin code.vertexCount.val → Bool :=
  let code := sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData
    minimal caps coloring web corridor hunique offset color
  fun left right => by
    classical
    exact decide
      (((code.graph (pair, false)) ⊔ (code.graph (pair, true))).Adj left right)

/-- Update the cumulative deletion-stable prefix state by Boolean-ORing the
literal Cell/seam adjacency row into every tracked colour-pair coordinate. -/
noncomputable def
    sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    SourceLocalLayerSerialTrackedDeletionStablePrefixState :=
  let prefixState :=
    sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt graphData
      minimal caps coloring web corridor hunique offset color
  let localCode :=
    sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal caps
      coloring web corridor hunique offset color
  { vertexCount := prefixState.vertexCount
    code := fun pair =>
      addInterfaceAdjacency (prefixState.code pair) (fun left right => by
        classical
        exact decide (((localCode.graph (pair, false)) ⊔
          (localCode.graph (pair, true))).Adj left right)) }

theorem sourceLocalLayerSerialTrackedLocalGraph_support_subset_carrier
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    (sourceLocalLayerSerialTrackedLocalGraphForColorAt caps coloring web corridor
      hunique offset color pair).support ⊆
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset : Set _) := by
  intro edge hedge
  rcases hedge with ⟨neighbor, hedge⟩
  change
    (regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerCellRegionAt corridor hunique offset)
          color (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 ⊔
      sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset color
        (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Adj edge neighbor at hedge
  rw [SimpleGraph.sup_adj] at hedge
  rcases hedge with hcell | hseam
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hcell.2.1)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (sourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
        corridor hunique offset color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 ⟨neighbor, hseam⟩))

theorem sourceLocalLayerSerialTrackedLocalGraph_support_subset_range
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let edgeAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (sourceLocalLayerSerialTrackedLocalGraphForColorAt caps coloring web corridor
      hunique offset color pair).support ⊆ Set.range edgeAt := by
  dsimp only
  intro edge hedge
  let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  have hcarrier : edge ∈ carrier :=
    sourceLocalLayerSerialTrackedLocalGraph_support_subset_carrier graphData
      caps coloring web corridor hunique offset color pair hedge
  refine ⟨carrierCoordinate carrier ⟨edge, hcarrier⟩, ?_⟩
  simp [carrier]

theorem sourceLocalLayerSerialTrackedLocalAdjacency_exact
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (left right : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card) :
    sourceLocalLayerSerialTrackedLocalAdjacencyForColorAt graphData minimal caps
        coloring web corridor hunique offset color pair left right = true ↔
      let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
        caps coloring web corridor hunique offset
      let edgeAt := fun slot : Fin carrier.card =>
        ((carrierCoordinate carrier).symm slot).1
      (sourceLocalLayerSerialTrackedLocalGraphForColorAt caps coloring web
        corridor hunique offset color pair).Adj (edgeAt left) (edgeAt right) := by
  classical
  let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  let localCode := sourceLocalLayerSerialTrackedTransitionCodeForColorAt
    graphData minimal caps coloring web corridor hunique offset color
  let first : {edge // edge ∈ carrier} := (carrierCoordinate carrier).symm left
  let second : {edge // edge ∈ carrier} := (carrierCoordinate carrier).symm right
  have hcellIff :
      (localCode.graph (pair, false)).Adj left right ↔
        (regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerCellRegionAt corridor hunique offset) color
          (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2).Adj first.1 second.1 := by
    have h := boundedCarrierGraphFamilyCode_adj_iff carrier 21 5
      (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        graphData minimal caps coloring web corridor hunique offset)
      (sourceLocalLayerSerialTrackedTransitionPointAt graphData caps coloring
        web corridor hunique offset)
      (fun factor => if factor.2 then
        sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
          color (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
      else regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerCellRegionAt corridor hunique offset) color
        (trackedColorPairColors factor.1).1
          (trackedColorPairColors factor.1).2)
      (pair, false) first second
    simpa [localCode,
      sourceLocalLayerSerialTrackedTransitionCodeForColorAt, first, second]
      using h
  have hseamIff :
      (localCode.graph (pair, true)).Adj left right ↔
        (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
          color (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2).Adj first.1 second.1 := by
    have h := boundedCarrierGraphFamilyCode_adj_iff carrier 21 5
      (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        graphData minimal caps coloring web corridor hunique offset)
      (sourceLocalLayerSerialTrackedTransitionPointAt graphData caps coloring
        web corridor hunique offset)
      (fun factor => if factor.2 then
        sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
          color (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
      else regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerCellRegionAt corridor hunique offset) color
        (trackedColorPairColors factor.1).1
          (trackedColorPairColors factor.1).2)
      (pair, true) first second
    simpa [localCode,
      sourceLocalLayerSerialTrackedTransitionCodeForColorAt, first, second]
      using h
  change decide (((localCode.graph (pair, false)) ⊔
    (localCode.graph (pair, true))).Adj left right) = true ↔ _
  rw [decide_eq_true_eq, SimpleGraph.sup_adj,
    sourceLocalLayerSerialTrackedLocalGraphForColorAt, SimpleGraph.sup_adj]
  exact or_congr hcellIff hseamIff

/-- The cumulative update is the literal exact three-row code, field by
field.  The stronger equality matters at the following boundary rebase,
whose interface change must inspect the three rows separately rather than
only their disjunction. -/
theorem
    sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt_code_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let edgeAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt
        graphData minimal caps coloring web corridor hunique offset color
        ).code pair =
      exactInterfaceExteriorCode
        (regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          color (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
        edgeAt := by
  dsimp only
  let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  let edgeAt := fun slot : Fin carrier.card =>
    ((carrierCoordinate carrier).symm slot).1
  let prefixGraph := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let localGraph := sourceLocalLayerSerialTrackedLocalGraphForColorAt caps
    coloring web corridor hunique offset color pair
  have hupdate := addInterfaceAdjacency_exact_code_eq prefixGraph localGraph
    edgeAt
    (sourceLocalLayerSerialTrackedLocalGraph_support_subset_range graphData caps
      coloring web corridor hunique offset color pair)
    (sourceLocalLayerSerialTrackedLocalAdjacencyForColorAt graphData minimal caps
      coloring web corridor hunique offset color pair)
    (sourceLocalLayerSerialTrackedLocalAdjacency_exact graphData minimal caps
      coloring web corridor hunique offset color pair)
  change addInterfaceAdjacency
      (exactInterfaceExteriorCode prefixGraph edgeAt)
      (sourceLocalLayerSerialTrackedLocalAdjacencyForColorAt graphData minimal
        caps coloring web corridor hunique offset color pair) =
    _
  rw [sourceLocalLayerSerialPreRebaseTrackedGraph_eq_three_factor corridor
    hunique offset color (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2, sup_assoc]
  exact hupdate

/-- Crown recurrence: the updated finite state presents exactly the literal
pre-rebase tracked graph on the common Cell carrier. -/
theorem
    sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt_step_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (left right : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card) :
    InterfaceExteriorFactoredStep
        ((sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt
          graphData minimal caps coloring web corridor hunique offset color
          ).code pair)
        left right ↔
      let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
        caps coloring web corridor hunique offset
      let edgeAt := fun slot : Fin carrier.card =>
        ((carrierCoordinate carrier).symm slot).1
      InterfaceExteriorStep
        (regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          color (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
        edgeAt left right := by
  let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  let edgeAt := fun slot : Fin carrier.card =>
    ((carrierCoordinate carrier).symm slot).1
  let prefixGraph := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let localGraph := sourceLocalLayerSerialTrackedLocalGraphForColorAt caps
    coloring web corridor hunique offset color pair
  have hupdate := addInterfaceAdjacency_exact_step_iff prefixGraph localGraph
    edgeAt
    (sourceLocalLayerSerialTrackedLocalGraph_support_subset_range graphData caps
      coloring web corridor hunique offset color pair)
    (sourceLocalLayerSerialTrackedLocalAdjacencyForColorAt graphData minimal caps
      coloring web corridor hunique offset color pair)
    (sourceLocalLayerSerialTrackedLocalAdjacency_exact graphData minimal caps
      coloring web corridor hunique offset color pair)
    left right
  change InterfaceExteriorFactoredStep
      (addInterfaceAdjacency
        (exactInterfaceExteriorCode prefixGraph edgeAt)
        (sourceLocalLayerSerialTrackedLocalAdjacencyForColorAt graphData minimal
          caps coloring web corridor hunique offset color pair))
      left right ↔ _
  rw [sourceLocalLayerSerialPreRebaseTrackedGraph_eq_three_factor corridor
    hunique offset color (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2, sup_assoc]
  exact hupdate

/-- Every deletion mask is reconstructed from the updated state.  This is the
mask-stable tracked recurrence consumed by the boundary-rebase step. -/
theorem
    sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt_reachable_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (removed : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card → Bool)
    (left right : SurvivingInterfaceSlot
      (fun slot : Fin
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset)).symm slot).1)
      removed) :
    let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let graph := regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let edgeAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (restrictedByMask graph edgeAt removed).Reachable
        (edgeAt left.1) (edgeAt right.1) ↔
      Relation.ReflTransGen
        (fun first second : SurvivingInterfaceSlot edgeAt removed =>
          InterfaceExteriorFactoredStep
            ((sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt
              graphData minimal caps coloring web corridor hunique offset color
              ).code pair)
            first.1 second.1)
        left right := by
  dsimp only
  rw [restrictedByMask_reachable_iff_interfaceExteriorClosure]
  constructor
  · intro hclosure
    exact hclosure.mono fun first second hstep =>
      (sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt_step_iff
        graphData minimal caps coloring web corridor hunique offset color pair
        first.1 second.1).2 hstep
  · intro hclosure
    exact hclosure.mono fun first second hstep =>
      (sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt_step_iff
        graphData minimal caps coloring web corridor hunique offset color pair
        first.1 second.1).1 hstep

end

end GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseState

end Mettapedia.GraphTheory.FourColor
