import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence

/-!
# Finite tracked rebase factor for the pointwise-selected Cell

The graph-free rolling ABI already stores a tracked rebase as a deletion mask,
a local adjacency table, and a partial coordinate map into the next rolling
carrier.  This file supplies that ABI from the corrected pointwise-selected
geometry.

The construction is intentionally split before target contraction.  On the
complete interaction carrier, applying the finite factor to the exact
pre-rebase state is proved rowwise equal to the literal successor graph.  The
only fact still needed to contract to the next rolling carrier is the precise
geometric statement that an unmapped next coordinate is isolated.  Keeping
that premise visible prevents the historical global selector from returning
through an opaque target-projection theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedTrackedRebaseFactor

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor
open GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence
open GoertzelV24CorridorProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedTrackedRebaseFactorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! ## Literal carriers and partial coordinate map -/

/-- Partial coordinate map from the selected next rolling carrier into the
complete selected Cell--rebase interaction carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let target :=
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)
    let interaction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext
    Fin target.card → Option (Fin interaction.card) := by
  classical
  dsimp only
  let target :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web corridor hinterior offset hnext
  intro targetSlot
  let edge := ((carrierCoordinate target).symm targetSlot).1
  if hedge : edge ∈ interaction then
    exact some (carrierCoordinate interaction ⟨edge, hedge⟩)
  else
    exact none

/-- Every mapped target coordinate and interaction coordinate name the same
ambient edge. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt_edge_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (targetSlot : Fin
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card)
    (interactionSlot : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext).card)
    (hsource :
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt
        web corridor hinterior offset hnext targetSlot =
          some interactionSlot) :
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
        corridor hinterior offset hnext interactionSlot =
      (((carrierCoordinate
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext))).symm targetSlot).1) := by
  classical
  simp only
    [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt,
      id_eq] at hsource
  split at hsource <;> rename_i hedge
  · simp only [Option.some.injEq] at hsource
    subst interactionSlot
    simp
      [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt]
  · cases hsource

/-! ## Exact source state and finite factor -/

/-- Exact selected pre-rebase exterior state on the complete interaction
carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color) :
    SourceLocalLayerSerialTrackedInteractionPrefixState :=
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web corridor hinterior offset hnext
  boundedInterfaceExteriorFamilyCode interaction 49
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      web corridor hinterior offset hnext hcell)
    (fun pair => pointwiseSelectedPreRebaseTrackedGraphForColorAt web.toFormation
      corridor hinterior offset color pair)

/-- Literal finite rebase factor for the corrected selected geometry. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color : G.edgeSet → Color) :
    SourceLocalLayerSerialTrackedRebaseFactor := by
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web corridor hinterior offset hnext
  let target :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)
  let hinteraction : interaction.card ≤ 49 :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      web corridor hinterior offset hnext hcell
  let htarget : target.card ≤ 21 :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      web corridor hinterior (sourceLocalLayerNextOffset offset hnext) hcellNext
  exact {
    interactionCount := ⟨interaction.card, Nat.lt_succ_of_le hinteraction⟩
    targetCount := ⟨target.card, Nat.lt_succ_of_le htarget⟩
    switchMask :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformSwitchMaskAt web
        corridor hinterior offset hnext
    localAdjacency := fun pair left right => by
      classical
      exact decide
        ((pointwiseSelectedLocalTrackedGraphForColorAt web corridor hinterior
          offset hnext color pair).Adj
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
            web corridor hinterior offset hnext left)
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
            web corridor hinterior offset hnext right))
    targetSource :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt
        web corridor hinterior offset hnext }

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt_interactionCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color : G.edgeSet → Color) :
    (pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt web corridor
      hinterior offset hnext hcell hcellNext color).interactionCount.val =
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext).card := by
  rfl

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt_targetCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color : G.edgeSet → Color) :
    (pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt web corridor
      hinterior offset hnext hcell hcellNext color).targetCount.val =
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card := by
  rfl

/-- The finite factor computes the exact selected successor code on the full
interaction carrier, before target forgetting. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt_uniformSuccessorCode_exact
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        web corridor hinterior offset hnext hcell color
    let factor :=
      pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt web corridor
        hinterior offset hnext hcell hcellNext color
    let edgeAt :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
        corridor hinterior offset hnext
    factor.uniformSuccessorCode preRebase (by rfl) pair =
      exactInterfaceExteriorCode
        (pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation
          corridor hinterior offset hnext color pair) edgeAt := by
  dsimp only
  change
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
        web corridor hinterior offset hnext color pair = _
  exact
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedSuccessorCodeAt_exact
      web corridor hinterior offset hnext color pair

/-- Executable target code obtained by the graph-free partial contraction.
Its literal exactness is deliberately postponed to the isolated-coordinate
theorem. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    BoundedInterfaceExteriorCode
      (Fin
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext)).card) :=
  partialContractedInterfaceExteriorCode
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
      web corridor hinterior offset hnext color pair)
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt
      web corridor hinterior offset hnext)

end

end GoertzelV24ClosedWebPointwiseSelectedTrackedRebaseFactor

end Mettapedia.GraphTheory.FourColor
