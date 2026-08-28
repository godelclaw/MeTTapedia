import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellRebaseInteractionCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedPrefixAttachmentState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFacePrefixAttachmentState

/-!
# Pointwise-selected semantic roots for the finite rolling machine

The finite rooted interaction state and its graph-free transition do not
depend on how a corridor Cell is selected.  Their historical source
constructor did: it used a global unique-shared-edge selector which is not
available in the corrected route.

This file supplies the missing semantic map from the pointwise-selected
geometry.  An arbitrary cumulative-prefix colour function is compressed on
the selected current carriers and on the complete forty-nine-edge and
forty-eight-dart Cell--rebase interaction carriers.  The result inhabits the
existing finite rooted-state ABI, so the already audited graph-free rolling
machine can be reused without importing the invalid geometric premise into
its semantics.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellStateFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24CorridorProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedRootedInteractionStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Extract the exact finite rooted state of an arbitrary cumulative-prefix
colour function on the corrected pointwise-selected Cell geometry. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0) :
    SourceLocalLayerSerialRootedInteractionState := by
  let region :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation
      corridor hinterior offset
  let current :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior offset
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web corridor hinterior offset hnext
  let faceCurrent :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
      web.toFormation corridor hinterior offset
  let faceInteraction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      web.toFormation corridor hinterior offset hnext
  let hcurrent : current.card ≤ 21 :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      web corridor hinterior offset hcell
  let hinteraction : interaction.card ≤ 49 :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      web corridor hinterior offset hnext hcell
  let hfaceCurrent : faceCurrent.card ≤ 24 :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
      web.toFormation corridor hinterior offset hcell
  let hfaceInteraction : faceInteraction.card ≤ 48 :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight
      web.toFormation corridor hinterior offset hnext hcell
  let input :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
      web.toFormation corridor hinterior offset color hcrossing
  let tracked :=
    pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
      web corridor hinterior offset color
  let face :=
    pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
      web.toFormation corridor hinterior offset hcell
  let colorCode :=
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
      corridor hinterior offset region color
  let faceCapSix : SourceLocalLayerSerialFaceDeletionStableCapSixState := {
    vertexCount := ⟨faceCurrent.card, Nat.lt_succ_of_le hfaceCurrent⟩
    code := fun _ => exactFaceInterfaceExteriorLabelCapCode web.annular.RS
      region (fun slot : Fin faceCurrent.card =>
        ((carrierCoordinate faceCurrent).symm slot).1) 6 }
  let trackedExterior : SourceLocalLayerSerialTrackedDeletionStablePrefixState :=
    boundedInterfaceExteriorFamilyCode current 21 hcurrent fun pair =>
      regionalTrackedEdgeGraph web.annular.RS region color
        (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let rooted : SourceLocalLayerSerialRootedCumulativeState := {
    toSourceLocalLayerSerialColoredCumulativeState := {
      toSourceLocalLayerSerialCumulativeState := {
        input := input
        tracked := tracked
        face := face }
      colorCode := colorCode
      faceCapSix := faceCapSix }
    trackedExterior := trackedExterior }
  let interactionExterior : SourceLocalLayerSerialTrackedInteractionPrefixState :=
    boundedInterfaceExteriorFamilyCode interaction 49 hinteraction fun pair =>
      regionalTrackedEdgeGraph web.annular.RS region color
        (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let interactionColorCode :=
    sourceLocalLayerSerialTrackedInteractionColorCodeAt interaction hinteraction
      region color
  let faceInteractionExterior :
      SourceLocalLayerSerialFaceInteractionPrefixState := {
    vertexCount := ⟨faceInteraction.card,
      Nat.lt_succ_of_le hfaceInteraction⟩
    code := fun _ => exactFaceInterfaceExteriorLabelCapCode web.annular.RS
      region (fun slot : Fin faceInteraction.card =>
        ((carrierCoordinate faceInteraction).symm slot).1) 6 }
  exact {
    toSourceLocalLayerSerialRootedCumulativeState := rooted
    interactionExterior := interactionExterior
    interactionColorCode := interactionColorCode
    currentCoordinate := fun slot =>
      carrierCoordinate interaction
        ⟨((carrierCoordinate current).symm slot).1,
          pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_subset_interaction
            web corridor hinterior offset hnext
              ((carrierCoordinate current).symm slot).2⟩
    faceInteractionExterior := faceInteractionExterior
    faceCurrentCoordinate := fun slot =>
      carrierCoordinate faceInteraction
        ⟨((carrierCoordinate faceCurrent).symm slot).1,
          pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_subset_interaction
            web.toFormation corridor hinterior offset hnext
              ((carrierCoordinate faceCurrent).symm slot).2⟩ }

/-- The rooted state exposes the exact terminal-aware source profile supplied
by the arbitrary prefix colour function. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_input
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0) :
    (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
      web corridor hinterior offset hnext hcell color hcrossing).input =
      pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
        web.toFormation corridor hinterior offset color hcrossing := by
  rfl

/-- The rooted tracked predecessor field is the exact selected prefix
attachment factor. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_tracked
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0) :
    (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
      web corridor hinterior offset hnext hcell color hcrossing).tracked =
      pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
        web corridor hinterior offset color := by
  rfl

/-- The rooted facial predecessor field is the exact selected prefix
attachment and cap factor. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_face
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0) :
    (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
      web corridor hinterior offset hnext hcell color hcrossing).face =
      pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
        web.toFormation corridor hinterior offset hcell := by
  rfl

/-- The rooted current colour table is the literal selected carrier table of
the arbitrary prefix. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_colorCode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0) :
    (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
      web corridor hinterior offset hnext hcell color hcrossing).colorCode =
      pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            web.toFormation corridor hinterior offset) color := by
  rfl

/-- The selected current tracked exterior factor stores the literal carrier
cardinality. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_trackedExteriorCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0) :
    (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
      web corridor hinterior offset hnext hcell color hcrossing
      ).trackedExterior.vertexCount.val =
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset).card := by
  rfl

/-- The selected current facial exterior factor stores the literal carrier
cardinality. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_faceCapSixCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0) :
    (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
      web corridor hinterior offset hnext hcell color hcrossing
      ).faceCapSix.vertexCount.val =
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior offset).card := by
  rfl

/-- The selected root stores the literal cardinality of its tracked
interaction carrier. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_interactionCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0) :
    (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
      web corridor hinterior offset hnext hcell color hcrossing
      ).interactionExterior.vertexCount.val =
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext).card := by
  rfl

/-- The selected root stores the literal cardinality of its facial
interaction carrier. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_faceInteractionCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0) :
    (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
      web corridor hinterior offset hnext hcell color hcrossing
      ).faceInteractionExterior.vertexCount.val =
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext).card := by
  rfl

/-- The stored tracked-coordinate inclusion names the same ambient edge in
the current and interaction carriers. -/
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_currentEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0)
    (slot : Fin
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset).card) :
    let state :=
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell color hcrossing
    let current :=
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset
    let interaction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext
    ((carrierCoordinate interaction).symm (state.currentCoordinate slot)).1 =
      ((carrierCoordinate current).symm slot).1 := by
  dsimp only
    [pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt]
  rw [Equiv.symm_apply_apply]

/-- The stored facial-coordinate inclusion names the same ambient dart in
the current and interaction carriers. -/
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_faceCurrentDart
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0)
    (slot : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior offset).card) :
    let state :=
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell color hcrossing
    let current :=
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior offset
    let interaction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext
    ((carrierCoordinate interaction).symm
        (state.faceCurrentCoordinate slot)).1 =
      ((carrierCoordinate current).symm slot).1 := by
  dsimp only
    [pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt]
  rw [Equiv.symm_apply_apply]

/-- Every live selected interaction coordinate reads back the exact regional
prefix colour. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_interactionColor_live
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior offset step) ≠ 0)
    (slot : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext).card) :
    let interaction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext
    let region :=
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation
        corridor hinterior offset
    (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
      web corridor hinterior offset hnext hcell color hcrossing
      ).interactionColorCode
        (Fin.castLE
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
            web corridor hinterior offset hnext hcell) slot) =
      if ((carrierCoordinate interaction).symm slot).1 ∈ region then
        some (color ((carrierCoordinate interaction).symm slot).1)
      else none := by
  apply sourceLocalLayerSerialTrackedInteractionColorCodeAt_live

end

end GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState

end Mettapedia.GraphTheory.FourColor
