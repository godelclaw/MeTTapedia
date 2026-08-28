import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedPreRebaseExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedTargetCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier

/-!
# Exact selected tracked Cell--rebase successor

The graph-free tracked transition first adjoins the positive literal Cell and
its terminal seam on the complete interaction carrier, then masks the retired
switch, adjoins the boundary-rebase residue, and contracts onto the next
rolling carrier.  The two exactness halves have already been proved
separately.  This file composes them on the corrected pointwise-selected
geometry.

For every compatible arbitrary cumulative prefix and positive literal Cell,
the guarded finite transition succeeds and returns the canonical selected
tracked exterior state at the next cut.  Thus this is an equality of the full
three-row exterior code, not a one-way source simulation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedTrackedSuccessor

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor
open GoertzelV24ClosedWebPointwiseSelectedCellNativeFactorization
open GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState
open GoertzelV24ClosedWebPointwiseSelectedTrackedPreRebaseExact
open GoertzelV24ClosedWebPointwiseSelectedTrackedRebaseFactor
open GoertzelV24ClosedWebPointwiseSelectedTrackedTargetCode
open GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedTrackedSuccessorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance pointwiseSelectedTrackedSuccessorOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-! ## Canonical selected target state -/

/-- Exact selected tracked exterior state on an arbitrary rolling cut. -/
noncomputable def
    pointwiseSelectedSourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color) :
    SourceLocalLayerSerialTrackedDeletionStablePrefixState :=
  let target :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior offset
  boundedInterfaceExteriorFamilyCode target 21
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      web corridor hinterior offset hcell)
    (fun pair => regionalTrackedEdgeGraph web.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2)

/-- The tracked exterior field of the selected rooted semantic state is the
canonical selected state just defined. -/
@[simp]
theorem
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_trackedExterior
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
      ).trackedExterior =
      pointwiseSelectedSourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
        web corridor hinterior offset hcell color := by
  rfl

/-! ## Exact finite successor -/

/-- Applying the selected finite target contraction to its exact interaction
state returns the canonical tracked state at the next rolling cut. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedRebaseTargetStateAt_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        web corridor hinterior offset hnext hcell color
    let factor :=
      pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt web corridor
        hinterior offset hnext hcell hcellNext color
    factor.targetState preRebase (by rfl) =
      pointwiseSelectedSourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
        web corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hcellNext color := by
  dsimp only
  unfold SourceLocalLayerSerialTrackedRebaseFactor.targetState
    pointwiseSelectedSourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
  rw [BoundedInterfaceExteriorFamilyCode.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  funext pair
  change
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt
        web corridor hinterior offset hnext color pair = _
  rw [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt_exact
    graphData minimal caps coloring web corridor hinterior offset hnext color
      pair]
  rfl

/-- On every compatible arbitrary cumulative prefix and positive selected
literal Cell, the complete graph-free tracked transition succeeds and returns
exactly the next canonical selected tracked state. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionTrackedSuccessorState?_at
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        web.toFormation corridor hinterior offset prefixColor
          (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
            corridor hinterior offset cellColoring)) :
    let state :=
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
    let localFactor :=
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2
    let color :=
      pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
        corridor hinterior offset prefixColor
          (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
            corridor hinterior offset cellColoring)
    let next := sourceLocalLayerNextOffset offset hnext
    let hcellNext :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
        caps coloring web corridor hinterior next
    let rebaseFactor :=
      pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt web corridor
        hinterior offset hnext hcell hcellNext color
    sourceLocalLayerSerialRootedInteractionTrackedSuccessorState? state
        localFactor rebaseFactor =
      some
        (pointwiseSelectedSourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
          web corridor hinterior next hcellNext color) := by
  dsimp only
  rw [sourceLocalLayerSerialRootedInteractionTrackedSuccessorState?]
  rw [pointwiseSelectedSourceLocalLayerSerialRootedInteractionPreRebaseState?_at
    web corridor hinterior offset hnext hcell prefixColor hprefix cellColoring
      hcompatible]
  simp only [Option.bind_some]
  unfold SourceLocalLayerSerialTrackedRebaseFactor.targetState?
  split <;> rename_i hcount
  · congr 1
    exact
      pointwiseSelectedSourceLocalLayerSerialTrackedRebaseTargetStateAt_eq
        graphData minimal caps coloring web corridor hinterior offset hnext
          hcell
          (pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData
            minimal caps coloring web corridor hinterior
              (sourceLocalLayerNextOffset offset hnext))
          (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
            web.toFormation corridor hinterior offset prefixColor
              (pointwiseSelectedSourceLocalLayerCellLiteralColorAt
                web.toFormation corridor hinterior offset cellColoring))
  · exfalso
    apply hcount
    rfl

end

end GoertzelV24ClosedWebPointwiseSelectedTrackedSuccessor

end Mettapedia.GraphTheory.FourColor
