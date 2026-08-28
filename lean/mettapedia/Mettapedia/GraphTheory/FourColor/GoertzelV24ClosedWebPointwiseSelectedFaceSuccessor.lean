import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFacePreRebaseExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapState

/-!
# Exact selected facial Cell--rebase successor

The source-independent facial rebase ABI masks retired interaction darts,
adjoins the literal next collar, and contracts onto the next rolling carrier.
This file instantiates that finite ABI on the corrected pointwise-selected
corridor geometry.  For every compatible arbitrary cumulative prefix and
positive literal Cell, the complete guarded facial transition succeeds and
returns the canonical selected cap-six state at the next cut.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceSuccessor

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceSuccessor
open GoertzelV24ClosedWebPointwiseSelectedCellFiniteSupportLetter
open GoertzelV24ClosedWebPointwiseSelectedCellNativeFactorization
open GoertzelV24ClosedWebPointwiseSelectedFacePreRebaseExact
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCap
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapExact
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapState
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCode
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetIncidence
open GoertzelV24ClosedWebPointwiseSelectedFaceUniformRecurrence
open GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceSuccessorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance pointwiseSelectedFaceSuccessorOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-! ## Literal selected rebase factor -/

/-- Literal finite facial rebase factor on the complete selected interaction
carrier.  Its rows depend only on the Cell, the boundary-rebase collar, and the
finite target contraction. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceRebaseFactorAt
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
      corridor hinterior offset).card ≤ 6) :
    SourceLocalLayerSerialFaceRebaseFactor := by
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      web.toFormation corridor hinterior offset hnext
  let dartAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
  let localGraph :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseLocalFaceGraphAt
      web.toFormation corridor hinterior offset hnext
  let next := sourceLocalLayerNextOffset offset hnext
  let nextRegion :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation
      corridor hinterior next
  let target :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
      web.toFormation corridor hinterior next
  have hinteraction : interaction.card ≤ 48 :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight
      web.toFormation corridor hinterior offset hnext hcell
  have hcellNext :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
      caps coloring web corridor hinterior next
  have htarget : target.card ≤ 24 :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
      web.toFormation corridor hinterior next hcellNext
  exact {
    interactionCount := ⟨interaction.card, Nat.lt_succ_of_le hinteraction⟩
    targetCount := ⟨target.card, Nat.lt_succ_of_le htarget⟩
    switchMask :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
        web.toFormation corridor hinterior offset hnext
    localAdjacency := fun left right => by
      classical
      exact decide (localGraph.Adj (dartAt left) (dartAt right))
    localPresent := fun slot => by
      classical
      exact decide (web.annular.RS.edgeOf (dartAt slot) ∈ nextRegion)
    targetSource :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
        web.toFormation corridor hinterior offset hnext
    targetPresent :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt
        corridor hinterior offset hnext
    targetEntry :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt
        graphData minimal caps coloring web corridor hinterior offset hnext }

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialFaceRebaseFactorAt_interactionCount
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
      corridor hinterior offset).card ≤ 6) :
    (pointwiseSelectedSourceLocalLayerSerialFaceRebaseFactorAt graphData minimal
      caps coloring web corridor hinterior offset hnext hcell
      ).interactionCount.val =
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext).card := by
  rfl

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialFaceRebaseFactorAt_targetCount
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
      corridor hinterior offset).card ≤ 6) :
    (pointwiseSelectedSourceLocalLayerSerialFaceRebaseFactorAt graphData minimal
      caps coloring web corridor hinterior offset hnext hcell).targetCount.val =
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card := by
  rfl

/-! ## Exact finite successor -/

/-- The literal selected finite factor computes exactly the uniform cap-six
successor code. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRebaseUniformSuccessorAt_eq
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
      corridor hinterior offset).card ≤ 6) :
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
        web.toFormation corridor hinterior offset hnext hcell
    let factor :=
      pointwiseSelectedSourceLocalLayerSerialFaceRebaseFactorAt graphData minimal
        caps coloring web corridor hinterior offset hnext hcell
    factor.uniformSuccessorCode preRebase (by rfl) =
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
        web.toFormation corridor hinterior offset hnext := by
  classical
  rfl

/-- The selected target contraction agrees row-for-row with the exact target
cap code. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRebaseTargetStateAt_code_eq
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
      corridor hinterior offset).card ≤ 6) :
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
        web.toFormation corridor hinterior offset hnext hcell
    let factor :=
      pointwiseSelectedSourceLocalLayerSerialFaceRebaseFactorAt graphData minimal
        caps coloring web corridor hinterior offset hnext hcell
    (factor.targetState preRebase (by rfl)).code () =
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
        graphData minimal caps coloring web corridor hinterior offset hnext := by
  dsimp only
  unfold SourceLocalLayerSerialFaceRebaseFactor.targetState
  dsimp only
  rw [pointwiseSelectedSourceLocalLayerSerialFaceRebaseUniformSuccessorAt_eq
    graphData minimal caps coloring web corridor hinterior offset hnext hcell]
  rfl

/-- The finite selected facial factor returns the canonical cumulative
cap-six state at the next rolling cut. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRebaseTargetStateAt_eq
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
      corridor hinterior offset).card ≤ 6) :
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
        web.toFormation corridor hinterior offset hnext hcell
    let factor :=
      pointwiseSelectedSourceLocalLayerSerialFaceRebaseFactorAt graphData minimal
        caps coloring web corridor hinterior offset hnext hcell
    let next := sourceLocalLayerNextOffset offset hnext
    let hcellNext :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
        caps coloring web corridor hinterior next
    factor.targetState preRebase (by rfl) =
      pointwiseSelectedSourceLocalLayerSerialFaceDeletionStableParametricCapPrefixAt
        web.toFormation corridor hinterior next hcellNext 6 := by
  dsimp only
  calc
    _ =
        pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt
          graphData minimal caps coloring web corridor hinterior offset hnext := by
      unfold SourceLocalLayerSerialFaceRebaseFactor.targetState
        pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt
      dsimp only
      congr 1
    _ = _ :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt_exact
        graphData minimal caps coloring web corridor hinterior offset hnext

/-- On every compatible arbitrary prefix and positive selected literal Cell,
the complete graph-free facial transition succeeds and returns exactly the
next canonical cumulative cap-six state. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionFaceSuccessorState?_at
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
        web.toFormation corridor hinterior offset) :
    let state :=
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web.toFormation corridor hinterior offset hnext hcell prefixColor hprefix
    let localFactor :=
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2
    let rebaseFactor :=
      pointwiseSelectedSourceLocalLayerSerialFaceRebaseFactorAt graphData minimal
        caps coloring web corridor hinterior offset hnext hcell
    let next := sourceLocalLayerNextOffset offset hnext
    let hcellNext :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
        caps coloring web corridor hinterior next
    sourceLocalLayerSerialRootedInteractionFaceSuccessorState? state localFactor
        rebaseFactor =
      some
        (pointwiseSelectedSourceLocalLayerSerialFaceDeletionStableParametricCapPrefixAt
          web.toFormation corridor hinterior next hcellNext 6) := by
  dsimp only
  rw [sourceLocalLayerSerialRootedInteractionFaceSuccessorState?]
  rw [pointwiseSelectedSourceLocalLayerSerialRootedInteractionFacePreRebaseState?_at
    web corridor hinterior offset hnext hcell prefixColor hprefix cellColoring]
  simp only [Option.bind_some]
  unfold SourceLocalLayerSerialFaceRebaseFactor.targetState?
  split <;> rename_i hcount
  · congr 1
    exact
      pointwiseSelectedSourceLocalLayerSerialFaceRebaseTargetStateAt_eq graphData
        minimal caps coloring web corridor hinterior offset hnext hcell
  · exfalso
    apply hcount
    rfl

end

end GoertzelV24ClosedWebPointwiseSelectedFaceSuccessor

end Mettapedia.GraphTheory.FourColor
