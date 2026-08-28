import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedSuccessor

/-!
# Exact finite selected Cell--rebase target

The tracked and facial exterior transitions share one physical Cell factor but
have independent boundary-rebase factors.  This file packages those three
finite objects as one consumer-facing Cell--rebase factor and applies both
guarded transitions together.

On compatible source data the result is exactly the pair of canonical tracked
and facial states at the next cut.  The following rolling-root projection is
intentionally not folded into this type: it consumes this target and supplies
the next lookahead root, while the target equality proved here remains the
stable compositional interface.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedCellRebaseTarget

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor
open GoertzelV24ClosedWebPointwiseSelectedCellNativeFactorization
open GoertzelV24ClosedWebPointwiseSelectedFaceSuccessor
open GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState
open GoertzelV24ClosedWebPointwiseSelectedTrackedRebaseFactor
open GoertzelV24ClosedWebPointwiseSelectedTrackedSuccessor
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedCellRebaseTargetOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The complete finite payload needed to compute both exterior targets of a
selected Cell--rebase step. -/
structure PointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactor where
  outputCount : Fin 5
  localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor outputCount
  trackedRebase : SourceLocalLayerSerialTrackedRebaseFactor
  faceRebase : SourceLocalLayerSerialFaceRebaseFactor

noncomputable instance :
    DecidableEq PointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactor :=
  Classical.decEq _

private abbrev pointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactorCode :=
  Σ outputCount : Fin 5,
    SourceLocalLayerSerialCellPhysicalBoolLocalFactor outputCount ×
      SourceLocalLayerSerialTrackedRebaseFactor ×
        SourceLocalLayerSerialFaceRebaseFactor

private def pointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactorEquiv :
    PointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactor ≃
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactorCode where
  toFun factor := ⟨factor.outputCount, factor.localFactor,
    factor.trackedRebase, factor.faceRebase⟩
  invFun factor := {
    outputCount := factor.1
    localFactor := factor.2.1
    trackedRebase := factor.2.2.1
    faceRebase := factor.2.2.2 }
  left_inv factor := by cases factor; rfl
  right_inv factor := by rcases factor with ⟨_, _, _, _⟩; rfl

set_option synthInstance.maxSize 256 in
deriving noncomputable instance Fintype for
  pointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactorCode

noncomputable instance :
    Fintype PointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactor :=
  Fintype.ofEquiv _
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactorEquiv.symm

/-- Apply the tracked and facial target transitions to their shared rooted
state and physical Cell factor. -/
def PointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactor.successor?
    (factor : PointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactor)
    (state : SourceLocalLayerSerialRootedInteractionState) :
    Option
      (SourceLocalLayerSerialTrackedDeletionStablePrefixState ×
        SourceLocalLayerSerialFaceDeletionStableCapSixState) :=
  (sourceLocalLayerSerialRootedInteractionTrackedSuccessorState? state
    factor.localFactor factor.trackedRebase).bind fun tracked =>
  (sourceLocalLayerSerialRootedInteractionFaceSuccessorState? state
    factor.localFactor factor.faceRebase).map fun face => (tracked, face)

/-- Literal finite target factor extracted from an arbitrary prefix and one
positive selected Cell. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactorAt
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
    PointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactor := by
  let factored :=
    pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
      corridor hinterior offset hnext hcell prefixColor hprefix cellColoring
  let color :=
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
      corridor hinterior offset prefixColor
        (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
          corridor hinterior offset cellColoring)
  let next := sourceLocalLayerNextOffset offset hnext
  let hcellNext :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
      caps coloring web corridor hinterior next
  exact {
    outputCount := factored.2.1.faceFragmentCount
    localFactor := factored.2.2
    trackedRebase :=
      pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt web corridor
        hinterior offset hnext hcell hcellNext color
    faceRebase :=
      pointwiseSelectedSourceLocalLayerSerialFaceRebaseFactorAt graphData minimal
        caps coloring web corridor hinterior offset hnext hcell }

/-- The complete selected finite target factor returns both canonical next-cut
exterior states exactly. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactorAt_successor_exact
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
    let factor :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactorAt graphData
        minimal caps coloring web corridor hinterior offset hnext hcell
          prefixColor hprefix cellColoring
    let color :=
      pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
        corridor hinterior offset prefixColor
          (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
            corridor hinterior offset cellColoring)
    let next := sourceLocalLayerNextOffset offset hnext
    let hcellNext :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
        caps coloring web corridor hinterior next
    factor.successor? state =
      some
        (pointwiseSelectedSourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
            web corridor hinterior next hcellNext color,
          pointwiseSelectedSourceLocalLayerSerialFaceDeletionStableParametricCapPrefixAt
            web.toFormation corridor hinterior next hcellNext 6) := by
  classical
  dsimp only
  rw [PointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactor.successor?]
  simp only [pointwiseSelectedSourceLocalLayerSerialCellRebaseTargetFactorAt]
  rw [pointwiseSelectedSourceLocalLayerSerialRootedInteractionTrackedSuccessorState?_at
    graphData minimal caps coloring web corridor hinterior offset hnext hcell
      prefixColor hprefix cellColoring hcompatible]
  simp only [Option.bind_some]
  rw [pointwiseSelectedSourceLocalLayerSerialRootedInteractionFaceSuccessorState?_at
    graphData minimal caps coloring web corridor hinterior offset hnext hcell
      prefixColor hprefix cellColoring]
  rfl

end


end GoertzelV24ClosedWebPointwiseSelectedCellRebaseTarget

end Mettapedia.GraphTheory.FourColor
