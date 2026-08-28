import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFacePrefixAttachmentState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapExact

/-!
# Package the selected exact facial target as the next cap-six state

The pointwise-selected Cell--rebase contraction computes the complete
cap-six exterior-label code on the literal next rolling facial carrier.  This
file packages that code in the fixed cumulative-state ABI and proves equality
to the canonical semantic prefix state extracted at the next cut.

Thus the finite transition does not merely preserve facial reachability or a
bounded approximation: it returns the exact next cumulative facial Count
field, without rereading the source graph after the transition.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapState

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCap
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapExact
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceTargetCapStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance pointwiseSelectedFaceTargetCapStateOpenedGraphDecidableRel
    {graphData : Data G}
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The graph-free selected cap-six result of one literal Cell rebase,
packaged in the fixed cumulative facial-state type. -/
noncomputable def
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerSerialFaceDeletionStableCapSixState :=
  let next := sourceLocalLayerNextOffset offset hnext
  let target :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
      web.toFormation corridor hinterior next
  let hcellNext :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData
      minimal caps coloring web corridor hinterior next
  { vertexCount := ⟨target.card, Nat.lt_succ_of_le
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
        web.toFormation corridor hinterior next hcellNext)⟩
    code := fun _ =>
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
        graphData minimal caps coloring web corridor hinterior offset hnext }

/-- The finite selected cap-six rebase result is exactly the cumulative
semantic facial state at the next rolling cut. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt_exact
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let next := sourceLocalLayerNextOffset offset hnext
    let hcellNext :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData
        minimal caps coloring web corridor hinterior next
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt
        graphData minimal caps coloring web corridor hinterior offset hnext =
      pointwiseSelectedSourceLocalLayerSerialFaceDeletionStableParametricCapPrefixAt
        web.toFormation corridor hinterior next hcellNext 6 := by
  classical
  dsimp only
  unfold
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt
    pointwiseSelectedSourceLocalLayerSerialFaceDeletionStableParametricCapPrefixAt
  dsimp only
  congr 1
  funext family
  exact
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_exact
      graphData minimal caps coloring web corridor hinterior offset hnext

end

end GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapState

end Mettapedia.GraphTheory.FourColor
