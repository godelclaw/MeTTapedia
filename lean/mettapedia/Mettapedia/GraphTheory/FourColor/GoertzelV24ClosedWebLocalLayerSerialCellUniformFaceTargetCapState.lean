import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState

/-!
# Package the exact rolling face target as the next cumulative cap-six state

The executable Cell--rebase contraction already produces the complete
five-field cap-six code on the literal next rolling carrier.  This file puts
that code in the same fixed bounded-family type used by cumulative prefix
states and proves that the result is exactly the semantic next prefix state.

This is a one-step state identity.  It does not enumerate the finite carrier,
compute a reachable closure, or assert a numerical threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapState

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapExact
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance uniformFaceTargetCapStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance uniformFaceTargetCapStateOpenedGraphDecidableRel
    {graphData : Data G}
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The graph-free cap-six result of one literal Cell rebase, packaged in the
same bounded-family type as the next cumulative prefix state. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt
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
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerSerialFaceDeletionStableCapSixState :=
  let next := sourceLocalLayerNextOffset offset hnext
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    next
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique next
  { vertexCount := ⟨target.card, Nat.lt_succ_of_le
      (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
        corridor hunique next hcell)⟩
    code := fun _ =>
      sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
        graphData minimal caps coloring web corridor hunique offset hnext }

/-- The finite cap-six rebase result is exactly the source-extracted
cumulative facial state at the next rolling cut. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt_exact
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
    (hnext : offset.val + 1 < blockLength - 3) :
    let next := sourceLocalLayerNextOffset offset hnext
    let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
      coloring web corridor hunique next
    sourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt graphData
        minimal caps coloring web corridor hunique offset hnext =
      sourceLocalLayerSerialFaceDeletionStableParametricCapPrefixAt corridor
        hunique next hcell 6 := by
  classical
  dsimp only
  unfold sourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt
    sourceLocalLayerSerialFaceDeletionStableParametricCapPrefixAt
  dsimp only
  congr 1
  funext family
  exact
    sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_exact
      graphData minimal caps coloring web corridor hunique offset hnext

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapState

end Mettapedia.GraphTheory.FourColor
