import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetFullState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedTargetCode

/-!
# Exact complete successor of one literal Cell--rebase step

The finite rebase decoder supplies the next boundary profile.  Independently,
the rolling target recurrences supply the next tracked state, complete facial
state, partial colour table, and cap-six facial factor.  This file assembles
those five outputs in the cumulative-state type and proves that the result is
the literal next source state at the spliced colouring.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformFullSuccessorState

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSupportColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellStateFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapState
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetFullState
open GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedTargetCode
open GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance uniformFullSuccessorStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance uniformFullSuccessorStateOpenedGraphDecidableRel
    {graphData : Data G}
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

private theorem cumulativeState_ext
    (left right : SourceLocalLayerSerialCumulativeState)
    (hinput : left.input = right.input)
    (htracked : left.tracked = right.tracked)
    (hface : left.face = right.face) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem coloredCumulativeState_ext
    (left right : SourceLocalLayerSerialColoredCumulativeState)
    (hinput : left.input = right.input)
    (htracked : left.tracked = right.tracked)
    (hface : left.face = right.face)
    (hcolor : left.colorCode = right.colorCode)
    (hcap : left.faceCapSix = right.faceCapSix) :
    left = right := by
  cases left with
  | mk leftState leftColor leftCap =>
    cases right with
    | mk rightState rightColor rightCap =>
      have hstate : leftState = rightState :=
        cumulativeState_ext leftState rightState hinput htracked hface
      cases hstate
      cases hcolor
      cases hcap
      rfl

/-- Assemble all five finite outputs of a literal Cell followed by its
boundary rebase. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFullSuccessorStateAt
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
    (hnext : offset.val + 1 < blockLength - 3)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) :
    SourceLocalLayerSerialColoredCumulativeState :=
  let hcross : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := fun step => hcell
          (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
            step)
  let factored := sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
    graphData minimal caps coloring web corridor hunique offset cellColor hcross
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      corridor hunique offset hnext cellColor hcell
  let rebase := finiteBoolSupportLetterForColorAt corridor hunique offset hnext
    factored.2.1 splice hrole
  {
    input := rebase.output
    tracked :=
      sourceLocalLayerSerialCellRebaseUniformTrackedTargetStateAt graphData caps
        coloring web corridor hunique offset hnext splice
    face :=
      sourceLocalLayerSerialCellRebaseUniformFaceTargetFullStateAt graphData
        minimal caps coloring web corridor hunique offset hnext
    colorCode :=
      sourceLocalLayerSerialCellRebaseTransportedColorCodeAt graphData minimal
        caps coloring web corridor hunique offset hnext cellColor hcell
    faceCapSix :=
      sourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt graphData
        minimal caps coloring web corridor hunique offset hnext
  }

/-- The assembled finite output is the complete literal next cumulative state,
field for field. -/
theorem sourceLocalLayerSerialCellRebaseUniformFullSuccessorStateAt_exact
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
    (hnext : offset.val + 1 < blockLength - 3)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) :
    sourceLocalLayerSerialCellRebaseUniformFullSuccessorStateAt graphData minimal
        caps coloring web corridor hunique offset hnext cellColor hcell =
      sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt graphData
        minimal caps coloring web corridor hunique offset hnext cellColor
          hcell := by
  let hcross : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := fun step => hcell
          (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
            step)
  let factored := sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
    graphData minimal caps coloring web corridor hunique offset cellColor hcross
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      corridor hunique offset hnext cellColor hcell
  let result := sourceLocalLayerSerialCellRebaseUniformFullSuccessorStateAt
    graphData minimal caps coloring web corridor hunique offset hnext cellColor
      hcell
  let expected := sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt
    graphData minimal caps coloring web corridor hunique offset hnext cellColor
      hcell
  change result = expected
  have hinput : result.input = expected.input := by
    simpa [result, expected, hcross, factored, splice, hrole,
      sourceLocalLayerSerialCellRebaseUniformFullSuccessorStateAt] using
        (finiteBoolSupportLetterForColorAt_output_eq_nextColoredCumulativeState_input
          graphData minimal caps coloring web corridor hunique offset hnext
            cellColor hcell)
  have htracked : result.tracked = expected.tracked := by
    simpa [result, expected, splice,
      sourceLocalLayerSerialCellRebaseUniformFullSuccessorStateAt,
      sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt,
      sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
        (sourceLocalLayerSerialCellRebaseUniformTrackedTargetStateAt_exact
          graphData minimal caps coloring web corridor hunique offset hnext
            splice)
  have hface : result.face = expected.face := by
    simpa [result, expected,
      sourceLocalLayerSerialCellRebaseUniformFullSuccessorStateAt,
      sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt,
      sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
        (sourceLocalLayerSerialCellRebaseUniformFaceTargetFullStateAt_exact
          graphData minimal caps coloring web corridor hunique offset hnext)
  have hcolor : result.colorCode = expected.colorCode := by
    simpa [result, expected,
      sourceLocalLayerSerialCellRebaseUniformFullSuccessorStateAt,
      sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt,
      sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
        (sourceLocalLayerSerialCellRebaseTransportedColorCodeAt_eq_target_unconditional
          graphData minimal caps coloring web corridor hunique offset hnext
            cellColor hcell)
  have hcap : result.faceCapSix = expected.faceCapSix := by
    simpa [result, expected,
      sourceLocalLayerSerialCellRebaseUniformFullSuccessorStateAt,
      sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt,
      sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
        (sourceLocalLayerSerialCellRebaseUniformFaceTargetCapSixStateAt_exact
          graphData minimal caps coloring web corridor hunique offset hnext)
  exact coloredCumulativeState_ext result expected hinput htracked hface hcolor
    hcap

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformFullSuccessorState

end Mettapedia.GraphTheory.FourColor
