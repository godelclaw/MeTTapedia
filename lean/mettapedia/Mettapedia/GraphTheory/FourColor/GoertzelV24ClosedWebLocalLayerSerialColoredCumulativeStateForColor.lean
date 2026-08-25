import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExecutableFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialTrackedPrefixAttachmentColorParametric

/-!
# Colour-parametric cumulative source states

One alternating source letter ends after its boundary rebase, at the next
terminal-aware cut.  Its colouring is the compatible prefix/Cell splice, not
necessarily the ambient web colouring used to name the corridor.  This file
packages the next cut profile, tracked prefix attachments, facial prefix
attachments, and partial carrier colours in the same finite cumulative-state
type used at the input.

The rebase's decoded output profile is proved to be literally the input-profile
field of this next state.  The remaining Phase-5 obligation is stronger: derive
the other three target-state fields by a finite recurrence from the predecessor
state and local factor.  They are extracted source-exactly here so that that
recurrence now has a precise codomain.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSupportColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialTrackedPrefixAttachmentColorParametric
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorSkeleton
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance coloredCumulativeStateForColorOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The complete cumulative finite state at one terminal-aware cut, evaluated
at an arbitrary colour function. -/
noncomputable def sourceLocalLayerSerialColoredCumulativeStateForColorAt
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
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    SourceLocalLayerSerialColoredCumulativeState :=
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique offset
  {
    input := terminalInputBoundedProfileForColorAt corridor hunique offset color
      hcrossing
    tracked := sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
      graphData caps coloring web corridor hunique offset color
    face := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique
      offset hcell
    colorCode := sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring
      web corridor hunique offset
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) color
  }

/-- At the ambient colouring this is exactly the cumulative state extracted by
the physical Cell factor, independently of the chosen local Cell colouring. -/
theorem sourceLocalLayerSerialColoredCumulativeStateForColorAt_ambient_eq_factored_input
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    sourceLocalLayerSerialColoredCumulativeStateForColorAt graphData minimal
        caps coloring web corridor hunique offset coloring (fun _ => web.tait _) =
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellColor).1 := by
  rfl

/-- The complete cumulative source state immediately after the Cell's boundary
rebase, evaluated at the literal spliced colouring. -/
noncomputable def sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt
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
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      corridor hunique offset hnext cellColor hcell
  sourceLocalLayerSerialColoredCumulativeStateForColorAt graphData minimal caps
    coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
      splice
      (successorCrossingNonzeroForColorAt corridor hunique offset hnext splice
        hrole)

/-- The rebase decoder's successor profile is literally the input-profile field
of the next colour-parametric cumulative state. -/
theorem finiteBoolSupportLetterForColorAt_output_eq_nextColoredCumulativeState_input
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
    (finiteBoolSupportLetterForColorAt corridor hunique offset hnext factored.2.1
      splice hrole).output =
      (sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt graphData
        minimal caps coloring web corridor hunique offset hnext cellColor
          hcell).input := by
  rfl

end


end GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor

end Mettapedia.GraphTheory.FourColor
