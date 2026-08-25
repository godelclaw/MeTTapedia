import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport

/-!
# Stable facial successor fields on the rolling carrier

The exact uniform facial recurrence has already been contracted to the next
rolling dart carrier.  This file begins assembling the canonical fixed facial
state.  Its supported-residual fields come from the exact exterior code.  Its
literal-presence field is computed from the independently transported partial
edge-colour table: a represented dart is present exactly when the colour table
contains its underlying edge.

This separation is essential for isolated regional darts.  Graph support alone
cannot distinguish an isolated present dart from an absent padded coordinate.
The capped component-size field remains a separate recurrence below this layer.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetState

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FramedTrail
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance uniformFaceTargetStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance uniformFaceTargetStateOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The edge below a next-carrier facial dart, represented in the next rolling
tracked carrier. -/
noncomputable def sourceLocalLayerSerialFaceTargetTrackedEdgeAt
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
    (dart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    {edge // edge ∈ sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset} :=
  ⟨web.annular.RS.edgeOf dart.1,
    sourceLocalLayerSerialFaceTransitionCarrierAt_edgeOf_mem_tracked graphData
      caps coloring web corridor hunique offset dart.1 dart.2⟩

/-- Compute literal presence of every stable facial slot from a partial colour
table on the next tracked carrier.  Padding decodes to `false`; a represented
dart is present exactly when the table contains its underlying edge. -/
noncomputable def sourceLocalLayerSerialFaceTargetPresentAt
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
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (targetColor : SourceLocalLayerSerialCarrierColorCode) :
    Fin 24 → Bool :=
  fun slot =>
    match sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique
        offset hcell slot with
    | none => false
    | some dart =>
        (targetColor
          (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
            coloring web corridor hunique offset
            (sourceLocalLayerSerialFaceTargetTrackedEdgeAt graphData caps
              coloring web corridor hunique offset dart))).isSome

/-- At a literal regional colour table, the finite presence decoder is exactly
the canonical facial state's `interfacePresent` field. -/
theorem sourceLocalLayerSerialFaceTargetPresentAt_exact
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
    let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
      coloring web corridor hunique offset
    sourceLocalLayerSerialFaceTargetPresentAt graphData minimal caps coloring web
        corridor hunique offset hcell
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          color) =
      (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique offset
        hcell).interfacePresent := by
  classical
  dsimp only
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique offset
  funext slot
  cases hdecode : sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor
      hunique offset hcell slot with
  | none =>
      simp [sourceLocalLayerSerialFaceTargetPresentAt,
        sourceLocalLayerSerialFacePrefixAttachmentStateAt,
        padCappedSupportedPortResidualCodePorts,
        padCappedSupportedPortResidualCode, hdecode]
  | some dart =>
      simp [sourceLocalLayerSerialFaceTargetPresentAt, hdecode,
        sourceLocalLayerSerialFacePrefixAttachmentStateAt,
        sourceLocalLayerSerialFacePrefixAttachmentCodeAt,
        sourceLocalLayerSerialFaceTargetTrackedEdgeAt,
        sourceLocalLayerSerialCarrierColorCodeAt_slot]
      split <;> simp_all

/-- Substitute the exact finite colour transport: literal facial presence is
therefore a recurrence of the predecessor colour code and local rebase data,
not a semantic observation of the successor graph. -/
theorem sourceLocalLayerSerialFaceTargetPresentAt_transport_exact
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
    (hcellColor : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) :
    let next := sourceLocalLayerNextOffset offset hnext
    let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
      coloring web corridor hunique next
    sourceLocalLayerSerialFaceTargetPresentAt graphData minimal caps coloring web
        corridor hunique next hcell
        (sourceLocalLayerSerialCellRebaseTransportedColorCodeAt graphData minimal
          caps coloring web corridor hunique offset hnext cellColor hcellColor) =
      (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique next
        hcell).interfacePresent := by
  dsimp only
  rw [sourceLocalLayerSerialCellRebaseTransportedColorCodeAt_eq_target_of_pastCellOverlap
    graphData minimal caps coloring web corridor hunique offset hnext cellColor
      hcellColor]
  · exact sourceLocalLayerSerialFaceTargetPresentAt_exact graphData minimal caps
      coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
      (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset coloring
        cellColor)
  · intro targetEdge prior hprior hpriorCell
    exact Or.inl <|
      sourceLocalLayerSerialCellRebase_pastCellOverlap_mem_switch graphData
        minimal caps coloring web corridor hunique offset hnext targetEdge prior
        hprior hpriorCell

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetState

end Mettapedia.GraphTheory.FourColor
