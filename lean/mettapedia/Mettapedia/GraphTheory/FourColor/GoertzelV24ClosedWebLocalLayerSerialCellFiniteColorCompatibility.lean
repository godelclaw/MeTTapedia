import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState

/-!
# Exact finite colour compatibility for one literal source Cell

The cumulative prefix and a positive literal `Cell` witness may use different
colour functions.  Their splice is valid exactly when those functions agree
on the literal overlap of the predecessor and Cell regions.

Reachability cannot encode this condition: it is reflexive even at an
isolated retained coordinate, and graph support can omit a tracked boundary
edge which has no tracked neighbour inside the selected region.  This file
therefore records the honest finite datum directly.  Each of the twenty-one
stable transition slots stores `some colour` precisely when its represented
edge lies in the selected region, and `none` otherwise.

The main theorem proves that compatibility of the two finite partial colour
tables is equivalent to pointwise compatibility on the actual graph regions.
It is representation bookkeeping for the source's Phase-5 factorization; it
does not assert positivity of a `Count` entry or perform the boundary rebase.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section


local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A partial colour table on the stable twenty-one-slot Cell-transition ABI.
`none` means that the slot is padding or its represented edge is outside the
selected region. -/
abbrev SourceLocalLayerSerialCarrierColorCode := Fin 21 -> Option Color

/-- Decode the literal transition edge at a stable slot and record its colour
exactly when that edge belongs to `region`. -/
noncomputable def sourceLocalLayerSerialCarrierColorCodeAt
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
    (region : Finset
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color) :
    SourceLocalLayerSerialCarrierColorCode :=
  fun slot =>
    (sourceLocalLayerSerialTrackedTransitionEdgeAtSlot? graphData caps coloring
      web corridor hunique offset slot).bind fun edge =>
        if edge.1 ∈ region then some (color edge.1) else none

/-- A represented literal edge is read back at its stable slot, with no loss
of either regional activity or colour. -/
@[simp]
theorem sourceLocalLayerSerialCarrierColorCodeAt_slot
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
    (region : Finset
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color)
    (edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset region color
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset edge) =
      if edge.1 ∈ region then some (color edge.1) else none := by
  simp [sourceLocalLayerSerialCarrierColorCodeAt]

/-- Two partial colour tables agree wherever both are active. -/
def SourceLocalLayerSerialCarrierColorsCompatible
    (oldCode newCode : SourceLocalLayerSerialCarrierColorCode) : Prop :=
  ∀ slot prefixColor cellColor,
    oldCode slot = some prefixColor ->
    newCode slot = some cellColor ->
    prefixColor = cellColor

noncomputable instance
    (oldCode newCode : SourceLocalLayerSerialCarrierColorCode) :
    Decidable (SourceLocalLayerSerialCarrierColorsCompatible oldCode newCode) :=
  Classical.propDecidable _

/-- The finite partial-table test is sound and complete for literal colour
agreement on the actual prefix/Cell overlap. -/
theorem sourceLocalLayerSerialCarrierColorsCompatible_iff
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color) :
    SourceLocalLayerSerialCarrierColorsCompatible
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          coloring)
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor) ↔
      SourceLocalLayerSerialCellColorsCompatibleAt corridor hunique offset
        coloring cellColor := by
  constructor
  · intro hfinite edge hprefix hcell
    let carrierEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique offset} :=
      ⟨edge, Finset.mem_union_left _ (Finset.mem_union_left _ hcell)⟩
    apply hfinite
      (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
        coloring web corridor hunique offset carrierEdge)
      (coloring edge) (cellColor edge)
    · simpa [carrierEdge, hprefix] using
        sourceLocalLayerSerialCarrierColorCodeAt_slot graphData minimal caps
          coloring web corridor hunique offset
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          coloring carrierEdge
    · simpa [carrierEdge, hcell] using
        sourceLocalLayerSerialCarrierColorCodeAt_slot graphData minimal caps
          coloring web corridor hunique offset
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor
          carrierEdge
  · intro hactual slot prefixColor cellColor hprefix hcell
    unfold sourceLocalLayerSerialCarrierColorCodeAt at hprefix hcell
    cases hdecode :
        sourceLocalLayerSerialTrackedTransitionEdgeAtSlot? graphData caps
          coloring web corridor hunique offset slot with
    | none => simp [hdecode] at hprefix
    | some edge =>
        simp only [hdecode, Option.bind_some] at hprefix hcell
        split at hprefix <;> rename_i hprefixMem
        · simp only [Option.some.injEq] at hprefix
          split at hcell <;> rename_i hcellMem
          · simp only [Option.some.injEq] at hcell
            exact hprefix.symm.trans
              ((hactual _ hprefixMem hcellMem).trans hcell)
          · simp at hcell
        · simp at hprefix

end

end GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility

end Mettapedia.GraphTheory.FourColor
