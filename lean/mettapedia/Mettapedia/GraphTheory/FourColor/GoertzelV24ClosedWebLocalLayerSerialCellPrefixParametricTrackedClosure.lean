import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellSplicedTrackedFiniteClosure
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialTrackedPrefixAttachmentColorParametric

/-!
# Prefix-parametric tracked closure for one literal Cell

The ambient Tait colouring fixes the closed-web geometry.  The accumulated
prefix colouring is separate data: it may be any colour function whose two
displayed cut edges are nonzero.  When it agrees with a positive literal Cell
on their actual overlap, the exact pre-rebase tracked graph is the finite
closure of that prefix state and the Cell code.

This is the compositional form needed by a product of transfer letters.  The
ambient-prefix specializations proved earlier are recovered by taking
`prefixColor := coloring`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricTrackedClosure

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellSplicedTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialTrackedPrefixAttachmentColorParametric
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance prefixParametricTrackedClosureOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The finite carrier-colour compatibility test represents literal overlap
agreement for an arbitrary accumulated prefix colouring. -/
theorem sourceLocalLayerSerialCarrierColorsCompatibleForColor_iff
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
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    SourceLocalLayerSerialCarrierColorsCompatible
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          prefixColor)
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor) ↔
      SourceLocalLayerSerialCellColorsCompatibleAt corridor hunique offset
        prefixColor cellColor := by
  constructor
  · intro hfinite edge hprefix hcell
    let carrierEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique offset} :=
      ⟨edge, Finset.mem_union_left _ (Finset.mem_union_left _ hcell)⟩
    apply hfinite
      (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
        coloring web corridor hunique offset carrierEdge)
      (prefixColor edge) (cellColor edge)
    · simp [carrierEdge, hprefix,
        sourceLocalLayerSerialCarrierColorCodeAt_slot]
    · simp [carrierEdge, hcell,
        sourceLocalLayerSerialCarrierColorCodeAt_slot]
  · intro hactual slot oldColor newColor hprefix hcell
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

/-- Exact three-factor tracked closure after adjoining one compatible Cell to
an arbitrary realized cumulative prefix. -/
theorem
    sourceLocalLayerSerialSplicedPreRebaseTrackedReachableForColor_iff_finiteClosure
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
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset prefixColor cellColor)
    (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    (regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
        prefixColor cellColor)
      (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable left.1 right.1 ↔
      Relation.ReflTransGen
        (SourceLocalLayerSerialTrackedFiniteComponentStep
          (sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt graphData
            caps coloring web corridor hunique offset prefixColor)
          (terminalInputBoundedProfileForColorAt corridor hunique offset
            prefixColor hprefixCrossing)
          (sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData
            minimal caps coloring web corridor hunique offset
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              prefixColor cellColor))
          pair)
        (carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset) left)
        (carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset) right) := by
  apply sourceLocalLayerSerialPreRebaseTrackedReachableForColor_iff_finiteClosure
    graphData minimal caps coloring web corridor hunique offset
    (sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt graphData caps
      coloring web corridor hunique offset prefixColor)
    (terminalInputBoundedProfileForColorAt corridor hunique offset prefixColor
      hprefixCrossing)
    (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset prefixColor
      cellColor)
  intro prefixPair first second
  rw [regionalTrackedEdgeGraph_spliced_eq_prefix corridor hunique offset
    prefixColor cellColor hcompatible (trackedColorPairColors prefixPair).1
      (trackedColorPairColors prefixPair).2]
  exact
    (sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt_factoredReachability_iff
      graphData minimal caps coloring web corridor hunique offset prefixColor
        hprefixCrossing prefixPair first second).symm

/-- The tracked-connectivity field of the spliced output profile is exactly
the finite closure above, for an arbitrary cumulative prefix colouring. -/
theorem
    sourceLocalLayerSerialSplicedPreRebaseOutputForColor_strandConnected_iff_finiteClosure
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
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset prefixColor cellColor)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (pair : TrackedColorPair) (left right : Fin 2) :
    (sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt corridor
        hunique offset prefixColor cellColor hcellColor).profile.strandConnected
          pair (.inl left) (.inl right) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          ((sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt corridor
            hunique offset prefixColor cellColor hcellColor).profile.edgeColor
              left).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          ((sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt corridor
            hunique offset prefixColor cellColor hcellColor).profile.edgeColor
              right).toColor ∧
        Relation.ReflTransGen
          (SourceLocalLayerSerialTrackedFiniteComponentStep
            (sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
              graphData caps coloring web corridor hunique offset prefixColor)
            (terminalInputBoundedProfileForColorAt corridor hunique offset
              prefixColor hprefixCrossing)
            (sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData
              minimal caps coloring web corridor hunique offset
              (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
                prefixColor cellColor))
            pair)
          (carrierCoordinate
            (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset)
            (sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData caps
              coloring web corridor hunique offset left))
          (carrierCoordinate
            (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset)
            (sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData caps
              coloring web corridor hunique offset right)) := by
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    prefixColor cellColor
  let data := regionalBoundaryGraphCutData web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    (sourceLocalLayerRightCrossingAt corridor hunique offset)
  have hsplice : ∀ step, splice (data.crossingEdge step) ≠ 0 := by
    intro step
    change sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
        prefixColor cellColor
        (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠ 0
    rw [sourceLocalLayerSerialCellSplicedColorAt_rightCrossing corridor hunique
      offset prefixColor cellColor step]
    exact hcellColor step
  have hports : data.PortsInRegion := by
    apply regionalBoundaryGraphCutData_portsInRegion
    intro step
    rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
      hunique offset]
    exact Finset.mem_union_right _
      (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset step)
  let leftPoint := sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData
    caps coloring web corridor hunique offset left
  let rightPoint := sourceLocalLayerSerialTrackedOutgoingCarrierPointAt graphData
    caps coloring web corridor hunique offset right
  have hfinite :=
    sourceLocalLayerSerialSplicedPreRebaseTrackedReachableForColor_iff_finiteClosure
      graphData minimal caps coloring web corridor hunique offset prefixColor
        cellColor hprefixCrossing hcompatible pair leftPoint rightPoint
  change (data.regionalProfile splice hsplice).strandConnected pair (.inl left)
      (.inl right) = true ↔ _
  rw [data.regionalProfile_strandConnected_eq_true_iff]
  constructor
  · rintro ⟨_hleftPort, _hrightPort, hleftColor, hrightColor, hreachable⟩
    refine ⟨?_, ?_, hfinite.1 hreachable⟩
    · rw [sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt_edgeColor]
      change IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (splice (sourceLocalLayerRightCrossingAt corridor hunique offset left))
          at hleftColor
      dsimp only [splice] at hleftColor
      rw [sourceLocalLayerSerialCellSplicedColorAt_rightCrossing corridor hunique
        offset prefixColor cellColor left] at hleftColor
      exact hleftColor
    · rw [sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt_edgeColor]
      change IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (splice (sourceLocalLayerRightCrossingAt corridor hunique offset right))
          at hrightColor
      dsimp only [splice] at hrightColor
      rw [sourceLocalLayerSerialCellSplicedColorAt_rightCrossing corridor hunique
        offset prefixColor cellColor right] at hrightColor
      exact hrightColor
  · rintro ⟨hleftColor, hrightColor, hclosure⟩
    refine ⟨hports (.inl left), hports (.inl right), ?_, ?_,
      hfinite.2 hclosure⟩
    · rw [sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt_edgeColor]
        at hleftColor
      change IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (splice (sourceLocalLayerRightCrossingAt corridor hunique offset left))
      dsimp only [splice]
      rw [sourceLocalLayerSerialCellSplicedColorAt_rightCrossing corridor hunique
        offset prefixColor cellColor left]
      exact hleftColor
    · rw [sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt_edgeColor]
        at hrightColor
      change IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (splice (sourceLocalLayerRightCrossingAt corridor hunique offset right))
      dsimp only [splice]
      rw [sourceLocalLayerSerialCellSplicedColorAt_rightCrossing corridor hunique
        offset prefixColor cellColor right]
      exact hrightColor

end

end GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricTrackedClosure

end Mettapedia.GraphTheory.FourColor
