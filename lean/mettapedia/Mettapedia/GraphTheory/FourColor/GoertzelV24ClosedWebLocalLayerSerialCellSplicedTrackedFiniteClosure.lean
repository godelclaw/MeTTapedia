import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure

/-!
# Tracked finite closure for a compatible prefix/Cell color splice

The color-parametric three-factor theorem accepts any cumulative state whose
finite attachment data recover the realized prefix graph.  This file applies
that interface to the exact source splice: the ambient cumulative prefix is
left unchanged, while an arbitrary compatible literal Cell coloring supplies
the new Cell and residual-seam factors.

This closes the tracked coordinate of the arbitrary-Cell soundness direction.
It does not infer overlap compatibility from a displayed boundary word, and
it does not yet assemble the facial coordinates or the following boundary
rebase.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellSplicedTrackedFiniteClosure

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
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

local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- An arbitrary compatible literal Cell coloring can be adjoined to the
actual cumulative prefix, and complete tracked reachability is then exactly
the finite closure of the stored prefix state and the color-parametric local
Cell/seam code. -/
theorem sourceLocalLayerSerialSplicedPreRebaseTrackedReachable_iff_finiteClosure
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
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor)
    (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    (regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
        coloring cellColor)
      (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable left.1 right.1 ↔
      Relation.ReflTransGen
        (SourceLocalLayerSerialTrackedFiniteComponentStep
          (sourceLocalLayerSerialTrackedPrefixAttachmentStateAt graphData caps
            coloring web corridor hunique offset)
          (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
            offset)
          (sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData
            minimal caps coloring web corridor hunique offset
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              coloring cellColor))
          pair)
        (carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset) left)
        (carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset) right) := by
  apply sourceLocalLayerSerialPreRebaseTrackedReachableForColor_iff_finiteClosure
    graphData minimal caps coloring web corridor hunique offset
    (sourceLocalLayerSerialTrackedPrefixAttachmentStateAt graphData caps coloring
      web corridor hunique offset)
    (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique offset)
    (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset coloring
      cellColor)
  intro prefixPair first second
  rw [regionalTrackedEdgeGraph_spliced_eq_prefix corridor hunique offset coloring
    cellColor hcompatible (trackedColorPairColors prefixPair).1
      (trackedColorPairColors prefixPair).2]
  exact
    (sourceLocalLayerSerialTrackedPrefixAttachmentStateAt_factoredReachability_iff
      graphData minimal caps coloring web corridor hunique offset prefixPair
        first second).symm

/-- The tracked-connectivity coordinate of the spliced output profile is
exactly the finite closure above, guarded only by the two displayed output
colors. -/
theorem sourceLocalLayerSerialSplicedPreRebaseOutput_strandConnected_iff_finiteClosure
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
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (pair : TrackedColorPair) (left right : Fin 2) :
    (sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt corridor
        hunique offset coloring cellColor hcellColor).profile.strandConnected
          pair (.inl left) (.inl right) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          ((sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt corridor
            hunique offset coloring cellColor hcellColor).profile.edgeColor
              left).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          ((sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt corridor
            hunique offset coloring cellColor hcellColor).profile.edgeColor
              right).toColor ∧
        Relation.ReflTransGen
          (SourceLocalLayerSerialTrackedFiniteComponentStep
            (sourceLocalLayerSerialTrackedPrefixAttachmentStateAt graphData caps
              coloring web corridor hunique offset)
            (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor
              hunique offset)
            (sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData
              minimal caps coloring web corridor hunique offset
              (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
                coloring cellColor))
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
    coloring cellColor
  let data := regionalBoundaryGraphCutData web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    (sourceLocalLayerRightCrossingAt corridor hunique offset)
  have hsplice : ∀ step, splice (data.crossingEdge step) ≠ 0 := by
    intro step
    change sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
        coloring cellColor
        (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠ 0
    rw [sourceLocalLayerSerialCellSplicedColorAt_rightCrossing corridor hunique
      offset coloring cellColor step]
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
    sourceLocalLayerSerialSplicedPreRebaseTrackedReachable_iff_finiteClosure
      graphData minimal caps coloring web corridor hunique offset cellColor
        hcompatible pair leftPoint rightPoint
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
        offset coloring cellColor left] at hleftColor
      exact hleftColor
    · rw [sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt_edgeColor]
      change IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (splice (sourceLocalLayerRightCrossingAt corridor hunique offset right))
          at hrightColor
      dsimp only [splice] at hrightColor
      rw [sourceLocalLayerSerialCellSplicedColorAt_rightCrossing corridor hunique
        offset coloring cellColor right] at hrightColor
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
        offset coloring cellColor left]
      exact hleftColor
    · rw [sourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt_edgeColor]
        at hrightColor
      change IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (splice (sourceLocalLayerRightCrossingAt corridor hunique offset right))
      dsimp only [splice]
      rw [sourceLocalLayerSerialCellSplicedColorAt_rightCrossing corridor hunique
        offset coloring cellColor right]
      exact hrightColor

end

end GoertzelV24ClosedWebLocalLayerSerialCellSplicedTrackedFiniteClosure

end Mettapedia.GraphTheory.FourColor
