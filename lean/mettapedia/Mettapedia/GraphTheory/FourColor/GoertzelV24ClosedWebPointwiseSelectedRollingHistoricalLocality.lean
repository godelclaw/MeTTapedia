import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap

/-!
# Historical locality for the pointwise-selected rolling carrier

The corrected Cell geometry selects the shared interior edge separately at
each corridor position.  Consequently the historical rolling argument must
not import the former global unique-shared-edge selector.

This file proves the two local statements needed by the rolling projection.
If an edge of a strict historical selected Cell is equal or adjacent to an
edge on the centre face of the following Cell, or to one of its incoming
crossings, then that historical Cell is the immediate predecessor.  The proof
uses only the selected two-vertex Cell geometry and separation in the induced
dual corridor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedRollingHistoricalLocality

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseLocality
open GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellInternal
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedRollingHistoricalOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- If an edge of a strict historical selected Cell is equal or adjacent to
an edge on the following selected Cell's centre face, the historical Cell is
the immediate predecessor. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebase_history_eq_or_adj_nextCenterEdge_succ_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring
        Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (prior : Fin (blockLength - 3))
    (hprior : prior.val < offset.val)
    (edge root :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (hhistory : edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior prior)
    (hroot : root ∈ orbitFaceBoundary web.annular.RS
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt
          (pointwiseSelectedSourceLocalLayerInteriorAt
            (sourceLocalLayerNextOffset offset hnext)).center).1)
    (hrel : edge = root ∨
      web.annular.RS.edgeAdjacencyGraph.Adj edge root) :
    prior.val + 1 = offset.val := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let target := sourceLocalLayerNextOffset offset hnext
  let newCenter := (pointwiseSelectedSourceLocalLayerInteriorAt target).center
  let priorSide :=
    pointwiseSelectedSourceLocalLayerCellVertexSideAt web.toFormation corridor
      hinterior prior
  have hroot' : root ∈ orbitFaceBoundary web.annular.RS
      (skeleton.faceAt newCenter).1 := by
    simpa [skeleton, target, newCenter] using hroot
  have hcrossingLocal : ∀
      (crossing :
        caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet),
      crossing ∈ vertexSetCrossingEdges web.annular.RS priorSide →
      (crossing = root ∨
        web.annular.RS.edgeAdjacencyGraph.Adj crossing root) →
      prior.val + 1 = offset.val := by
    intro crossing hcrossing hcrossingRel
    rcases pointwiseSelectedSourceLocalLayerCellCrossingAt_eq_left_or_right
        web.toFormation corridor hinterior prior
          (by simpa [priorSide] using hcrossing) with
      ⟨oldStep, hedge⟩ | ⟨oldStep, hedge⟩
    · let oldCenter :=
        (pointwiseSelectedSourceLocalLayerInteriorAt prior).center
      have hold : crossing ∈ orbitFaceBoundary web.annular.RS
          (skeleton.faceAt oldCenter).1 := by
        rw [hedge]
        simpa [skeleton, oldCenter] using
          pointwiseSelectedSourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary
            web.toFormation corridor hinterior prior oldStep
      have hfacesNe : (skeleton.faceAt oldCenter).1 ≠
          (skeleton.faceAt newCenter).1 := by
        intro hfaces
        have hindices : oldCenter = newCenter :=
          skeleton.faceAt_injective (Subtype.ext hfaces)
        have hvalues := congrArg Fin.val hindices
        change prior.val + 1 = target.val + 1 at hvalues
        have htargetVal : target.val = offset.val + 1 := rfl
        rw [htargetVal] at hvalues
        omega
      have hfaceAdj :=
        interiorDualGraph_adj_of_eq_or_edgeAdjacencyGraph_adj web hfacesNe
          hold hroot' hcrossingRel
      have hseparated : oldCenter.val + 1 < newCenter.val := by
        change prior.val + 1 + 1 < target.val + 1
        have htargetVal : target.val = offset.val + 1 := rfl
        rw [htargetVal]
        omega
      exact False.elim
        ((skeleton.separated_not_adjacent oldCenter newCenter hseparated)
          hfaceAdj)
    · by_cases himmediate : prior.val + 1 = offset.val
      · exact himmediate
      · let oldCenter :=
          (nextCorridorInterior
            (pointwiseSelectedSourceLocalLayerInteriorAt prior)
            (pointwiseSelectedSourceLocalLayerInteriorAt_hasNext prior)).center
        have hold : crossing ∈ orbitFaceBoundary web.annular.RS
            (skeleton.faceAt oldCenter).1 := by
          rw [hedge]
          simpa [skeleton, oldCenter] using
            pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary
              web.toFormation corridor hinterior prior oldStep
        have hfacesNe : (skeleton.faceAt oldCenter).1 ≠
            (skeleton.faceAt newCenter).1 := by
          intro hfaces
          have hindices : oldCenter = newCenter :=
            skeleton.faceAt_injective (Subtype.ext hfaces)
          have hvalues := congrArg Fin.val hindices
          change prior.val + 2 = target.val + 1 at hvalues
          have htargetVal : target.val = offset.val + 1 := rfl
          rw [htargetVal] at hvalues
          omega
        have hfaceAdj :=
          interiorDualGraph_adj_of_eq_or_edgeAdjacencyGraph_adj web hfacesNe
            hold hroot' hcrossingRel
        have hseparated : oldCenter.val + 1 < newCenter.val := by
          change prior.val + 2 + 1 < target.val + 1
          have htargetVal : target.val = offset.val + 1 := rfl
          rw [htargetVal]
          omega
        exact False.elim
          ((skeleton.separated_not_adjacent oldCenter newCenter hseparated)
            hfaceAdj)
  by_cases hcrossing : edge ∈
      vertexSetCrossingEdges web.annular.RS priorSide
  · exact hcrossingLocal edge hcrossing hrel
  · rcases hrel with heq | hadj
    · rcases exists_pointwiseSelectedSourceLocalLayerRightCrossingAt_mem_cellCrossing
          graphData minimal caps coloring web corridor hinterior prior with
        ⟨oldStep, holdCrossing⟩
      have holdAdj := pointwiseSelected_internalEdge_adj_crossingEdge graphData
        minimal caps coloring web corridor hinterior prior hhistory
          (by simpa [priorSide] using hcrossing) holdCrossing
      apply hcrossingLocal
        (pointwiseSelectedSourceLocalLayerRightCrossingAt web.toFormation
          corridor hinterior prior oldStep)
        holdCrossing
      exact Or.inr (by simpa [heq] using holdAdj.symm)
    · have hrootCrossing := pointwiseSelected_crossingEdge_of_internalEdge_adj
        graphData minimal caps coloring web corridor hinterior prior hhistory
          (by simpa [priorSide] using hcrossing) hadj
      exact hcrossingLocal root hrootCrossing (Or.inl rfl)

/-- If an edge of a strict historical selected Cell is equal or adjacent to a
following incoming crossing, the historical Cell is the immediate
predecessor. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebase_history_eq_or_adj_nextLeft_succ_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring
        Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (prior : Fin (blockLength - 3))
    (hprior : prior.val < offset.val)
    (edge :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (hhistory : edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior prior)
    (newStep : Fin 2)
    (hrel : edge = pointwiseSelectedSourceLocalLayerLeftCrossingAt
          web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext) newStep ∨
      web.annular.RS.edgeAdjacencyGraph.Adj edge
        (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext)
            newStep)) :
    prior.val + 1 = offset.val := by
  apply
    pointwiseSelectedSourceLocalLayerSerialCellRebase_history_eq_or_adj_nextCenterEdge_succ_eq
      graphData minimal caps coloring web corridor hinterior offset hnext prior
        hprior edge
        (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext)
            newStep)
        hhistory
  · simpa using
      pointwiseSelectedSourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext) newStep
  · exact hrel

end

end GoertzelV24ClosedWebPointwiseSelectedRollingHistoricalLocality

end Mettapedia.GraphTheory.FourColor
