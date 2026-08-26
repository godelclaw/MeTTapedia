import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseHistoricalLocality
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor

/-!
# Rolling locality for the rooted Cell--rebase interaction carrier

The exact successor prefix is already computable on the current
forty-nine-edge interaction carrier.  To use that code as the root of the
following Cell, one must still compare it with the following interaction
carrier.  A newly named coordinate there is harmless unless it is active in
the accumulated prefix.

This file proves the required structural statement.  An active coordinate of
the following interaction carrier is already present in the current
interaction carrier.  For the rolling twenty-one-edge part this is the
established past-overlap theorem.  For the following rebase collar, strict
historical locality says that contact can only come from the immediately
preceding Cell; the remaining named boundary edges already lie in the current
rebase collar.

The statement is local and independent of corridor length.  It does not assume
or assert eventual saturation of a reachable profile set.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingLocality

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseHistoricalLocality
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rootedInteractionRollingLocalityOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A strict historical Cell which meets the following rebase collar already
meets the current bounded interaction carrier. -/
theorem sourceLocalLayerSerialCellRebase_strictHistory_nextCollar_mem_currentInteraction
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (prior : Fin (blockLength - 3))
    (hprior : prior.val < offset.val)
    (edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (hhistory : edge ∈
      sourceLocalLayerCellRegionAt corridor hunique prior)
    (hcollar : edge ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique (sourceLocalLayerNextOffset offset hnext) hnextNext) :
    edge ∈ sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
      caps coloring web corridor hunique offset hnext := by
  let next := sourceLocalLayerNextOffset offset hnext
  let nextNext := sourceLocalLayerNextOffset next hnextNext
  have hpriorNext : prior.val < next.val := by
    simp only [next, sourceLocalLayerNextOffset_val]
    omega
  rcases (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).1
      (by simpa [sourceLocalLayerBoundaryRebaseTrackedCollarAt, next] using
        hcollar) with
    hedgeSwitch | ⟨root, hrootSwitch, hedgeAdj⟩
  · let root := edge
    have hrootSwitch' : root ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor
        hunique next hnextNext := by
      simpa [root, next] using hedgeSwitch
    have hrel : edge = root ∨
        web.annular.RS.edgeAdjacencyGraph.Adj edge root := Or.inl rfl
    rcases (mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique next
        hnextNext root).1 hrootSwitch' with ⟨role, hrole⟩
    rcases role with consumed | incomingOrSuccessor
    · apply Finset.mem_union_right
      apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
      apply Or.inl
      rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inr (.inr (0 : Fin 1)), ?_⟩
      simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next, root] using hrole
    · rcases incomingOrSuccessor with incoming | successor
      · have hrootEq :
            sourceLocalLayerLeftCrossingAt corridor hunique nextNext incoming =
              root := by
          simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next, nextNext] using hrole
        have hrelTarget : edge =
              sourceLocalLayerLeftCrossingAt corridor hunique nextNext incoming ∨
            web.annular.RS.edgeAdjacencyGraph.Adj edge
              (sourceLocalLayerLeftCrossingAt corridor hunique nextNext
                incoming) := by
          rw [hrootEq]
          exact hrel
        have hsuc :=
          sourceLocalLayerSerialCellRebase_history_eq_or_adj_nextLeft_succ_eq
            graphData minimal caps coloring web corridor hunique next hnextNext
              prior hpriorNext edge hhistory incoming
              (by simpa [nextNext] using hrelTarget)
        simp only [next, sourceLocalLayerNextOffset_val] at hsuc
        omega
      · let skeleton :=
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        have hrootFace : sourceLocalLayerSharedRungAt corridor hunique nextNext ∈
            orbitFaceBoundary web.annular.RS
              (skeleton.faceAt
                (sourceLocalLayerInteriorAt nextNext).center).1 := by
          simpa [sourceLocalLayerSharedRungAt, skeleton] using
            skeleton.rungEdge_mem_left hunique
              (sourceLocalLayerInteriorAt nextNext).outgoing
        have hrootEq :
            sourceLocalLayerSharedRungAt corridor hunique nextNext = root := by
          simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next, nextNext] using hrole
        have hrelTarget : edge =
              sourceLocalLayerSharedRungAt corridor hunique nextNext ∨
            web.annular.RS.edgeAdjacencyGraph.Adj edge
              (sourceLocalLayerSharedRungAt corridor hunique nextNext) := by
          rw [hrootEq]
          exact hrel
        have hsuc :=
          sourceLocalLayerSerialCellRebase_history_eq_or_adj_nextCenterEdge_succ_eq
            graphData minimal caps coloring web corridor hunique next hnextNext
              prior hpriorNext edge
              (sourceLocalLayerSharedRungAt corridor hunique nextNext) hhistory
              hrootFace
              hrelTarget
        simp only [next, sourceLocalLayerNextOffset_val] at hsuc
        omega
  · have hrootSwitch' : root ∈
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique next hnextNext :=
      by simpa [next] using hrootSwitch
    have hrel : edge = root ∨
        web.annular.RS.edgeAdjacencyGraph.Adj edge root := Or.inr hedgeAdj
    rcases (mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique next
        hnextNext root).1 hrootSwitch' with ⟨role, hrole⟩
    rcases role with consumed | incomingOrSuccessor
    · apply Finset.mem_union_right
      apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
      refine Or.inr ⟨root, ?_, hedgeAdj⟩
      rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inr (.inr (0 : Fin 1)), ?_⟩
      simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next] using hrole
    · rcases incomingOrSuccessor with incoming | successor
      · have hrootEq :
            sourceLocalLayerLeftCrossingAt corridor hunique nextNext incoming =
              root := by
          simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next, nextNext] using hrole
        have hrelTarget : edge =
              sourceLocalLayerLeftCrossingAt corridor hunique nextNext incoming ∨
            web.annular.RS.edgeAdjacencyGraph.Adj edge
              (sourceLocalLayerLeftCrossingAt corridor hunique nextNext
                incoming) := by
          rw [hrootEq]
          exact hrel
        have hsuc :=
          sourceLocalLayerSerialCellRebase_history_eq_or_adj_nextLeft_succ_eq
            graphData minimal caps coloring web corridor hunique next hnextNext
              prior hpriorNext edge hhistory incoming
              (by simpa [nextNext] using hrelTarget)
        simp only [next, sourceLocalLayerNextOffset_val] at hsuc
        omega
      · let skeleton :=
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        have hrootFace : sourceLocalLayerSharedRungAt corridor hunique nextNext ∈
            orbitFaceBoundary web.annular.RS
              (skeleton.faceAt
                (sourceLocalLayerInteriorAt nextNext).center).1 := by
          simpa [sourceLocalLayerSharedRungAt, skeleton] using
            skeleton.rungEdge_mem_left hunique
              (sourceLocalLayerInteriorAt nextNext).outgoing
        have hrootEq :
            sourceLocalLayerSharedRungAt corridor hunique nextNext = root := by
          simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next, nextNext] using hrole
        have hrelTarget : edge =
              sourceLocalLayerSharedRungAt corridor hunique nextNext ∨
            web.annular.RS.edgeAdjacencyGraph.Adj edge
              (sourceLocalLayerSharedRungAt corridor hunique nextNext) := by
          rw [hrootEq]
          exact hrel
        have hsuc :=
          sourceLocalLayerSerialCellRebase_history_eq_or_adj_nextCenterEdge_succ_eq
            graphData minimal caps coloring web corridor hunique next hnextNext
              prior hpriorNext edge
              (sourceLocalLayerSharedRungAt corridor hunique nextNext) hhistory
              hrootFace
              hrelTarget
        simp only [next, sourceLocalLayerNextOffset_val] at hsuc
        omega

/-- Every active coordinate of the following interaction carrier is already
named by the current interaction carrier.  This is the exact one-step rolling
locality property needed to prevent the rooted receipt from growing. -/
theorem sourceLocalLayerSerialCellRebase_activeNextInteraction_mem_currentInteraction
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (targetEdge : {edge // edge ∈
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          hnextNext})
    (hactive : targetEdge.1 ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)) :
    targetEdge.1 ∈
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext := by
  let next := sourceLocalLayerNextOffset offset hnext
  have htarget := targetEdge.property
  change targetEdge.1 ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique next ∪
        sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique next
          hnextNext at htarget
  rw [Finset.mem_union] at htarget
  rcases htarget with hrolling | hcollar
  · let rollingEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique next} := ⟨targetEdge.1, hrolling⟩
    rcases sourceLocalLayerSerialCellRebase_activeTarget_mem_switch_or_currentCell
        graphData minimal caps coloring web corridor hunique offset hnext
          rollingEdge hactive with hswitch | hcell
    · apply Finset.mem_union_right
      apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).2
      exact Or.inl hswitch
    · exact Finset.mem_union_left _ <| Finset.mem_union_left _ <|
        Finset.mem_union_left _ hcell
  · rw [sourceLocalLayerSerialTerminalInputRegionAt, Finset.mem_union] at hactive
    rcases hactive with hinput | hrung
    · rw [sourceLocalLayerSerialInputRegionAt, Finset.mem_union] at hinput
      rcases hinput with hprefix | hcrossing
      · rw [sourceLocalLayerSerialPrefixRegion, Finset.mem_biUnion] at hprefix
        rcases hprefix with ⟨prior, hprior, hhistory⟩
        have hpriorLt : prior.val < next.val := (Finset.mem_filter.mp hprior).2
        by_cases hstrict : prior.val < offset.val
        · exact
            sourceLocalLayerSerialCellRebase_strictHistory_nextCollar_mem_currentInteraction
              graphData minimal caps coloring web corridor hunique offset hnext
                hnextNext prior hstrict targetEdge.1 hhistory
                hcollar
        · have heq : prior = offset := by
            apply Fin.ext
            simp only [next, sourceLocalLayerNextOffset_val] at hpriorLt
            omega
          exact Finset.mem_union_left _ <| Finset.mem_union_left _ <|
            Finset.mem_union_left _ (heq ▸ hhistory)
      · rcases (mem_indexedCrossingEdgeSet_iff
            (sourceLocalLayerLeftCrossingAt corridor hunique next)
            targetEdge.1).1 hcrossing with ⟨step, hedge⟩
        apply Finset.mem_union_right
        apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).2
        apply Or.inl
        rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
        refine ⟨.inr (.inl step), ?_⟩
        simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next] using hedge
    · have hedge : targetEdge.1 =
          sourceLocalLayerSharedRungAt corridor hunique next := by
        simpa using hrung
      apply Finset.mem_union_right
      apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).2
      apply Or.inl
      rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inr (.inr (0 : Fin 1)), ?_⟩
      simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next] using hedge.symm

/-- Consequently, a following-interaction coordinate which is absent from the
current interaction carrier is inactive in every literal successor tracked
graph. -/
theorem sourceLocalLayerSerialCellRebase_nextInteraction_none_not_mem_support
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (targetEdge : {edge // edge ∈
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          hnextNext})
    (hnot : targetEdge.1 ∉
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext) :
    targetEdge.1 ∉
      (successorTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).support := by
  intro hsupport
  rcases (SimpleGraph.mem_support _).1 hsupport with ⟨other, hadj⟩
  apply hnot
  exact
    sourceLocalLayerSerialCellRebase_activeNextInteraction_mem_currentInteraction
      graphData minimal caps coloring web corridor hunique offset hnext
        hnextNext targetEdge hadj.2.1

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingLocality

end Mettapedia.GraphTheory.FourColor
