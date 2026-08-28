import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedRollingHistoricalLocality
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence

/-!
# Rolling locality for the pointwise-selected tracked carrier

An active coordinate of the following selected interaction carrier is already
named by the current forty-nine-edge interaction carrier.  The following
rolling part is handled by the selected past-overlap theorem.  A strict
historical edge meeting the following rebase collar is handled by the local
dual-corridor statements proved without a global selector.

This is a one-step locality theorem.  It neither assumes nor asserts eventual
saturation of a reachable profile set.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedRollingLocality

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap
open GoertzelV24ClosedWebPointwiseSelectedRollingHistoricalLocality
open GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorPointwiseRungs
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedRollingLocalityOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A strict historical selected Cell which meets the following rebase collar
already meets the current bounded interaction carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebase_strictHistory_nextCollar_mem_currentInteraction
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (prior : Fin (blockLength - 3))
    (hprior : prior.val < offset.val)
    (edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (hhistory : edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior prior)
    (hcollar : edge ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseTrackedCollarAt web
        corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hnextNext) :
    edge ∈
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext := by
  let next := sourceLocalLayerNextOffset offset hnext
  let nextNext := sourceLocalLayerNextOffset next hnextNext
  have hpriorNext : prior.val < next.val := by
    simp only [next, sourceLocalLayerNextOffset_val]
    omega
  rcases (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).1
      (by simpa
        [pointwiseSelectedSourceLocalLayerBoundaryRebaseTrackedCollarAt, next]
        using hcollar) with
    hedgeSwitch | ⟨root, hrootSwitch, hedgeAdj⟩
  · let root := edge
    have hrootSwitch' : root ∈
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt web.toFormation
          corridor hinterior next hnextNext := by
      simpa [root, next] using hedgeSwitch
    have hrel : edge = root ∨
        web.annular.RS.edgeAdjacencyGraph.Adj edge root := Or.inl rfl
    rcases
        (mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff
          web.toFormation corridor hinterior next hnextNext root).1
            hrootSwitch' with ⟨role, hrole⟩
    rcases role with consumed | incomingOrSuccessor
    · apply Finset.mem_union_right
      apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
      apply Or.inl
      rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inr (.inr ⟨0, by omega⟩), ?_⟩
      simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next, root]
        using hrole
    · rcases incomingOrSuccessor with incoming | successor
      · have hrootEq :
            pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
                corridor hinterior nextNext incoming = root := by
          simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next,
            nextNext] using hrole
        have hrelTarget : edge =
              pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
                corridor hinterior nextNext incoming ∨
            web.annular.RS.edgeAdjacencyGraph.Adj edge
              (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
                corridor hinterior nextNext incoming) := by
          rw [hrootEq]
          exact hrel
        have hsuc :=
          pointwiseSelectedSourceLocalLayerSerialCellRebase_history_eq_or_adj_nextLeft_succ_eq
            graphData minimal caps coloring web corridor hinterior next
              hnextNext prior hpriorNext edge hhistory incoming
                (by simpa [nextNext] using hrelTarget)
        simp only [next, sourceLocalLayerNextOffset_val] at hsuc
        omega
      · let skeleton :=
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        have hrootFace :
            pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
                corridor hinterior nextNext ∈
              orbitFaceBoundary web.annular.RS
                (skeleton.faceAt
                  (pointwiseSelectedSourceLocalLayerInteriorAt
                    nextNext).center).1 := by
          simpa [pointwiseSelectedSourceLocalLayerSharedRungAt, skeleton] using
            pointwiseRungEdge_mem_left skeleton
              (boundaryCleanCorridor_consecutiveRungUnique web.annular hinterior
                corridor)
              (pointwiseSelectedSourceLocalLayerInteriorAt nextNext).outgoing
        have hrootEq :
            pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
              corridor hinterior nextNext = root := by
          simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next,
            nextNext] using hrole
        have hrelTarget : edge =
              pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
                corridor hinterior nextNext ∨
            web.annular.RS.edgeAdjacencyGraph.Adj edge
              (pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
                corridor hinterior nextNext) := by
          rw [hrootEq]
          exact hrel
        have hsuc :=
          pointwiseSelectedSourceLocalLayerSerialCellRebase_history_eq_or_adj_nextCenterEdge_succ_eq
            graphData minimal caps coloring web corridor hinterior next
              hnextNext prior hpriorNext edge
                (pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
                  corridor hinterior nextNext) hhistory hrootFace
                    (by simpa [nextNext] using hrelTarget)
        simp only [next, sourceLocalLayerNextOffset_val] at hsuc
        omega
  · have hrootSwitch' : root ∈
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt web.toFormation
          corridor hinterior next hnextNext := by
      simpa [next] using hrootSwitch
    have hrel : edge = root ∨
        web.annular.RS.edgeAdjacencyGraph.Adj edge root := Or.inr hedgeAdj
    rcases
        (mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff
          web.toFormation corridor hinterior next hnextNext root).1
            hrootSwitch' with ⟨role, hrole⟩
    rcases role with consumed | incomingOrSuccessor
    · apply Finset.mem_union_right
      apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
      refine Or.inr ⟨root, ?_, hedgeAdj⟩
      rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inr (.inr ⟨0, by omega⟩), ?_⟩
      simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next]
        using hrole
    · rcases incomingOrSuccessor with incoming | successor
      · have hrootEq :
            pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
                corridor hinterior nextNext incoming = root := by
          simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next,
            nextNext] using hrole
        have hrelTarget : edge =
              pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
                corridor hinterior nextNext incoming ∨
            web.annular.RS.edgeAdjacencyGraph.Adj edge
              (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
                corridor hinterior nextNext incoming) := by
          rw [hrootEq]
          exact hrel
        have hsuc :=
          pointwiseSelectedSourceLocalLayerSerialCellRebase_history_eq_or_adj_nextLeft_succ_eq
            graphData minimal caps coloring web corridor hinterior next
              hnextNext prior hpriorNext edge hhistory incoming
                (by simpa [nextNext] using hrelTarget)
        simp only [next, sourceLocalLayerNextOffset_val] at hsuc
        omega
      · let skeleton :=
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        have hrootFace :
            pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
                corridor hinterior nextNext ∈
              orbitFaceBoundary web.annular.RS
                (skeleton.faceAt
                  (pointwiseSelectedSourceLocalLayerInteriorAt
                    nextNext).center).1 := by
          simpa [pointwiseSelectedSourceLocalLayerSharedRungAt, skeleton] using
            pointwiseRungEdge_mem_left skeleton
              (boundaryCleanCorridor_consecutiveRungUnique web.annular hinterior
                corridor)
              (pointwiseSelectedSourceLocalLayerInteriorAt nextNext).outgoing
        have hrootEq :
            pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
              corridor hinterior nextNext = root := by
          simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next,
            nextNext] using hrole
        have hrelTarget : edge =
              pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
                corridor hinterior nextNext ∨
            web.annular.RS.edgeAdjacencyGraph.Adj edge
              (pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
                corridor hinterior nextNext) := by
          rw [hrootEq]
          exact hrel
        have hsuc :=
          pointwiseSelectedSourceLocalLayerSerialCellRebase_history_eq_or_adj_nextCenterEdge_succ_eq
            graphData minimal caps coloring web corridor hinterior next
              hnextNext prior hpriorNext edge
                (pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
                  corridor hinterior nextNext) hhistory hrootFace
                    (by simpa [nextNext] using hrelTarget)
        simp only [next, sourceLocalLayerNextOffset_val] at hsuc
        omega

set_option maxHeartbeats 800000 in
/-- Every active coordinate of the following selected interaction carrier is
already named by the current selected interaction carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebase_activeNextInteraction_mem_currentInteraction
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (targetEdge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hnextNext})
    (hactive : targetEdge.1 ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)) :
    targetEdge.1 ∈
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext := by
  let next := sourceLocalLayerNextOffset offset hnext
  have htarget := targetEdge.property
  change targetEdge.1 ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          web.toFormation corridor hinterior next ∪
        pointwiseSelectedSourceLocalLayerBoundaryRebaseTrackedCollarAt web
          corridor hinterior next hnextNext at htarget
  rw [Finset.mem_union] at htarget
  rcases htarget with hrolling | hcollar
  · let rollingEdge : {edge // edge ∈
        pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          web.toFormation corridor hinterior next} :=
      ⟨targetEdge.1, hrolling⟩
    rcases
        pointwiseSelectedSourceLocalLayerSerialCellRebase_activeTarget_mem_switch_or_currentCell
          graphData minimal caps coloring web corridor hinterior offset hnext
            rollingEdge hactive with hswitch | hcell
    · apply Finset.mem_union_right
      apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).2
      exact Or.inl hswitch
    · exact Finset.mem_union_left _ <| Finset.mem_union_left _ <|
        Finset.mem_union_left _ hcell
  · rw [pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt,
      Finset.mem_union] at hactive
    rcases hactive with hinput | hrung
    · rw [pointwiseSelectedSourceLocalLayerSerialInputRegionAt,
        Finset.mem_union] at hinput
      rcases hinput with hprefix | hcrossing
      · rw [pointwiseSelectedSourceLocalLayerSerialPrefixRegion,
          Finset.mem_biUnion] at hprefix
        rcases hprefix with ⟨prior, hprior, hhistory⟩
        have hpriorLt : prior.val < next.val :=
          (Finset.mem_filter.mp hprior).2
        by_cases hstrict : prior.val < offset.val
        · exact
            pointwiseSelectedSourceLocalLayerSerialCellRebase_strictHistory_nextCollar_mem_currentInteraction
              graphData minimal caps coloring web corridor hinterior offset
                hnext hnextNext prior hstrict targetEdge.1 hhistory
                  (by simpa [next] using hcollar)
        · have heq : prior = offset := by
            apply Fin.ext
            simp only [next, sourceLocalLayerNextOffset_val] at hpriorLt
            omega
          exact Finset.mem_union_left _ <| Finset.mem_union_left _ <|
            Finset.mem_union_left _ (heq ▸ hhistory)
      · rcases (mem_indexedCrossingEdgeSet_iff
            (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
              corridor hinterior next) targetEdge.1).1 hcrossing with
          ⟨step, hedge⟩
        apply Finset.mem_union_right
        apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).2
        apply Or.inl
        rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
        refine ⟨.inr (.inl step), ?_⟩
        simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next]
          using hedge
    · have hedge : targetEdge.1 =
          pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
            corridor hinterior next := by
        simpa using hrung
      apply Finset.mem_union_right
      apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).2
      apply Or.inl
      rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inr (.inr ⟨0, by omega⟩), ?_⟩
      simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next]
        using hedge.symm

/-- A following-interaction coordinate absent from the current carrier is
inactive in every literal selected successor tracked graph. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebase_nextInteraction_none_not_mem_support
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (targetEdge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hnextNext})
    (hnot : targetEdge.1 ∉
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext) :
    targetEdge.1 ∉
      (pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation corridor
        hinterior offset hnext color pair).support := by
  intro hsupport
  rcases (SimpleGraph.mem_support _).1 hsupport with ⟨other, hadj⟩
  apply hnot
  exact
    pointwiseSelectedSourceLocalLayerSerialCellRebase_activeNextInteraction_mem_currentInteraction
      graphData minimal caps coloring web corridor hinterior offset hnext
        hnextNext targetEdge hadj.2.1

end


end GoertzelV24ClosedWebPointwiseSelectedRollingLocality

end Mettapedia.GraphTheory.FourColor
