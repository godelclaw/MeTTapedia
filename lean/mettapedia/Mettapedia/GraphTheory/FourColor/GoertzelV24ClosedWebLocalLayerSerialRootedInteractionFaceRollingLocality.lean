import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingLocality

/-!
# Rolling locality for the rooted facial interaction carrier

The exact facial rebase is computed on a bounded forty-eight-dart carrier.  To
use its output as the lookahead root of the following Cell, an active dart of
the following interaction carrier must already be named by the current one.

The ordinary following transition carrier has this property by the established
occurrence-sensitive target theorem.  For the following facial collar, a dart
over strict history can only meet the consumed rung: meeting either future
incoming crossing or the future rung would violate corridor separation.  The
consumed-rung occurrence already lies in the current collar.  The remaining
active cases are the current Cell and its two named successor-boundary roles.

Thus the facial receipt rolls from one fixed forty-eight-dart carrier to the
next; no saturation or corridor-length hypothesis is used.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingLocality

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseHistoricalLocality
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingLocality
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance faceRollingLocalityOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A strict historical Cell occurrence in the following facial collar is
already named by the current facial interaction carrier. -/
theorem sourceLocalLayerSerialCellRebase_strictHistory_nextFaceCollar_mem_currentFaceInteraction
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
    (dart : web.annular.RS.D)
    (hhistory : web.annular.RS.edgeOf dart ∈
      sourceLocalLayerCellRegionAt corridor hunique prior)
    (hcollar : dart ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor
      hunique (sourceLocalLayerNextOffset offset hnext) hnextNext) :
    dart ∈ sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
      hunique offset hnext := by
  let next := sourceLocalLayerNextOffset offset hnext
  let nextNext := sourceLocalLayerNextOffset next hnextNext
  rw [sourceLocalLayerBoundaryRebaseFaceCollarAt, Finset.mem_biUnion] at hcollar
  rcases hcollar with ⟨base, hbaseChanged, hdartNear⟩
  have hbaseSwitch : web.annular.RS.edgeOf base ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique next hnextNext := by
    simpa [sourceLocalLayerBoundaryRebaseChangedFaceDartsAt, next] using
      hbaseChanged
  have hdartClosed : dart ∈
      closedDartCarrier web.annular.RS {web.annular.RS.edgeOf base} := by
    rw [closedDartCarrier, Finset.mem_biUnion]
    refine ⟨base, ?_, ?_⟩
    · rw [mem_dartsOnEdges_iff]
      simp
    · simpa [faceDartNeighbors] using hdartNear
  have hedgeClosed :=
    edgeOf_mem_edgeAdjacencyClosedCarrier_of_mem_closedDartCarrier
      web.annular.RS {web.annular.RS.edgeOf base} dart hdartClosed
  have hrelBase : web.annular.RS.edgeOf dart = web.annular.RS.edgeOf base ∨
      web.annular.RS.edgeAdjacencyGraph.Adj
        (web.annular.RS.edgeOf dart) (web.annular.RS.edgeOf base) := by
    rcases (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).1
        hedgeClosed with hedge | ⟨root, hroot, hadj⟩
    · exact Or.inl (by simpa using hedge)
    · have hrootEq : root = web.annular.RS.edgeOf base := by simpa using hroot
      exact Or.inr (hrootEq ▸ hadj)
  rcases (mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique next
      hnextNext (web.annular.RS.edgeOf base)).1 hbaseSwitch with ⟨role, hrole⟩
  rcases role with consumed | incomingOrSuccessor
  · have hbaseCurrentSwitch : web.annular.RS.edgeOf base ∈
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext := by
      rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inr (.inr (0 : Fin 1)), ?_⟩
      simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next] using hrole
    apply Finset.mem_union_right
    rw [sourceLocalLayerBoundaryRebaseFaceCollarAt, Finset.mem_biUnion]
    refine ⟨base, ?_, hdartNear⟩
    simpa [sourceLocalLayerBoundaryRebaseChangedFaceDartsAt] using
      hbaseCurrentSwitch
  · rcases incomingOrSuccessor with incoming | successor
    · have hbaseEq :
          sourceLocalLayerLeftCrossingAt corridor hunique nextNext incoming =
            web.annular.RS.edgeOf base := by
        simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next, nextNext] using hrole
      have hrelTarget : web.annular.RS.edgeOf dart =
            sourceLocalLayerLeftCrossingAt corridor hunique nextNext incoming ∨
          web.annular.RS.edgeAdjacencyGraph.Adj
            (web.annular.RS.edgeOf dart)
            (sourceLocalLayerLeftCrossingAt corridor hunique nextNext
              incoming) := by
        rw [hbaseEq]
        exact hrelBase
      have hsuc :=
        sourceLocalLayerSerialCellRebase_history_eq_or_adj_nextLeft_succ_eq
          graphData minimal caps coloring web corridor hunique next hnextNext
            prior (by
              simp only [next, sourceLocalLayerNextOffset_val]
              omega)
            (web.annular.RS.edgeOf dart) hhistory incoming
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
      have hbaseEq : sourceLocalLayerSharedRungAt corridor hunique nextNext =
          web.annular.RS.edgeOf base := by
        simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next, nextNext] using hrole
      have hrelTarget : web.annular.RS.edgeOf dart =
            sourceLocalLayerSharedRungAt corridor hunique nextNext ∨
          web.annular.RS.edgeAdjacencyGraph.Adj
            (web.annular.RS.edgeOf dart)
            (sourceLocalLayerSharedRungAt corridor hunique nextNext) := by
        rw [hbaseEq]
        exact hrelBase
      have hsuc :=
        sourceLocalLayerSerialCellRebase_history_eq_or_adj_nextCenterEdge_succ_eq
          graphData minimal caps coloring web corridor hunique next hnextNext
            prior (by
              simp only [next, sourceLocalLayerNextOffset_val]
              omega)
            (web.annular.RS.edgeOf dart)
            (sourceLocalLayerSharedRungAt corridor hunique nextNext) hhistory
            hrootFace
            (by simpa [nextNext] using hrelTarget)
      simp only [next, sourceLocalLayerNextOffset_val] at hsuc
      omega

/-- Every active dart of the following forty-eight-coordinate interaction
carrier is already named by the current interaction carrier. -/
theorem sourceLocalLayerSerialCellRebase_activeNextFaceInteraction_mem_currentFaceInteraction
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
    (dart : web.annular.RS.D)
    (htarget : dart ∈
      sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext)
    (hactive : dart ∈
      (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
        offset hnext).support) :
    dart ∈ sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
      hunique offset hnext := by
  let next := sourceLocalLayerNextOffset offset hnext
  change dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique next ∪
        sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique next
          hnextNext at htarget
  rw [Finset.mem_union] at htarget
  rcases htarget with htransition | hcollar
  · exact sourceLocalLayerSerialCellRebase_activeFaceTarget_mem_uniform
      graphData minimal caps coloring web corridor hunique offset hnext dart
        (by simpa [next] using htransition) hactive
  · rcases (SimpleGraph.mem_support _).1 hactive with ⟨other, hadj⟩
    have hregion : web.annular.RS.edgeOf dart ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique next :=
      hadj.2.2.1
    rw [sourceLocalLayerSerialTerminalInputRegionAt, Finset.mem_union] at hregion
    rcases hregion with hinput | hrung
    · rw [sourceLocalLayerSerialInputRegionAt, Finset.mem_union] at hinput
      rcases hinput with hprefix | hcrossing
      · rw [sourceLocalLayerSerialPrefixRegion, Finset.mem_biUnion] at hprefix
        rcases hprefix with ⟨prior, hprior, hhistory⟩
        have hpriorLt : prior.val < next.val := (Finset.mem_filter.mp hprior).2
        by_cases hstrict : prior.val < offset.val
        · exact
            sourceLocalLayerSerialCellRebase_strictHistory_nextFaceCollar_mem_currentFaceInteraction
              graphData minimal caps coloring web corridor hunique offset hnext
                hnextNext prior hstrict dart hhistory (by simpa [next] using hcollar)
        · have heq : prior = offset := by
            apply Fin.ext
            simp only [next, sourceLocalLayerNextOffset_val] at hpriorLt
            omega
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          exact (mem_dartsOnEdges_iff web.annular.RS _ dart).2 (heq ▸ hhistory)
      · rcases (mem_indexedCrossingEdgeSet_iff
            (sourceLocalLayerLeftCrossingAt corridor hunique next)
            (web.annular.RS.edgeOf dart)).1 hcrossing with ⟨step, hedge⟩
        apply Finset.mem_union_right
        apply sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
          corridor hunique offset hnext
        rw [mem_sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_iff]
        rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
        refine ⟨.inr (.inl step), ?_⟩
        simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next] using hedge
    · have hedge : web.annular.RS.edgeOf dart =
          sourceLocalLayerSharedRungAt corridor hunique next := by
        simpa using hrung
      apply Finset.mem_union_right
      apply sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
        corridor hunique offset hnext
      rw [mem_sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_iff]
      rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inr (.inr (0 : Fin 1)), ?_⟩
      simpa [sourceLocalLayerBoundaryRebaseEdgeAt, next] using hedge.symm

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingLocality

end Mettapedia.GraphTheory.FourColor
