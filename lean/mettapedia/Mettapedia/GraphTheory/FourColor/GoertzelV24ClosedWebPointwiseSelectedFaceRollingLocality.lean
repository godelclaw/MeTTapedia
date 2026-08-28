import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedRollingLocality

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

namespace GoertzelV24ClosedWebPointwiseSelectedFaceRollingLocality

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebPointwiseSelectedRollingHistoricalLocality
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCode
open GoertzelV24ClosedWebPointwiseSelectedRollingLocality
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorPointwiseRungs
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
theorem pointwiseSelectedSourceLocalLayerSerialCellRebase_strictHistory_nextFaceCollar_mem_currentFaceInteraction
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
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
    (dart : web.annular.RS.D)
    (hhistory : web.annular.RS.edgeOf dart ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor hinterior prior)
    (hcollar : dart ∈ pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt web.toFormation corridor
      hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext) :
    dart ∈ pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
      hinterior offset hnext := by
  let next := sourceLocalLayerNextOffset offset hnext
  let nextNext := sourceLocalLayerNextOffset next hnextNext
  rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt, Finset.mem_biUnion] at hcollar
  rcases hcollar with ⟨base, hbaseChanged, hdartNear⟩
  have hbaseSwitch : web.annular.RS.edgeOf base ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt web.toFormation corridor hinterior next hnextNext := by
    simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt, next] using
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
  rcases (mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff web.toFormation corridor hinterior next
      hnextNext (web.annular.RS.edgeOf base)).1 hbaseSwitch with ⟨role, hrole⟩
  rcases role with consumed | incomingOrSuccessor
  · have hbaseCurrentSwitch : web.annular.RS.edgeOf base ∈
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt web.toFormation corridor hinterior offset hnext := by
      rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inr (.inr (0 : Fin 1)), ?_⟩
      simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next] using hrole
    apply Finset.mem_union_right
    rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt, Finset.mem_biUnion]
    refine ⟨base, ?_, hdartNear⟩
    simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt] using
      hbaseCurrentSwitch
  · rcases incomingOrSuccessor with incoming | successor
    · have hbaseEq :
          pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation corridor hinterior nextNext incoming =
            web.annular.RS.edgeOf base := by
        simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next, nextNext] using hrole
      have hrelTarget : web.annular.RS.edgeOf dart =
            pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation corridor hinterior nextNext incoming ∨
          web.annular.RS.edgeAdjacencyGraph.Adj
            (web.annular.RS.edgeOf dart)
            (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation corridor hinterior nextNext
              incoming) := by
        rw [hbaseEq]
        exact hrelBase
      have hsuc :=
        pointwiseSelectedSourceLocalLayerSerialCellRebase_history_eq_or_adj_nextLeft_succ_eq
          graphData minimal caps coloring web corridor hinterior next hnextNext
            prior (by
              simp only [next, sourceLocalLayerNextOffset_val]
              omega)
            (web.annular.RS.edgeOf dart) hhistory incoming
            (by simpa [nextNext] using hrelTarget)
      simp only [next, sourceLocalLayerNextOffset_val] at hsuc
      omega
    · let skeleton :=
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      have hrootFace : pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation corridor hinterior nextNext ∈
          orbitFaceBoundary web.annular.RS
            (skeleton.faceAt
              (pointwiseSelectedSourceLocalLayerInteriorAt nextNext).center).1 := by
        simpa [pointwiseSelectedSourceLocalLayerSharedRungAt, skeleton] using
          pointwiseRungEdge_mem_left skeleton
            (boundaryCleanCorridor_consecutiveRungUnique web.annular hinterior
              corridor)
            (pointwiseSelectedSourceLocalLayerInteriorAt nextNext).outgoing
      have hbaseEq : pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation corridor hinterior nextNext =
          web.annular.RS.edgeOf base := by
        simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next, nextNext] using hrole
      have hrelTarget : web.annular.RS.edgeOf dart =
            pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation corridor hinterior nextNext ∨
          web.annular.RS.edgeAdjacencyGraph.Adj
            (web.annular.RS.edgeOf dart)
            (pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation corridor hinterior nextNext) := by
        rw [hbaseEq]
        exact hrelBase
      have hsuc :=
        pointwiseSelectedSourceLocalLayerSerialCellRebase_history_eq_or_adj_nextCenterEdge_succ_eq
          graphData minimal caps coloring web corridor hinterior next hnextNext
            prior (by
              simp only [next, sourceLocalLayerNextOffset_val]
              omega)
            (web.annular.RS.edgeOf dart)
            (pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation corridor hinterior nextNext) hhistory
            hrootFace
            (by simpa [nextNext] using hrelTarget)
      simp only [next, sourceLocalLayerNextOffset_val] at hsuc
      omega

/-- Every active dart of the following forty-eight-coordinate interaction
carrier is already named by the current interaction carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebase_activeNextFaceInteraction_mem_currentFaceInteraction
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (dart : web.annular.RS.D)
    (htarget : dart ∈
      pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext)
    (hactive : dart ∈
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor hinterior
        offset hnext).support) :
    dart ∈ pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
      hinterior offset hnext := by
  let next := sourceLocalLayerNextOffset offset hnext
  change dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior next ∪
        pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt web.toFormation corridor hinterior next
          hnextNext at htarget
  rw [Finset.mem_union] at htarget
  rcases htarget with htransition | hcollar
  · exact pointwiseSelectedSourceLocalLayerSerialCellRebase_activeFaceTarget_mem_uniform
      graphData minimal caps coloring web corridor hinterior offset hnext dart
        (by simpa [next] using htransition) hactive
  · rcases (SimpleGraph.mem_support _).1 hactive with ⟨other, hadj⟩
    have hregion : web.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior next :=
      hadj.2.2.1
    rw [pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt, Finset.mem_union] at hregion
    rcases hregion with hinput | hrung
    · rw [pointwiseSelectedSourceLocalLayerSerialInputRegionAt, Finset.mem_union] at hinput
      rcases hinput with hprefix | hcrossing
      · rw [pointwiseSelectedSourceLocalLayerSerialPrefixRegion, Finset.mem_biUnion] at hprefix
        rcases hprefix with ⟨prior, hprior, hhistory⟩
        have hpriorLt : prior.val < next.val := (Finset.mem_filter.mp hprior).2
        by_cases hstrict : prior.val < offset.val
        · exact
            pointwiseSelectedSourceLocalLayerSerialCellRebase_strictHistory_nextFaceCollar_mem_currentFaceInteraction
              graphData minimal caps coloring web corridor hinterior offset hnext
                hnextNext prior hstrict dart hhistory (by simpa [next] using hcollar)
        · have heq : prior = offset := by
            apply Fin.ext
            simp only [next, sourceLocalLayerNextOffset_val] at hpriorLt
            omega
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          exact (mem_dartsOnEdges_iff web.annular.RS _ dart).2 (heq ▸ hhistory)
      · rcases (mem_indexedCrossingEdgeSet_iff
            (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation corridor hinterior next)
            (web.annular.RS.edgeOf dart)).1 hcrossing with ⟨step, hedge⟩
        apply Finset.mem_union_right
        apply pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
          web.toFormation corridor hinterior offset hnext
        rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt,
          mem_dartsOnEdges_iff]
        rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
        refine ⟨.inr (.inl step), ?_⟩
        simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next] using hedge
    · have hedge : web.annular.RS.edgeOf dart =
          pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation corridor hinterior next := by
        simpa using hrung
      apply Finset.mem_union_right
      apply pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
        web.toFormation corridor hinterior offset hnext
      rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt,
        mem_dartsOnEdges_iff]
      rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inr (.inr (0 : Fin 1)), ?_⟩
      simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt, next] using hedge.symm

end

end GoertzelV24ClosedWebPointwiseSelectedFaceRollingLocality

end Mettapedia.GraphTheory.FourColor

