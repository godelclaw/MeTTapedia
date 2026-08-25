import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellInternalOverlap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport

/-!
# Localize strict historical Cell overlap at one rebase

The cumulative-prefix recurrence must know that an edge recurring from a
strict historical Cell into the successor transition carrier is already
visible in the bounded current Cell--rebase window.  This file closes that
geometric locality statement on the literal two-cap opened carrier.

Two elementary facts do the work.  The unique internal bond of a two-vertex
Cell is adjacent to every genuine boundary portal.  Conversely, no portal of
a strict historical Cell can equal or be adjacent to an outgoing portal of
the successor Cell: the two named incident corridor faces would violate the
geodesic separation of the clean corridor.  These facts reduce all mixed
internal/crossing cases to the already-proved internal/internal exclusion.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalFaceBoundaryAdjacency
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseLocality
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellInternalOverlap
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance serialCellPastOverlapOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The unique internal bond of a literal two-vertex Cell is adjacent to
every genuine boundary crossing of that Cell. -/
theorem internalEdge_adj_crossingEdge
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
    {internal boundary :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (hinternalRegion : internal ∈
      sourceLocalLayerCellRegionAt corridor hunique offset)
    (hinternalNotCrossing : internal ∉ vertexSetCrossingEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)))
    (hboundaryCrossing : boundary ∈ vertexSetCrossingEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset))) :
    web.annular.RS.edgeAdjacencyGraph.Adj internal boundary := by
  let side := sourceLocalLayerCellVertexSide corridor hunique
    (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)
  have hendpoints :=
    sourceLocalLayerCellRegionAt_internalEdge_endpoints_eq_side graphData
      minimal caps coloring web corridor hunique offset hinternalRegion
        hinternalNotCrossing
  rw [mem_vertexSetCrossingEdges_iff] at hboundaryCrossing
  rcases hboundaryCrossing with
    ⟨vertex, hvertexBoundary, hvertexSide, _outer, _houterBoundary,
      _houterOutside⟩
  apply (web.annular.RS.edgeAdjacencyGraph_adj_iff).2
  refine ⟨?_, vertex, ?_, hvertexBoundary⟩
  · intro heq
    subst boundary
    exact hinternalNotCrossing (by
      rw [mem_vertexSetCrossingEdges_iff]
      exact ⟨vertex, hvertexBoundary, hvertexSide, _outer,
        _houterBoundary, _houterOutside⟩)
  · rw [hendpoints]
    exact hvertexSide

/-- Any edge adjacent to a Cell's internal bond and meeting that bond at a
Cell vertex is a boundary crossing unless it is the bond itself.  The latter
case is excluded by irreflexivity of edge adjacency. -/
theorem crossingEdge_of_internalEdge_adj
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
    {internal neighbor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (hinternalRegion : internal ∈
      sourceLocalLayerCellRegionAt corridor hunique offset)
    (hinternalNotCrossing : internal ∉ vertexSetCrossingEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)))
    (hadj : web.annular.RS.edgeAdjacencyGraph.Adj internal neighbor) :
    neighbor ∈ vertexSetCrossingEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)) := by
  let side := sourceLocalLayerCellVertexSide corridor hunique
    (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)
  have hendpoints :=
    sourceLocalLayerCellRegionAt_internalEdge_endpoints_eq_side graphData
      minimal caps coloring web corridor hunique offset hinternalRegion
        hinternalNotCrossing
  have hregionEq : sourceLocalLayerCellRegionAt corridor hunique offset =
      vertexSetRegionEdges web.annular.RS side := by
    have hside := sourceLocalLayerCellVertexSide_eq_retained_compl
      corridor hunique (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)
    exact congrArg (vertexSetRegionEdges web.annular.RS) hside.symm
  rcases (web.annular.RS.edgeAdjacencyGraph_adj_iff).1 hadj with
    ⟨hne, vertex, hvertexInternal, hvertexNeighbor⟩
  have hneighborRegion : neighbor ∈
      sourceLocalLayerCellRegionAt corridor hunique offset := by
    rw [hregionEq, mem_vertexSetRegionEdges_iff]
    refine ⟨vertex, hvertexNeighbor, ?_⟩
    have hvertexSide : vertex ∈
        sourceLocalLayerCellVertexSide corridor hunique
          (sourceLocalLayerInteriorAt offset)
          (sourceLocalLayerInteriorAt_hasNext offset) := by
      rw [← hendpoints]
      exact hvertexInternal
    simpa [side] using hvertexSide
  by_contra hneighborNotCrossing
  have heq := sourceLocalLayerCellRegionAt_internalEdge_subsingleton graphData
    minimal caps coloring web corridor hunique offset hinternalRegion
      hinternalNotCrossing hneighborRegion hneighborNotCrossing
  exact hne heq

/-- A crossing of a strict historical Cell can neither coincide with nor
touch an outgoing crossing of the successor Cell.  Equality uses ordinary
two-face incidence; adjacency uses only local cubicity at the common vertex.
-/
theorem not_pastCellCrossing_eq_or_adj_nextRightCrossing
    (graphData : Data G)
    (_minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
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
    (prior : Fin (blockLength - 3))
    (hprior : prior.val < offset.val)
    {edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (holdCrossing : edge ∈ vertexSetCrossingEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        (sourceLocalLayerInteriorAt prior)
        (sourceLocalLayerInteriorAt_hasNext prior)))
    (newStep : Fin 2)
    (hrel : edge = sourceLocalLayerRightCrossingAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) newStep ∨
      web.annular.RS.edgeAdjacencyGraph.Adj edge
        (sourceLocalLayerRightCrossingAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext) newStep)) : False := by
  let target := sourceLocalLayerNextOffset offset hnext
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let newCenter :=
    (nextCorridorInterior (sourceLocalLayerInteriorAt target)
      (sourceLocalLayerInteriorAt_hasNext target)).center
  have hnewFace :
      sourceLocalLayerRightCrossingAt corridor hunique target newStep ∈
        orbitFaceBoundary web.annular.RS
          (skeleton.faceAt newCenter).1 := by
    simpa [newCenter, skeleton, target] using
      sourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary corridor
        hunique target newStep
  rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique prior
      holdCrossing with ⟨oldStep, hedge⟩ | ⟨oldStep, hedge⟩
  · let oldCenter := (sourceLocalLayerInteriorAt prior).center
    have holdFace : edge ∈ orbitFaceBoundary web.annular.RS
        (skeleton.faceAt oldCenter).1 := by
      rw [hedge]
      simpa [oldCenter, skeleton] using
        sourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary corridor hunique
          prior oldStep
    have hcentersNe : oldCenter ≠ newCenter := by
      intro hsame
      have hvalues := congrArg Fin.val hsame
      change prior.val + 1 = target.val + 2 at hvalues
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal] at hvalues
      omega
    have hfacesNe : (skeleton.faceAt oldCenter).1 ≠
        (skeleton.faceAt newCenter).1 := by
      intro hsame
      exact hcentersNe (skeleton.faceAt_injective (Subtype.ext hsame))
    have hfaceAdj :
        (interiorDualGraph (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
            ⟨(skeleton.faceAt oldCenter).1, Finset.mem_univ _⟩
            ⟨(skeleton.faceAt newCenter).1, Finset.mem_univ _⟩ := by
      rcases hrel with heq | hadj
      · apply
          interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
            (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))
            (orbitFace_incidence_le_two web.annular.RS) hfacesNe
              (by simpa [target, heq] using holdFace) hnewFace
      · exact interiorDualGraph_adj_of_edgeAdjacencyGraph_adj web hfacesNe
          holdFace hnewFace (by simpa [target] using hadj)
    have hseparated : oldCenter.val + 1 < newCenter.val := by
      change prior.val + 1 + 1 < target.val + 2
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal]
      omega
    exact (skeleton.separated_not_adjacent oldCenter newCenter hseparated)
      hfaceAdj
  · let oldCenter :=
      (nextCorridorInterior (sourceLocalLayerInteriorAt prior)
        (sourceLocalLayerInteriorAt_hasNext prior)).center
    have holdFace : edge ∈ orbitFaceBoundary web.annular.RS
        (skeleton.faceAt oldCenter).1 := by
      rw [hedge]
      simpa [oldCenter, skeleton] using
        sourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary corridor
          hunique prior oldStep
    have hcentersNe : oldCenter ≠ newCenter := by
      intro hsame
      have hvalues := congrArg Fin.val hsame
      change prior.val + 2 = target.val + 2 at hvalues
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal] at hvalues
      omega
    have hfacesNe : (skeleton.faceAt oldCenter).1 ≠
        (skeleton.faceAt newCenter).1 := by
      intro hsame
      exact hcentersNe (skeleton.faceAt_injective (Subtype.ext hsame))
    have hfaceAdj :
        (interiorDualGraph (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
            ⟨(skeleton.faceAt oldCenter).1, Finset.mem_univ _⟩
            ⟨(skeleton.faceAt newCenter).1, Finset.mem_univ _⟩ := by
      rcases hrel with heq | hadj
      · apply
          interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
            (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))
            (orbitFace_incidence_le_two web.annular.RS) hfacesNe
              (by simpa [target, heq] using holdFace) hnewFace
      · exact interiorDualGraph_adj_of_edgeAdjacencyGraph_adj web hfacesNe
          holdFace hnewFace (by simpa [target] using hadj)
    have hseparated : oldCenter.val + 1 < newCenter.val := by
      change prior.val + 2 + 1 < target.val + 2
      have htargetVal : target.val = offset.val + 1 := rfl
      rw [htargetVal]
      omega
    exact (skeleton.separated_not_adjacent oldCenter newCenter hseparated)
      hfaceAdj

/-- Every strict historical Cell edge that recurs in the successor transition
carrier is one of the four named rebase edges.  In particular, no unbounded
prefix history survives into the moving twenty-one-slot carrier. -/
theorem sourceLocalLayerSerialCellRebase_pastCellOverlap_mem_switch
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
    (hnext : offset.val + 1 < blockLength - 3) :
    ∀
      (targetEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique (sourceLocalLayerNextOffset offset hnext)})
      (prior : Fin (blockLength - 3)),
      prior.val < offset.val →
      targetEdge.1 ∈ sourceLocalLayerCellRegionAt corridor hunique prior →
        targetEdge.1 ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor
          hunique offset hnext := by
  intro targetEdge prior hprior hpriorRegion
  let target := sourceLocalLayerNextOffset offset hnext
  let priorSide := sourceLocalLayerCellVertexSide corridor hunique
    (sourceLocalLayerInteriorAt prior)
    (sourceLocalLayerInteriorAt_hasNext prior)
  let targetSide := sourceLocalLayerCellVertexSide corridor hunique
    (sourceLocalLayerInteriorAt target)
    (sourceLocalLayerInteriorAt_hasNext target)
  have htargetCarrier := targetEdge.property
  change targetEdge.1 ∈
      (sourceLocalLayerCellRegionAt corridor hunique target ∪
        sourceLocalLayerSerialOutgoingEdgeCarrierAt corridor hunique target) ∪
          {sourceLocalLayerSharedRungAt corridor hunique target} at htargetCarrier
  rw [Finset.mem_union] at htargetCarrier
  rcases htargetCarrier with htargetCore | htargetRung
  · rw [Finset.mem_union] at htargetCore
    rcases htargetCore with htargetCell | htargetOutgoing
    · by_cases htargetCrossing : targetEdge.1 ∈
          vertexSetCrossingEdges web.annular.RS targetSide
      · rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique
          target (by simpa [targetSide] using htargetCrossing) with
          ⟨newStep, htargetLeft⟩ | ⟨newStep, htargetRight⟩
        · rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
          refine ⟨.inr (.inl newStep), ?_⟩
          simpa [sourceLocalLayerBoundaryRebaseEdgeAt, target] using
            htargetLeft.symm
        · by_cases hpriorCrossing : targetEdge.1 ∈
              vertexSetCrossingEdges web.annular.RS priorSide
          · exact (not_pastCellCrossing_eq_or_adj_nextRightCrossing graphData
              minimal caps coloring web corridor hunique offset hnext prior
                hprior (by simpa [priorSide] using hpriorCrossing) newStep
                  (Or.inl (by simpa [target] using htargetRight))).elim
          · rcases exists_sourceLocalLayerRightCrossingAt_mem_cellCrossing
                graphData minimal caps coloring web corridor hunique prior with
              ⟨oldStep, holdCrossing⟩
            have hadj := internalEdge_adj_crossingEdge graphData minimal caps
              coloring web corridor hunique prior hpriorRegion
                (by simpa [priorSide] using hpriorCrossing) holdCrossing
            exact (not_pastCellCrossing_eq_or_adj_nextRightCrossing graphData
              minimal caps coloring web corridor hunique offset hnext prior
                hprior holdCrossing newStep
                  (Or.inr (by simpa [target, htargetRight] using hadj.symm))).elim
      · by_cases hpriorCrossing : targetEdge.1 ∈
            vertexSetCrossingEdges web.annular.RS priorSide
        · rcases exists_sourceLocalLayerRightCrossingAt_mem_cellCrossing
              graphData minimal caps coloring web corridor hunique target with
            ⟨newStep, hnewCrossing⟩
          have hadj := internalEdge_adj_crossingEdge graphData minimal caps
            coloring web corridor hunique target htargetCell
              (by simpa [targetSide] using htargetCrossing) hnewCrossing
          exact (not_pastCellCrossing_eq_or_adj_nextRightCrossing graphData
            minimal caps coloring web corridor hunique offset hnext prior
              hprior (by simpa [priorSide] using hpriorCrossing) newStep
                (Or.inr (by simpa [target] using hadj))).elim
        · exact (not_common_internalEdge_of_lt_next graphData minimal caps
            coloring web corridor hunique offset hnext prior hprior
              hpriorRegion (by simpa [priorSide] using hpriorCrossing)
                htargetCell (by simpa [targetSide, target] using
                  htargetCrossing)).elim
    · rcases (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff
          (indexedCrossingEdgeSet
            (sourceLocalLayerRightCrossingAt corridor hunique target))
          targetEdge.1).1 (by simpa [sourceLocalLayerSerialOutgoingEdgeCarrierAt,
            target] using htargetOutgoing) with htargetRight | htargetAdj
      · rcases (mem_indexedCrossingEdgeSet_iff
            (sourceLocalLayerRightCrossingAt corridor hunique target)
            targetEdge.1).1 htargetRight with ⟨newStep, htargetRightEq⟩
        by_cases hpriorCrossing : targetEdge.1 ∈
            vertexSetCrossingEdges web.annular.RS priorSide
        · exact (not_pastCellCrossing_eq_or_adj_nextRightCrossing graphData
            minimal caps coloring web corridor hunique offset hnext prior
              hprior (by simpa [priorSide] using hpriorCrossing) newStep
                (Or.inl (by simpa [target] using htargetRightEq.symm))).elim
        · rcases exists_sourceLocalLayerRightCrossingAt_mem_cellCrossing
              graphData minimal caps coloring web corridor hunique prior with
            ⟨oldStep, holdCrossing⟩
          have hadj := internalEdge_adj_crossingEdge graphData minimal caps
            coloring web corridor hunique prior hpriorRegion
              (by simpa [priorSide] using hpriorCrossing) holdCrossing
          exact (not_pastCellCrossing_eq_or_adj_nextRightCrossing graphData
            minimal caps coloring web corridor hunique offset hnext prior
              hprior holdCrossing newStep
                (Or.inr (by simpa [target, htargetRightEq] using hadj.symm))).elim
      · rcases htargetAdj with ⟨rightEdge, hrightEdge, hadj⟩
        rcases (mem_indexedCrossingEdgeSet_iff
            (sourceLocalLayerRightCrossingAt corridor hunique target)
            rightEdge).1 hrightEdge with ⟨newStep, hrightEq⟩
        by_cases hpriorCrossing : targetEdge.1 ∈
            vertexSetCrossingEdges web.annular.RS priorSide
        · exact (not_pastCellCrossing_eq_or_adj_nextRightCrossing graphData
            minimal caps coloring web corridor hunique offset hnext prior
              hprior (by simpa [priorSide] using hpriorCrossing) newStep
                (Or.inr (by simpa [target, hrightEq] using hadj))).elim
        · have hrightPriorCrossing := crossingEdge_of_internalEdge_adj graphData
            minimal caps coloring web corridor hunique prior hpriorRegion
              (by simpa [priorSide] using hpriorCrossing) hadj
          exact (not_pastCellCrossing_eq_or_adj_nextRightCrossing graphData
            minimal caps coloring web corridor hunique offset hnext prior
              hprior hrightPriorCrossing newStep
                (Or.inl (by simpa [target] using hrightEq.symm))).elim
  · have htargetRungEq : targetEdge.1 =
        sourceLocalLayerSharedRungAt corridor hunique target := by
      simpa using htargetRung
    rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
    refine ⟨.inr (.inr ⟨0, by omega⟩), ?_⟩
    simpa [sourceLocalLayerBoundaryRebaseEdgeAt, target] using htargetRungEq.symm

/-- Compatibility form of the historical-overlap theorem used by the earlier
carrier-transport API.  The first disjunct always holds; the weaker second
disjunct is retained only to avoid perturbing downstream consumers. -/
theorem sourceLocalLayerSerialCellRebase_pastCellOverlap
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
    (hnext : offset.val + 1 < blockLength - 3) :
    ∀
      (targetEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique (sourceLocalLayerNextOffset offset hnext)})
      (prior : Fin (blockLength - 3)),
      prior.val < offset.val →
      targetEdge.1 ∈ sourceLocalLayerCellRegionAt corridor hunique prior →
        targetEdge.1 ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor
            hunique offset hnext ∨
          targetEdge.1 ∈
            sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset := by
  intro targetEdge prior hprior hpriorRegion
  exact Or.inl
    (sourceLocalLayerSerialCellRebase_pastCellOverlap_mem_switch graphData
      minimal caps coloring web corridor hunique offset hnext targetEdge prior
        hprior hpriorRegion)

/-- An active edge of the next rolling carrier is already local in the exact
occurrence-sensitive sense needed by the facial recurrence: it is either one
of the four rebase edges or belongs to the current literal Cell.  The coarser
outgoing edge-adjacency neighborhood contributes no third case. -/
theorem sourceLocalLayerSerialCellRebase_activeTarget_mem_switch_or_currentCell
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
    (targetEdge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)})
    (hactive : targetEdge.1 ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)) :
    targetEdge.1 ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique
        offset hnext ∨
      targetEdge.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset := by
  by_cases hswitch : targetEdge.1 ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext
  · exact Or.inl hswitch
  have hpre : targetEdge.1 ∈
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset :=
    (sourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
      corridor hunique offset hnext targetEdge.1 hswitch).2 hactive
  rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor hunique
    offset, Finset.mem_union] at hpre
  rcases hpre with hold | hcell
  · rw [sourceLocalLayerSerialTerminalInputRegionAt, Finset.mem_union] at hold
    rcases hold with hinput | hrung
    · rw [sourceLocalLayerSerialInputRegionAt, Finset.mem_union] at hinput
      rcases hinput with hprefix | hcrossing
      · rw [sourceLocalLayerSerialPrefixRegion, Finset.mem_biUnion] at hprefix
        rcases hprefix with ⟨prior, hprior, hpriorCell⟩
        exact Or.inl
          (sourceLocalLayerSerialCellRebase_pastCellOverlap_mem_switch graphData
            minimal caps coloring web corridor hunique offset hnext targetEdge
              prior (Finset.mem_filter.mp hprior).2 hpriorCell)
      · rcases (mem_indexedCrossingEdgeSet_iff
            (sourceLocalLayerLeftCrossingAt corridor hunique offset)
            targetEdge.1).1 hcrossing with ⟨step, hedge⟩
        exact Or.inr (by
          rw [← hedge]
          exact sourceLocalLayerCellRegionAt_leftCrossing corridor hunique
            offset step)
    · apply Or.inl
      have hedge : targetEdge.1 =
          sourceLocalLayerSharedRungAt corridor hunique offset := by
        simpa using hrung
      rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
      refine ⟨.inl ⟨0, by omega⟩, ?_⟩
      simpa [sourceLocalLayerBoundaryRebaseEdgeAt] using hedge.symm
  · exact Or.inr hcell

/-- The exact cumulative colour recurrence is unconditional on the literal
two-cap source carrier: the former `pastCellOverlap` premise is discharged by
the geometric localization theorem above. -/
theorem sourceLocalLayerSerialCellRebaseTransportedColorCodeAt_eq_target_unconditional
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
    sourceLocalLayerSerialCellRebaseTransportedColorCodeAt graphData minimal
        caps coloring web corridor hunique offset hnext cellColor hcell =
      sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique (sourceLocalLayerNextOffset offset hnext)
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          coloring cellColor) := by
  apply
    sourceLocalLayerSerialCellRebaseTransportedColorCodeAt_eq_target_of_pastCellOverlap
  exact sourceLocalLayerSerialCellRebase_pastCellOverlap graphData minimal caps
    coloring web corridor hunique offset hnext

end

end GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap

end Mettapedia.GraphTheory.FourColor
