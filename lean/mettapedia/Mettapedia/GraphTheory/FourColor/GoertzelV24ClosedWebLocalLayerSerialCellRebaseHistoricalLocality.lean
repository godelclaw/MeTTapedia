import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseHistoricalCollarRelation

/-!
# Localize strict-history contact with the successor incoming portals

The expanded facial decoder reduces a new collar coordinate to an edge which
is equal or adjacent to one of the literal rebase edges.  For a successor
incoming crossing, that relation can only come from the immediately preceding
Cell.  Earlier Cells are excluded by the induced corridor geometry.

This statement treats both kinds of historical Cell edge.  A boundary edge is
one of the four named crossings.  The unique internal bond is converted to a
boundary crossing using the literal two-vertex Cell geometry, after which the
same corridor-separation argument applies.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellRebaseHistoricalLocality

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseLocality
open GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
open GoertzelV24FacialPentagonCap
open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance historicalLocalityOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- If an edge of a strict historical Cell is equal or adjacent to a
successor incoming crossing, that historical Cell is the immediate
predecessor. -/
theorem sourceLocalLayerSerialCellRebase_history_eq_or_adj_nextLeft_succ_eq
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
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (prior : Fin (blockLength - 3))
    (hprior : prior.val < offset.val)
    (edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (hhistory : edge ∈ sourceLocalLayerCellRegionAt corridor hunique prior)
    (newStep : Fin 2)
    (hrel : edge = sourceLocalLayerLeftCrossingAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext) newStep ∨
      web.annular.RS.edgeAdjacencyGraph.Adj edge
        (sourceLocalLayerLeftCrossingAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext) newStep)) :
    prior.val + 1 = offset.val := by
  let priorSide := sourceLocalLayerCellVertexSide corridor hunique
    (sourceLocalLayerInteriorAt prior)
    (sourceLocalLayerInteriorAt_hasNext prior)
  by_cases hcrossing : edge ∈
      vertexSetCrossingEdges web.annular.RS priorSide
  · rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique
        prior (by simpa [priorSide] using hcrossing) with
      ⟨oldStep, hedge⟩ | ⟨oldStep, hedge⟩
    · exfalso
      apply not_sourceLocalLayerLeftCrossingAt_eq_or_adj_nextLeftCrossing_of_lt
        web corridor hunique offset prior hnext hprior oldStep newStep
      simpa [hedge] using hrel
    · apply
        sourceLocalLayerRightCrossingAt_succ_eq_of_lt_of_eq_or_adj_nextLeftCrossing
          web corridor hunique offset prior hnext hprior oldStep newStep
      simpa [hedge] using hrel
  · rcases hrel with heq | hadj
    · rcases exists_sourceLocalLayerRightCrossingAt_mem_cellCrossing
          graphData minimal caps coloring web corridor hunique prior with
        ⟨oldStep, holdCrossing⟩
      have holdAdj := internalEdge_adj_crossingEdge graphData minimal caps
        coloring web corridor hunique prior hhistory
          (by simpa [priorSide] using hcrossing) holdCrossing
      apply
        sourceLocalLayerRightCrossingAt_succ_eq_of_lt_of_eq_or_adj_nextLeftCrossing
          web corridor hunique offset prior hnext hprior oldStep newStep
      exact Or.inr (by simpa [heq] using holdAdj.symm)
    · have hnextCrossing := crossingEdge_of_internalEdge_adj graphData
        minimal caps coloring web corridor hunique prior hhistory
          (by simpa [priorSide] using hcrossing) hadj
      rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique
          prior hnextCrossing with ⟨oldStep, hedge⟩ | ⟨oldStep, hedge⟩
      · exfalso
        apply
          not_sourceLocalLayerLeftCrossingAt_eq_or_adj_nextLeftCrossing_of_lt
            web corridor hunique offset prior hnext hprior oldStep newStep
        exact Or.inl hedge.symm
      · apply
          sourceLocalLayerRightCrossingAt_succ_eq_of_lt_of_eq_or_adj_nextLeftCrossing
            web corridor hunique offset prior hnext hprior oldStep newStep
        exact Or.inl hedge.symm

/-- After decoding a genuinely new strict-history collar occurrence, the
successor-incoming role can only be supplied by the immediate predecessor.
The two rung roles remain explicit for their separate local arguments. -/
theorem sourceLocalLayerSerialCellRebase_strictHistory_collar_role_localized
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
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (slot : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (dart : web.annular.RS.D)
    (hdecode : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell slot = some dart)
    (prior : Fin (blockLength - 3))
    (hprior : prior.val < offset.val)
    (hhistory : web.annular.RS.edgeOf dart ∈
      sourceLocalLayerCellRegionAt corridor hunique prior)
    (hnew : dart ∉
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset) :
    ∃ occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor
        hunique offset hnext,
      ∃ direction : SourceLocalLayerSerialCellRebaseFaceCollarDirection,
        dart = sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
            occurrence.1 direction ∧
          (web.annular.RS.edgeOf occurrence.1 =
              sourceLocalLayerSharedRungAt corridor hunique offset ∨
            (∃ step : Fin 2,
              web.annular.RS.edgeOf occurrence.1 =
                  sourceLocalLayerLeftCrossingAt corridor hunique
                    (sourceLocalLayerNextOffset offset hnext) step ∧
                prior.val + 1 = offset.val) ∨
            web.annular.RS.edgeOf occurrence.1 =
              sourceLocalLayerSharedRungAt corridor hunique
                (sourceLocalLayerNextOffset offset hnext)) ∧
          (web.annular.RS.edgeOf dart = web.annular.RS.edgeOf occurrence.1 ∨
            web.annular.RS.edgeAdjacencyGraph.Adj
              (web.annular.RS.edgeOf dart)
              (web.annular.RS.edgeOf occurrence.1)) := by
  rcases sourceLocalLayerSerialCellRebase_strictHistory_collar_relation
      corridor hunique offset hnext hcell slot dart hdecode prior hprior
        hhistory hnew with
    ⟨occurrence, direction, hdart, hrole, hrel⟩
  refine ⟨occurrence, direction, hdart, ?_, hrel⟩
  rcases hrole with hconsumed | ⟨step, hincoming⟩ | hsuccessor
  · exact Or.inl hconsumed
  · refine Or.inr (Or.inl ⟨step, hincoming, ?_⟩)
    apply sourceLocalLayerSerialCellRebase_history_eq_or_adj_nextLeft_succ_eq
      graphData minimal caps coloring web corridor hunique offset hnext prior
        hprior (web.annular.RS.edgeOf dart) hhistory step
    rw [← hincoming]
    exact hrel
  · exact Or.inr (Or.inr hsuccessor)

end

end GoertzelV24ClosedWebLocalLayerSerialCellRebaseHistoricalLocality

end Mettapedia.GraphTheory.FourColor
