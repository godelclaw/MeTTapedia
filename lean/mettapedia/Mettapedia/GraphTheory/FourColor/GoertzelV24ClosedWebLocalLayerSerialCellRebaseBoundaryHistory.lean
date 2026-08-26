import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseBoundaryReduction

/-!
# Reduce promoted facial rebase occurrences to strict history

A dart which is regionally present immediately before a Cell rebase comes
from the strict cumulative prefix, the current literal Cell, or the consumed
rung.  If it is absent from the old rolling facial carrier, the current-Cell
case is impossible.  The consumed-rung case is already boundary-local.

Consequently every still-open successor-collar locality obligation is a
strict historical-alias obligation.  This is an exact decomposition of the
source region; it adds no locality assumption.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseBoundaryHistoryEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- A pre-rebase dart missing from the old rolling facial carrier comes from
either a strict historical Cell or the explicitly consumed rung.  The current
Cell alternative is impossible because all darts over its edges are old
coordinates. -/
theorem sourceLocalLayerSerialCellRebase_present_not_old_history_or_consumedRung
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (dart : web.annular.RS.D)
    (hpresent : web.annular.RS.edgeOf dart ∈
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    (hnew : dart ∉
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset) :
    (∃ prior : Fin (blockLength - 3),
        prior.val < offset.val ∧
          web.annular.RS.edgeOf dart ∈
            sourceLocalLayerCellRegionAt corridor hunique prior) ∨
      web.annular.RS.edgeOf dart =
        sourceLocalLayerSharedRungAt corridor hunique offset := by
  rw [sourceLocalLayerSerialPreRebaseOutputRegionAt, Finset.mem_union] at hpresent
  rcases hpresent with houtput | hrung
  · rw [sourceLocalLayerSerialOutputRegionAt,
      sourceLocalLayerSerialPrefixRegion_succ corridor hunique offset.isLt,
      Finset.mem_union] at houtput
    rcases houtput with hhistory | hcurrent
    · left
      rw [sourceLocalLayerSerialPrefixRegion, Finset.mem_biUnion] at hhistory
      rcases hhistory with ⟨prior, hprior, hedge⟩
      exact ⟨prior, (Finset.mem_filter.mp hprior).2, hedge⟩
    · exfalso
      apply hnew
      apply Finset.mem_union_left
      rw [mem_dartsOnEdges_iff]
      exact hcurrent
  · right
    simpa using hrung

/-- Once strict historical aliases have an old facial neighbour, every
genuinely promoted pre-rebase dart has one: the only other case is the
consumed rung, discharged by the literal two-hexagon geometry. -/
theorem sourceLocalLayerSerialCellRebase_exists_oldNeighbor_of_history
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (dart : web.annular.RS.D)
    (hhistory : ∀ prior : Fin (blockLength - 3),
      prior.val < offset.val →
      web.annular.RS.edgeOf dart ∈
          sourceLocalLayerCellRegionAt corridor hunique prior →
        ∃ oldDart : {dart // dart ∈
            sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset},
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset)).Adj oldDart.1 dart)
    (hpresent : web.annular.RS.edgeOf dart ∈
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    (hnew : dart ∉
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset) :
    ∃ oldDart : {dart // dart ∈
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset},
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        ).Adj oldDart.1 dart := by
  rcases
      sourceLocalLayerSerialCellRebase_present_not_old_history_or_consumedRung
        corridor hunique offset dart hpresent hnew with
    ⟨prior, hprior, hedge⟩ | hrung
  · exact hhistory prior hprior hedge
  · exact sourceLocalLayerSerialCellRebase_sharedRung_exists_oldNeighbor
      corridor hunique offset dart hrung hpresent hnew

/-- The complete forty-eight-slot boundary-locality theorem has only one
remaining source-geometric input: a represented dart which aliases a strict
historical Cell has an old facial neighbour.  Current-Cell darts and the
consumed rung are discharged internally. -/
theorem sourceLocalLayerSerialCellRebase_expandedFace_boundaryLocal_of_history
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (hhistory : ∀
      (slot : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
      (dart : web.annular.RS.D),
      sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
          offset hnext hcell slot = some dart →
      ∀ prior : Fin (blockLength - 3),
        prior.val < offset.val →
        web.annular.RS.edgeOf dart ∈
            sourceLocalLayerCellRegionAt corridor hunique prior →
          ∃ oldDart : {dart // dart ∈
              sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
                offset},
            (faceRegionalDartGraph web.annular.RS
              (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
                offset)).Adj oldDart.1 dart) :
    ∀ slot dart,
      sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
          offset hnext hcell slot = some dart →
      web.annular.RS.edgeOf dart ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset →
      dart ∉ sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          offset →
      ∃ oldDart : {dart // dart ∈
          sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset},
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset)).Adj oldDart.1 dart := by
  intro slot dart hdecode hpresent hnew
  apply sourceLocalLayerSerialCellRebase_exists_oldNeighbor_of_history
    corridor hunique offset dart
  · intro prior hprior hedge
    exact hhistory slot dart hdecode prior hprior hedge
  · exact hpresent
  · exact hnew

/-- Boolean boundary locality for the literal occurrence state is therefore
reduced to the single strict-history proposition above. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_boundaryLocal_of_history
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (hhistory : ∀
      (slot : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
      (dart : web.annular.RS.D),
      sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
          offset hnext hcell slot = some dart →
      ∀ prior : Fin (blockLength - 3),
        prior.val < offset.val →
        web.annular.RS.edgeOf dart ∈
            sourceLocalLayerCellRegionAt corridor hunique prior →
          ∃ oldDart : {dart // dart ∈
              sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
                offset},
            (faceRegionalDartGraph web.annular.RS
              (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
                offset)).Adj oldDart.1 dart) :
    ∀ occurrence,
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
          hunique offset hnext hcell).promoted occurrence = true →
        ((sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
          hunique offset hnext hcell).oldNeighbor? occurrence).isSome := by
  rw [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_boundaryLocal_iff]
  exact sourceLocalLayerSerialCellRebase_expandedFace_boundaryLocal_of_history
    corridor hunique offset hnext hcell hhistory

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
