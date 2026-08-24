import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerLiteralCountWitness
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier

/-!
# Tracked local adequacy of a positive literal Cell `Count`

The literal source-Cell `Count` ranges over every Tait coloring of the actual
open Cell, whereas the first executable tracked code was read from the one
ambient coloring already carried by a closed web.  This file removes that
asymmetry on the Cell factor.

Every positive entry of the literal five-coordinate `Count` supplies its own
open-Cell coloring.  Reading that coloring back onto the complementary
vertex-side region gives a six-slot finite graph-family code, and the code
preserves complete reachability for all three tracked color pairs.

This is deliberately local adequacy.  It does not yet glue the Count witness
to an arbitrary accumulated-prefix witness across their common seam, and it
does not claim that the resulting Cell factor alone is the cumulative
one-step transition.  Those are the next serial-composition obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerLiteralCountTrackedAdequacy

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A six-slot tracked-family code read from an arbitrary literal open-Cell
Tait coloring.  Its four distinguished points are the two incoming followed
by the two outgoing source crossings. -/
noncomputable def sourceLocalLayerCellLiteralTrackedFamilyCodeAt
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
    (cellColoring : SourceLocalLayerCellLiteralOpenTaitColoring corridor
      hunique (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)) :
    BoundedCarrierGraphFamilyCode 6 4 TrackedColorPair :=
  let pair := (sourceLocalLayerPairAt corridor hunique offset)
    |>.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  let localColor :=
    pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
      web.annular.cellulation.rotation boundary cellColoring.1
  boundedCarrierGraphFamilyCode
    (sourceLocalLayerCellRegionAt corridor hunique offset) 6 4
    (sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps coloring
      web corridor hunique offset)
    (sourceLocalLayerCellPortAt corridor hunique offset)
    (fun trackedPair =>
      regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerCellRegionAt corridor hunique offset) localColor
        (trackedColorPairColors trackedPair).1
        (trackedColorPairColors trackedPair).2)

private theorem literalTrackedGraph_support_subset_cellRegion
    (graphData : Data G)
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
    (cellColoring : SourceLocalLayerCellLiteralOpenTaitColoring corridor
      hunique (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset))
    (trackedPair : TrackedColorPair) :
    let pair := (sourceLocalLayerPairAt corridor hunique offset)
      |>.separatedLocalLayerPair hunique
    let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
    let localColor :=
      pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
        web.annular.cellulation.rotation boundary cellColoring.1
    (regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerCellRegionAt corridor hunique offset) localColor
      (trackedColorPairColors trackedPair).1
      (trackedColorPairColors trackedPair).2).support ⊆
        (sourceLocalLayerCellRegionAt corridor hunique offset : Set _) := by
  dsimp only
  intro edge hedge
  rcases hedge with ⟨neighbor, hadj⟩
  exact hadj.2.1

/-- The code read from an arbitrary positive-Count witness preserves the
complete tracked reachability relation on the literal Cell region. -/
theorem sourceLocalLayerCellLiteralTrackedFamilyCodeAt_reachable_iff
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
    (cellColoring : SourceLocalLayerCellLiteralOpenTaitColoring corridor
      hunique (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset))
    (trackedPair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset}) :
    ((sourceLocalLayerCellLiteralTrackedFamilyCodeAt graphData minimal caps
      coloring web corridor hunique offset cellColoring).graph trackedPair).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      let pair := (sourceLocalLayerPairAt corridor hunique offset)
        |>.separatedLocalLayerPair hunique
      let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
      let localColor :=
        pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
          web.annular.cellulation.rotation boundary cellColoring.1
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerCellRegionAt corridor hunique offset) localColor
        (trackedColorPairColors trackedPair).1
        (trackedColorPairColors trackedPair).2).Reachable first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceLocalLayerCellRegionAt corridor hunique offset) 6 4
    (sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps coloring
      web corridor hunique offset)
    (sourceLocalLayerCellPortAt corridor hunique offset) _ trackedPair
    (literalTrackedGraph_support_subset_cellRegion graphData caps coloring web
      corridor hunique offset cellColoring trackedPair) first second

/-- Every positive literal five-coordinate `Count` entry supplies an actual
open-Cell coloring and therefore a finite tracked code for that witness.  The
two displayed profiles are exactly the requested matrix indices. -/
theorem exists_literalTrackedFamilyCode_of_count_pos
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
    (left right : SourceLocalLayerCellProfile corridor hunique
      (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset))
    (hpositive :
      let pair := (sourceLocalLayerPairAt corridor hunique offset)
        |>.separatedLocalLayerPair hunique
      let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
      0 < pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary
        web.annular.cellulation.rotation boundary left right) :
    ∃ cellColoring : SourceLocalLayerCellLiteralOpenTaitColoring corridor
        hunique (sourceLocalLayerInteriorAt offset)
          (sourceLocalLayerInteriorAt_hasNext offset),
      let pair := (sourceLocalLayerPairAt corridor hunique offset)
        |>.separatedLocalLayerPair hunique
      let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
      pair.sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
          web.annular.cellulation.rotation boundary
          cellColoring.1 cellColoring.2 = left ∧
        pair.sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
          web.annular.cellulation.rotation boundary
          cellColoring.1 cellColoring.2 = right ∧
        ∀ trackedPair first second,
          ((sourceLocalLayerCellLiteralTrackedFamilyCodeAt graphData minimal caps
            coloring web corridor hunique offset cellColoring).graph
              trackedPair).Reachable
              (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
            let localColor :=
              pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
                web.annular.cellulation.rotation boundary cellColoring.1
            (regionalTrackedEdgeGraph web.annular.RS
              (sourceLocalLayerCellRegionAt corridor hunique offset) localColor
              (trackedColorPairColors trackedPair).1
              (trackedColorPairColors trackedPair).2).Reachable first.1 second.1 := by
  let pair := (sourceLocalLayerPairAt corridor hunique offset)
    |>.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  rcases (pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff
      web.annular.cellulation.rotation boundary left right).1 hpositive with
    ⟨cellColoring, hleft, hright⟩
  refine ⟨cellColoring, hleft, hright, ?_⟩
  intro trackedPair first second
  exact sourceLocalLayerCellLiteralTrackedFamilyCodeAt_reachable_iff
    graphData minimal caps coloring web corridor hunique offset cellColoring
      trackedPair first second

end

end GoertzelV24ClosedWebLocalLayerLiteralCountTrackedAdequacy

end Mettapedia.GraphTheory.FourColor
