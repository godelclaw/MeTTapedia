import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExecutableFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFullSuccessorState

/-!
# Positive literal Count witnesses have exact complete successors

The executable native factorization produces one literal Cell colouring from
every positive source `Count` entry and decides whether that Cell is compatible
with the accumulated prefix.  The uniform recurrence separately computes the
complete next cumulative state of the same source Cell--rebase step.  This file
joins those two results.

Thus a positive literal `Count` witness supplies both its exact left/right
profiles and an exact complete successor, while support remains the one finite
native compatibility test.  This is the source-realizable completeness joint.
It does not yet assert that an arbitrary accepted finite state/factor pair is
source-realizable, nor does it define or enumerate the reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellCountFullSuccessorFactorization

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellCountNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseExecutableFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFullSuccessorState
open GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorSkeleton
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellCountFullSuccessorFactorizationOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Every positive literal five-field `Count` entry produces a source Cell
whose profiles, finite acceptance test, and complete next cumulative state are
all exact. -/
theorem exists_executableNativeCellRebaseFullSuccessor_of_count_pos
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
      let cellColor := sourceLocalLayerCellLiteralColorAt caps coloring web
        corridor hunique offset cellColoring
      let hcell : ∀ {edge}, edge ∈
          sourceLocalLayerCellRegionAt corridor hunique offset →
            cellColor edge ≠ 0 :=
        sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web
          corridor hunique offset cellColoring
      pair.sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
          web.annular.cellulation.rotation boundary
          cellColoring.1 cellColoring.2 = left ∧
        pair.sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
          web.annular.cellulation.rotation boundary
          cellColoring.1 cellColoring.2 = right ∧
        (SourceLocalLayerSerialCellRebaseNativeSupportedAt graphData minimal caps
            coloring web corridor hunique offset hnext cellColor hcell ↔
          sourceLocalLayerSerialCellRebaseNativeCompatibleAt graphData minimal
            caps coloring web corridor hunique offset cellColor hcell = true) ∧
        sourceLocalLayerSerialCellRebaseUniformFullSuccessorStateAt graphData
            minimal caps coloring web corridor hunique offset hnext cellColor
              hcell =
          sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt graphData
            minimal caps coloring web corridor hunique offset hnext cellColor
              hcell := by
  rcases exists_executableNativeCellRebaseFactorization_of_count_pos graphData
      minimal caps coloring web corridor hunique offset hnext left right
      hpositive with
    ⟨cellColoring, hleft, hright, haccept⟩
  refine ⟨cellColoring, hleft, hright, haccept, ?_⟩
  exact sourceLocalLayerSerialCellRebaseUniformFullSuccessorStateAt_exact
    graphData minimal caps coloring web corridor hunique offset hnext
      (sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
        offset cellColoring)
      (sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web
        corridor hunique offset cellColoring)

end

end GoertzelV24ClosedWebLocalLayerSerialCellCountFullSuccessorFactorization

end Mettapedia.GraphTheory.FourColor
