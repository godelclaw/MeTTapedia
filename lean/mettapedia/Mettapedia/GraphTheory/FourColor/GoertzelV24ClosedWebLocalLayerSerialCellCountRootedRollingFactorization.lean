import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellCountFullSuccessorFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionExact

/-!
# Positive Count entries factor through the exact rooted rolling transition

The literal source `Count` supplies a positive Cell colouring, while the
rooted rolling exactness theorem turns every compatible such colouring into
one supported finite transition whose output is the literal next rooted state.
This file joins those two statements without changing either interface.

The compatibility premise is intentionally visible: a local positive `Count`
witness composes with a cumulative prefix precisely when their colours agree
on the actual overlap.  No arbitrary accepted finite factor is claimed to be
source-realizable here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellCountRootedRollingFactorization

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellCountFullSuccessorFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellCountNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransition
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionExact
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
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

local instance countRootedRollingFactorizationOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Every positive literal five-field `Count` entry, when compatible with the
accumulated prefix, is one supported step of the finite rooted transition and
lands on the exact rooted state of the spliced colouring at the next cut. -/
theorem exists_rootedRollingFactorization_of_count_pos
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
        (SourceLocalLayerSerialCellColorsCompatibleAt corridor hunique offset
            coloring cellColor →
          let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
            graphData minimal caps coloring web corridor hunique offset hnext
              coloring (fun _ ↦ web.tait _)
          let factor := sourceLocalLayerSerialRootedInteractionRollingCellFactorAt
            graphData minimal caps coloring web corridor hunique offset hnext
              hnextNext cellColor hcell
          let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique
            offset coloring cellColor
          let hrole : ∀ role, splice
              (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
                hnext role) ≠ 0 :=
            sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
              corridor hunique offset hnext cellColor hcell
          let hnextCrossing := successorCrossingNonzeroForColorAt corridor
            hunique offset hnext splice hrole
          factor.supportsBool state = true ∧
            factor.successor? state = some
              (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
                minimal caps coloring web corridor hunique
                  (sourceLocalLayerNextOffset offset hnext) hnextNext splice
                    hnextCrossing)) := by
  rcases exists_executableNativeCellRebaseFullSuccessor_of_count_pos graphData
      minimal caps coloring web corridor hunique offset hnext left right
      hpositive with
    ⟨cellColoring, hleft, hright, _hnative, _hfull⟩
  refine ⟨cellColoring, hleft, hright, ?_⟩
  intro hcompatible
  exact ⟨
    sourceLocalLayerSerialRootedInteractionRollingCellFactorAt_supportsBool
      graphData minimal caps coloring web corridor hunique offset hnext
        hnextNext
        (sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
          offset cellColoring)
        hcompatible
        (sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web
          corridor hunique offset cellColoring),
    sourceLocalLayerSerialRootedInteractionRollingCellFactorAt_successor_exact
      graphData minimal caps coloring web corridor hunique offset hnext
        hnextNext
        (sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
          offset cellColoring)
        hcompatible
        (sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web
          corridor hunique offset cellColoring)⟩

end

end GoertzelV24ClosedWebLocalLayerSerialCellCountRootedRollingFactorization

end Mettapedia.GraphTheory.FourColor
