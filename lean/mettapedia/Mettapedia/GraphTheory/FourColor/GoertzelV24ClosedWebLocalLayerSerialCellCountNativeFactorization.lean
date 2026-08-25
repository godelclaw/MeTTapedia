import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerLiteralCountTrackedAdequacy
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization

/-!
# Every compatible positive Count witness has a physical native Cell factor

The literal manuscript `Count` is an existence count over open-Cell Tait
colourings.  A positive entry therefore supplies a local colouring that need
not be the ambient prefix colouring.  This file turns every such witness into
the prefix-independent native Cell factor of the preceding module.

Compatibility with the cumulative prefix remains explicit and load-bearing.
Subject to that exact overlap condition, the reconstructed five-field Cell
transition is accepted by the executable support predicate.  No particular
positive entry is privileged, and no prefix-specialized seam table is stored
inside the physical Cell factor.

This is the Cell half of the source's alternating Cell--boundary-rebase
transition.  Generalizing the following rebase from the ambient colouring to
this arbitrary compatible splice remains a separate obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellCountNativeFactorization

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerLiteralCountTrackedAdequacy
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance countNativeFactorizationOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Extend one literal open-Cell colouring to the ambient opened carrier by
reading its colour on the complementary vertex-side region and returning zero
off that region. -/
noncomputable def sourceLocalLayerCellLiteralColorAt
    (caps : OrientedFacialPentagonCapPair (G := G) graphData)
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
    caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color :=
  let pair := (sourceLocalLayerPairAt corridor hunique offset)
    |>.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
    web.annular.cellulation.rotation boundary cellColoring.1

/-- The two outgoing crossings of a literal Count witness carry nonzero
colours, as required to form its exact zero-terminal output profile. -/
theorem sourceLocalLayerCellLiteralColorAt_rightCrossing_ne_zero
    (caps : OrientedFacialPentagonCapPair (G := G) graphData)
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
    (step : Fin 2) :
    sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique offset
        cellColoring
        (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠ 0 := by
  let pair := (sourceLocalLayerPairAt corridor hunique offset)
    |>.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  apply pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary_ne_zero
    web.annular.cellulation.rotation boundary cellColoring.1 cellColoring.2
  apply pair.sourceCrosscutComplementBoundaryProfileData_regionEdges_subset
    web.annular.cellulation.rotation boundary
  simpa [sourceLocalLayerCellRegionAt, pair, boundary] using
    sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset step

/-- Every positive literal five-coordinate `Count` entry supplies a physical
native Cell factor.  Whenever the supplied Cell colouring agrees with the
cumulative prefix on their actual overlap, applying that factor reconstructs
a supported five-field transition. -/
theorem exists_physicalBoolFactoredLetter_of_count_pos
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
      let cellColor := sourceLocalLayerCellLiteralColorAt caps coloring web
        corridor hunique offset cellColoring
      pair.sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
          web.annular.cellulation.rotation boundary
          cellColoring.1 cellColoring.2 = left ∧
        pair.sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
          web.annular.cellulation.rotation boundary
          cellColoring.1 cellColoring.2 = right ∧
        (SourceLocalLayerSerialCellColorsCompatibleAt corridor hunique offset
            coloring cellColor →
          let factored :=
            sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData
              minimal caps coloring web corridor hunique offset cellColor
              (sourceLocalLayerCellLiteralColorAt_rightCrossing_ne_zero caps
                coloring web corridor hunique offset cellColoring)
          SourceLocalLayerSerialCellPhysicalSupportsBool factored.1 factored.2.1
            factored.2.2 = true) := by
  let pair := (sourceLocalLayerPairAt corridor hunique offset)
    |>.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  have hexists :=
    (pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff
      web.annular.cellulation.rotation boundary left right).1 hpositive
  rcases hexists with ⟨cellColoring, hleft, hright⟩
  refine ⟨cellColoring, hleft, hright, ?_⟩
  intro hcompatible
  exact sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt_supports
    graphData minimal caps coloring web corridor hunique offset
    (sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
      offset cellColoring) hcompatible
    (sourceLocalLayerCellLiteralColorAt_rightCrossing_ne_zero caps coloring web
      corridor hunique offset cellColoring)

end

end GoertzelV24ClosedWebLocalLayerSerialCellCountNativeFactorization

end Mettapedia.GraphTheory.FourColor
