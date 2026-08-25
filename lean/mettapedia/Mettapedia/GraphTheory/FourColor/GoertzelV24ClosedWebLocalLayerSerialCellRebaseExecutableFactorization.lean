import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization

/-!
# Executable acceptance of one source Cell--rebase factor

The exact native factorization previously retained proof-facing colour
compatibility as an implication premise.  The finite cumulative state and the
physical Cell factor already contain the two partial colour tables needed to
decide that premise.  This file makes their Boolean comparison the complete
acceptance condition for a literal source Cell followed by its boundary
rebase.

For every positive five-field source `Count`, Lean therefore produces an
exact finite Cell--rebase candidate whose support is equivalent to one native
twenty-one-slot test.  This removes the last external premise from one
alternating letter.  It does not claim that every arbitrary supported code is
source-realizable, enumerate initial states, or compute a reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellRebaseExecutableFactorization

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerLiteralCountTrackedAdequacy
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellCountNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedBoolColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization
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

local instance cellRebaseExecutableFactorizationOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The native acceptance bit for a literal Cell at one accumulated prefix.
All inputs are fields of the finite cumulative state or the physical Cell
factor extracted from the source witness. -/
def sourceLocalLayerSerialCellRebaseNativeCompatibleAt
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) : Bool :=
  let hcross : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := fun step => hcell
          (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
            step)
  let factored := sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
    graphData minimal caps coloring web corridor hunique offset cellColor hcross
  SourceLocalLayerSerialCarrierColorsCompatibleBool factored.1.colorCode
    factored.2.2.trackedCellColor

/-- For a literal source Cell, complete Cell--rebase support is equivalent to
the native partial-colour compatibility bit.  The rebase tail itself is always
supported; the bit records exactly whether the Cell can be spliced onto the
given cumulative prefix. -/
theorem sourceLocalLayerSerialCellRebaseNativeSupportedAt_iff_compatible
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
    SourceLocalLayerSerialCellRebaseNativeSupportedAt graphData minimal caps
        coloring web corridor hunique offset hnext cellColor hcell ↔
      sourceLocalLayerSerialCellRebaseNativeCompatibleAt graphData minimal caps
        coloring web corridor hunique offset cellColor hcell = true := by
  let hcross : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := fun step => hcell
          (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
            step)
  let factored := sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
    graphData minimal caps coloring web corridor hunique offset cellColor hcross
  constructor
  · intro hsupported
    have hphysical : SourceLocalLayerSerialCellPhysicalSupportsBool factored.1
        factored.2.1 factored.2.2 = true := by
      simpa [SourceLocalLayerSerialCellRebaseNativeSupportedAt, hcross,
        factored] using hsupported.1
    change (SourceLocalLayerSerialCarrierColorsCompatibleBool
      factored.1.colorCode factored.2.2.trackedCellColor && _) = true at hphysical
    rw [Bool.and_eq_true] at hphysical
    simpa [sourceLocalLayerSerialCellRebaseNativeCompatibleAt, hcross,
      factored] using hphysical.1
  · intro hfinite
    have hcode : SourceLocalLayerSerialCarrierColorsCompatible
        factored.1.colorCode factored.2.2.trackedCellColor :=
      (sourceLocalLayerSerialCarrierColorsCompatibleBool_eq_true_iff _ _).1
        (by simpa [sourceLocalLayerSerialCellRebaseNativeCompatibleAt, hcross,
          factored] using hfinite)
    have hactual : SourceLocalLayerSerialCellColorsCompatibleAt corridor hunique
        offset coloring cellColor := by
      apply (sourceLocalLayerSerialCarrierColorsCompatible_iff graphData minimal
        caps coloring web corridor hunique offset cellColor).1
      simpa [factored, hcross,
        sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt] using hcode
    exact sourceLocalLayerSerialCell_and_boundaryRebase_supports graphData
      minimal caps coloring web corridor hunique offset hnext cellColor hactual
        hcell

/-- Every positive literal five-field `Count` entry yields an exact native
Cell--rebase candidate whose complete support is decided by the finite
compatibility bit. -/
theorem exists_executableNativeCellRebaseFactorization_of_count_pos
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
            caps coloring web corridor hunique offset cellColor hcell = true) := by
  rcases exists_physicalBoolFactoredLetter_of_count_pos graphData minimal caps
    coloring web corridor hunique offset left right hpositive with
      ⟨cellColoring, hleft, hright, _⟩
  refine ⟨cellColoring, hleft, hright, ?_⟩
  exact sourceLocalLayerSerialCellRebaseNativeSupportedAt_iff_compatible
    graphData minimal caps coloring web corridor hunique offset hnext
      (sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
        offset cellColoring)
      (sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web
        corridor hunique offset cellColoring)

end

end GoertzelV24ClosedWebLocalLayerSerialCellRebaseExecutableFactorization

end Mettapedia.GraphTheory.FourColor
