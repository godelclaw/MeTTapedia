import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSupportColorParametric
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellCountNativeFactorization

/-!
# Exact native factorization of one Cell followed by its boundary rebase

The source serial word alternates a physical Cell with a change of boundary
presentation.  Positive literal `Count` supplies the Cell colouring; the
cumulative prefix supplies the other side.  The exact splice is now fed to
both finite factors:

* the prefix-independent physical Cell factor reconstructs the zero-terminal
  pre-rebase profile;
* the bounded rebase collar consumes that very profile and decodes the next
  terminal-aware profile at the same spliced colouring.

Thus the shared endpoint is literal record equality, rather than an informal
agreement of displayed boundary colours.  This is source-sound factorization
of one alternating letter.  Reachable closure, source-realizability of every
finite code, and representative invariance remain separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization

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
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSupportColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellCountNativeFactorization
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

local instance cellRebaseNativeFactorizationOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A Cell colouring that is nonzero on the whole literal Cell makes the
prefix/Cell splice nonzero at all four roles of the following rebase. -/
theorem sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (cellColor : G.edgeSet -> Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0)
    (role : SourceLocalLayerBoundaryRebaseRole) :
    sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset coloring
        cellColor
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          role) ≠ 0 := by
  by_cases hedge :
      sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role ∈
        sourceLocalLayerCellRegionAt corridor hunique offset
  · rw [sourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem corridor
      hunique offset coloring cellColor hedge]
    exact hcell hedge
  · rw [sourceLocalLayerSerialCellSplicedColorAt]
    simp only [if_neg hedge]
    exact web.tait _

/-- The literal open-Cell `Count` witness is nonzero on every edge of its
actual Cell region, not merely on the two displayed outgoing crossings. -/
theorem sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem
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
    {edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (hedge : edge ∈ sourceLocalLayerCellRegionAt corridor hunique offset) :
    sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique offset
      cellColoring edge ≠ 0 := by
  let pair := (sourceLocalLayerPairAt corridor hunique offset)
    |>.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  have hregion :=
    pair.sourceCrosscutComplementBoundaryProfileData_regionEdges_subset
      web.annular.cellulation.rotation boundary
  apply pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary_ne_zero
    web.annular.cellulation.rotation boundary cellColoring.1 cellColoring.2
  apply hregion
  simpa [sourceLocalLayerCellRegionAt, pair, boundary] using hedge

/-- The exact finite statement that one physical Cell and its following
boundary rebase are both supported at a literal shared profile.  The Cell
nonzeroness witness is kept explicit because it is supplied by the positive
source `Count`, rather than by the finite code. -/
def SourceLocalLayerSerialCellRebaseNativeSupportedAt
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
        cellColor edge ≠ 0) : Prop :=
  let hcross : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := fun step => hcell
          (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
            step)
  let factored := sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
    graphData minimal caps coloring web corridor hunique offset cellColor hcross
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      corridor hunique offset hnext cellColor hcell
  let rebase := finiteBoolSupportLetterForColorAt corridor hunique offset hnext
    factored.2.1 splice hrole
  SourceLocalLayerSerialCellPhysicalSupportsBool factored.1 factored.2.1
      factored.2.2 = true ∧
    rebase.input = factored.2.1 ∧
    SourceLocalLayerBoundaryRebaseFiniteSupportsBool rebase = true

/-- For any compatible nonzero Cell colouring, the physical Cell and the
following rebase are simultaneously supported and meet at exactly the same
pre-rebase profile. -/
theorem sourceLocalLayerSerialCell_and_boundaryRebase_supports
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
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) :
    SourceLocalLayerSerialCellRebaseNativeSupportedAt graphData minimal caps
      coloring web corridor hunique offset hnext cellColor hcell := by
  unfold SourceLocalLayerSerialCellRebaseNativeSupportedAt
  dsimp only
  refine ⟨sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt_supports
    graphData minimal caps coloring web corridor hunique offset cellColor
      hcompatible _, rfl, ?_⟩
  exact finiteBoolSupportLetterForColorAt_supports corridor hunique offset hnext
    _ _ _

/-- Every compatible positive literal five-field `Count` entry therefore
factors through one physical Cell and one supported rebase with a literal
shared endpoint. -/
theorem exists_nativeCellRebaseFactorization_of_count_pos
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
      pair.sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
          web.annular.cellulation.rotation boundary
          cellColoring.1 cellColoring.2 = left ∧
        pair.sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
          web.annular.cellulation.rotation boundary
          cellColoring.1 cellColoring.2 = right ∧
        (SourceLocalLayerSerialCellColorsCompatibleAt corridor hunique offset
            coloring cellColor →
          SourceLocalLayerSerialCellRebaseNativeSupportedAt graphData minimal
            caps coloring web corridor hunique offset hnext cellColor
              (sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring
                web corridor hunique offset cellColoring)) := by
  rcases exists_physicalBoolFactoredLetter_of_count_pos graphData minimal caps
    coloring web corridor hunique offset left right hpositive with
      ⟨cellColoring, hleft, hright, _⟩
  refine ⟨cellColoring, hleft, hright, ?_⟩
  intro hcompatible
  exact sourceLocalLayerSerialCell_and_boundaryRebase_supports graphData
    minimal caps coloring web corridor hunique offset hnext
      (sourceLocalLayerCellLiteralColorAt caps coloring web corridor hunique
        offset cellColoring) hcompatible
      (sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web
        corridor hunique offset cellColoring)

end

end GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization

end Mettapedia.GraphTheory.FourColor
