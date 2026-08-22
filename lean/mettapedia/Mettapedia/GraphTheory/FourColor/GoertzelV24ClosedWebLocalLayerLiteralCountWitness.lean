import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerLiteralCount

/-!
# The ambient source coloring witnesses literal one-Cell `Count` support

The finite successor packet and the literal one-Cell `Count` describe the
same physical source Cell only after the latter is known to be inhabited by
the restriction of the ambient coloring.  This file constructs that literal
open coloring and proves that its two exact full profiles form a positive
entry of the already-defined heterogeneous `Count` matrix.

This is the validation direction from an actual source corridor into its
local support letter.  It does not yet identify the local two-boundary
profiles with the cumulative predecessor and successor packets, assert a
deterministic update, or bound the heterogeneous reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebComputedDepthProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OpenRegionTaitInheritance
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerLiteralCountWitnessEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The boundary-rooted literal open-coloring carrier for one source Cell. -/
abbrev SourceLocalLayerCellLiteralOpenTaitColoring
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :=
  let pair :=
    (sourceLocalLayerPair corridor hunique leftInterior hnext)
      |>.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  pair.SourceCrosscutComplementLiteralOpenTaitColoringOfBoundary
    web.annular.cellulation.rotation boundary

/-- Restrict the ambient source coloring to the literal complementary Cell
bounded by the two selected local crosscuts. -/
noncomputable def sourceLocalLayerCellInheritedOpenTaitColoring
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    SourceLocalLayerCellLiteralOpenTaitColoring corridor hunique
      leftInterior hnext := by
  let pair :=
    (sourceLocalLayerPair corridor hunique leftInterior hnext)
      |>.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  exact ⟨inheritedColoring web.annular.RS
      (fun vertex => vertex ∉ pair.componentSide boundary.component)
      (pair.sourceCrosscutComplementRootOfBoundary
        web.annular.cellulation.rotation boundary)
      (rotationColoringOfGraph web.annular coloring),
    inheritedColoring_isTait web.annular.RS
      (fun vertex => vertex ∉ pair.componentSide boundary.component)
      (pair.sourceCrosscutComplementRootOfBoundary
        web.annular.cellulation.rotation boundary)
      (rotationColoringOfGraph web.annular coloring)
      (rotationColoringOfGraph_isTait web.annular coloring web.tait)⟩

/-- The left exact local profile computed by the inherited Cell coloring. -/
noncomputable def sourceLocalLayerCellInheritedLeftProfile
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    SourceLocalLayerCellProfile corridor hunique leftInterior hnext :=
  let pair :=
    (sourceLocalLayerPair corridor hunique leftInterior hnext)
      |>.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  let cellColoring := sourceLocalLayerCellInheritedOpenTaitColoring corridor
    hunique leftInterior hnext
  pair.sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
    web.annular.cellulation.rotation boundary cellColoring.1 cellColoring.2

/-- The right exact local profile computed by the inherited Cell coloring. -/
noncomputable def sourceLocalLayerCellInheritedRightProfile
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    SourceLocalLayerCellProfile corridor hunique leftInterior hnext :=
  let pair :=
    (sourceLocalLayerPair corridor hunique leftInterior hnext)
      |>.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  let cellColoring := sourceLocalLayerCellInheritedOpenTaitColoring corridor
    hunique leftInterior hnext
  pair.sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
    web.annular.cellulation.rotation boundary cellColoring.1 cellColoring.2

/-- The actual ambient source Cell contributes a positive entry to its
literal five-coordinate `Count` matrix. -/
theorem sourceLocalLayerCellLiteralCount_pos_of_ambientColoring
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    let pair :=
      (sourceLocalLayerPair corridor hunique leftInterior hnext)
        |>.separatedLocalLayerPair hunique
    let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
      leftInterior hnext
    0 < pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary
      web.annular.cellulation.rotation boundary
      (sourceLocalLayerCellInheritedLeftProfile corridor hunique
        leftInterior hnext)
      (sourceLocalLayerCellInheritedRightProfile corridor hunique
        leftInterior hnext) := by
  let pair :=
    (sourceLocalLayerPair corridor hunique leftInterior hnext)
      |>.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  let cellColoring := sourceLocalLayerCellInheritedOpenTaitColoring corridor
    hunique leftInterior hnext
  rw [pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff]
  exact ⟨cellColoring, rfl, rfl⟩

/-- The same actual Cell inhabits the common finite support relation.  This
is the exact positive-`Count` letter, not a relation invented from the one
chosen ambient coloring. -/
theorem sourceLocalLayerCellBoundedProfileTransfer_of_ambientColoring
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    sourceLocalLayerCellBoundedProfileTransfer corridor hunique
      leftInterior hnext
      (sourceLocalLayerCellProfileCode corridor hunique leftInterior hnext
        (sourceLocalLayerCellInheritedLeftProfile corridor hunique
          leftInterior hnext))
      (sourceLocalLayerCellProfileCode corridor hunique leftInterior hnext
        (sourceLocalLayerCellInheritedRightProfile corridor hunique
          leftInterior hnext)) := by
  rw [sourceLocalLayerCellBoundedProfileTransfer_code_iff]
  exact sourceLocalLayerCellLiteralCount_pos_of_ambientColoring corridor
    hunique leftInterior hnext

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
