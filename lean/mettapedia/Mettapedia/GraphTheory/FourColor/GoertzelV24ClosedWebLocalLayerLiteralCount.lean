import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerFiniteTrackedLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfileOfBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryProfileFiniteState

/-!
# Literal five-coordinate `Count` for an actual opened-source Cell

The source-local Cell pair now has a boundary package constructed on the
actual opened annulus, whose global rotation system is deliberately not
cubic.  The boundary-rooted profile API lets that literal complementary Cell
carry its own exact `Count` matrix anyway.

This file transports that matrix to the common width-two, zero-terminal,
eight-fragment carrier.  Its positive support is heterogeneous in the actual
Cell and contains all five manuscript profile coordinates.  It is not yet the
cumulative prefix update: relating the Cell's two local profiles to the old
and new cumulative cut profiles remains the next factorization theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerLiteralCountEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The exact dependent full-profile carrier on either boundary of one
literal source-local Cell. -/
abbrev SourceLocalLayerCellProfile
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :=
  let pair :=
    (sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
      hunique
  pair.SourceCrosscutComplementInterfaceProfile
    web.annular.cellulation.rotation
    (sourceLocalLayerPairCrosscutBoundaryData corridor hunique
      leftInterior hnext)

/-- The common finite carrier for every actual source-local Cell profile.
The bound eight is occurrence-sensitive and keeps the complete five fields. -/
abbrev SourceLocalLayerCellBoundedProfile :=
  BoundedCorridorCutProfile 2 0 8

/-- The actual complementary Cell has at most eight boundary-local face
fragments.  This uses its literal four-edge wall and no global cubicity. -/
theorem sourceLocalLayerCell_faceFragmentCount_le_eight
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    let pair :=
      (sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique
    pair.sourceCrosscutComplementFaceFragmentCount
        web.annular.cellulation.rotation
        (sourceLocalLayerPairCrosscutBoundaryData corridor hunique
          leftInterior hnext) ≤ 8 := by
  let layers := sourceLocalLayerPair corridor hunique leftInterior hnext
  let pair := layers.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  let inside := (pair.componentSide boundary.component)ᶜ
  change Fintype.card (BoundaryRegionalFragment web.annular.RS
      (vertexSetCrossingEdges web.annular.RS inside)
      (vertexSetRegionEdges web.annular.RS inside)) ≤ 8
  calc
    Fintype.card (BoundaryRegionalFragment web.annular.RS
        (vertexSetCrossingEdges web.annular.RS inside)
        (vertexSetRegionEdges web.annular.RS inside)) ≤
        2 * Fintype.card (VertexSetCrossingEdge web.annular.RS inside) :=
      vertexSetBoundaryGraphCutData_fragmentCount_le_two_mul_crossingPortCount_of_dartOccurrences
        web.annular.RS inside
    _ = 8 := by
      have hcard : Fintype.card (VertexSetCrossingEdge web.annular.RS inside) =
          pair.left.walk.length + pair.right.walk.length := by
        simpa [inside] using
          (Fintype.card_congr
            (pair.sourceCrosscutComplementPort
              web.annular.cellulation.rotation boundary)).symm
      rw [hcard]
      simp [pair, layers, LocalLayerPair.separatedLocalLayerPair,
        LocalLayerPair.firstLayer, LocalLayerPair.secondLayer,
        LocalLayerPair.firstWalk, LocalLayerPair.secondWalk]

/-- Faithfully embed one exact actual-Cell profile in the common finite
carrier.  Only the dependent fragment-count packaging changes. -/
noncomputable def sourceLocalLayerCellProfileCode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (profile : SourceLocalLayerCellProfile corridor hunique
      leftInterior hnext) :
    SourceLocalLayerCellBoundedProfile := by
  refine {
    faceFragmentCount := ⟨_, Nat.lt_succ_of_le
      (sourceLocalLayerCell_faceFragmentCount_le_eight
        corridor hunique leftInterior hnext)⟩
    profile := ?_ }
  let layers := sourceLocalLayerPair corridor hunique leftInterior hnext
  let pair := layers.separatedLocalLayerPair hunique
  have hwidth : pair.left.walk.length = 2 := by
    simp [pair, layers, LocalLayerPair.separatedLocalLayerPair,
      LocalLayerPair.firstLayer, LocalLayerPair.firstWalk]
  rw [← hwidth]
  exact profile

/-- The common-carrier encoding cannot identify two distinct actual full
profiles. -/
theorem sourceLocalLayerCellProfileCode_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Function.Injective (sourceLocalLayerCellProfileCode corridor hunique
      leftInterior hnext) := by
  intro left right heq
  dsimp only [sourceLocalLayerCellProfileCode] at heq
  injection heq

/-- Positive support of the literal actual-Cell `Count`, transported to the
common bounded carrier.  Distinct source Cells remain distinct letters. -/
noncomputable def sourceLocalLayerCellBoundedProfileTransfer
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (left right : SourceLocalLayerCellBoundedProfile) : Prop :=
  let pair :=
    (sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
      hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  ∃ leftRaw rightRaw : SourceLocalLayerCellProfile corridor hunique
      leftInterior hnext,
    sourceLocalLayerCellProfileCode corridor hunique leftInterior hnext leftRaw =
        left ∧
      sourceLocalLayerCellProfileCode corridor hunique leftInterior hnext rightRaw =
        right ∧
      0 < pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary
        web.annular.cellulation.rotation boundary leftRaw rightRaw

/-- The actual source-local transfer remains a decidable finite relation. -/
noncomputable instance instDecidableRelSourceLocalLayerCellBoundedProfileTransfer
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    DecidableRel (sourceLocalLayerCellBoundedProfileTransfer corridor hunique
      leftInterior hnext) := by
  classical
  intro left right
  unfold sourceLocalLayerCellBoundedProfileTransfer
  infer_instance

/-- On encoded profiles, the bounded relation is exactly positivity of the
literal boundary-rooted `Count` entry. -/
theorem sourceLocalLayerCellBoundedProfileTransfer_code_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (left right : SourceLocalLayerCellProfile corridor hunique
      leftInterior hnext) :
    sourceLocalLayerCellBoundedProfileTransfer corridor hunique
        leftInterior hnext
        (sourceLocalLayerCellProfileCode corridor hunique leftInterior hnext left)
        (sourceLocalLayerCellProfileCode corridor hunique leftInterior hnext right) ↔
      let pair :=
        (sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
          hunique
      let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
        leftInterior hnext
      0 < pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary
        web.annular.cellulation.rotation boundary left right := by
  constructor
  · rintro ⟨leftRaw, rightRaw, hleft, hright, hpositive⟩
    have hleftRaw : leftRaw = left :=
      sourceLocalLayerCellProfileCode_injective corridor hunique
        leftInterior hnext hleft
    have hrightRaw : rightRaw = right :=
      sourceLocalLayerCellProfileCode_injective corridor hunique
        leftInterior hnext hright
    simpa only [hleftRaw, hrightRaw] using hpositive
  · intro hpositive
    exact ⟨left, right, rfl, rfl, hpositive⟩

/-- Concrete source semantics: an encoded transition holds exactly when one
literal Tait coloring of the actual complementary Cell realizes its two full
profiles. -/
theorem sourceLocalLayerCellBoundedProfileTransfer_code_iff_exists_coloring
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (left right : SourceLocalLayerCellProfile corridor hunique
      leftInterior hnext) :
    sourceLocalLayerCellBoundedProfileTransfer corridor hunique
        leftInterior hnext
        (sourceLocalLayerCellProfileCode corridor hunique leftInterior hnext left)
        (sourceLocalLayerCellProfileCode corridor hunique leftInterior hnext right) ↔
      let pair :=
        (sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
          hunique
      let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
        leftInterior hnext
      ∃ cellColoring :
          pair.SourceCrosscutComplementLiteralOpenTaitColoringOfBoundary
            web.annular.cellulation.rotation boundary,
        pair.sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
            web.annular.cellulation.rotation boundary
            cellColoring.1 cellColoring.2 = left ∧
          pair.sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
            web.annular.cellulation.rotation boundary
            cellColoring.1 cellColoring.2 = right := by
  rw [sourceLocalLayerCellBoundedProfileTransfer_code_iff]
  exact (sourceLocalLayerPair corridor hunique leftInterior hnext
      |>.separatedLocalLayerPair hunique
      |>.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff
        web.annular.cellulation.rotation
        (sourceLocalLayerPairCrosscutBoundaryData corridor hunique
          leftInterior hnext) left right)

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
