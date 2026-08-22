import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerLiteralCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialPrefixRegion
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementLiteralSerialSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleChain

/-!
# Literal serial support for an actual opened-source Cell

The source word is heterogeneous: every corridor position contributes its
own literal complementary Cell morphism.  This file gives one such Cell the
common `Fin 2` boundary coordinates and proves that positivity of its exact
five-coordinate `Count` entry supplies color support on that same serial
tangle.

The theorem is one-way and retains the complete profiles in its premise.  It
does not identify a cumulative-prefix carrier with an iterated tagged serial
composite, and it does not replace the five profile fields by boundary colors.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24CorridorTransferWord
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OpenTangleComposition
open GoertzelV24RotationCutDartDecomposition
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerLiteralSerialTangleEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- One actual complementary source Cell with both literal boundaries
coordinatized by the common two-position corridor interface. -/
noncomputable def sourceLocalLayerCoordinatizedComplementTangle
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    CoordinatizedTwoSidedOpenTangle (Fin 2) := by
  let layers := sourceLocalLayerPair corridor hunique leftInterior hnext
  let pair := layers.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  have hleft : 2 = pair.left.walk.length := by
    simp [pair, layers, LocalLayerPair.separatedLocalLayerPair,
      LocalLayerPair.firstLayer, LocalLayerPair.firstWalk]
  have hright : 2 = pair.right.walk.length := by
    simp [pair, layers, LocalLayerPair.separatedLocalLayerPair,
      LocalLayerPair.secondLayer, LocalLayerPair.secondWalk]
  exact {
    V := { vertex : V // vertex ∉ pair.componentSide boundary.component }
    I := InternalDart web.annular.RS
      (fun vertex => vertex ∉ pair.componentSide boundary.component)
    L := Fin pair.left.walk.length
    R := Fin pair.right.walk.length
    data := pair.sourceCrosscutComplementTwoSidedOpenTangleOfBoundary
      web.annular.cellulation.rotation boundary
    leftCoordinate := finCongr hleft
    rightCoordinate := finCongr hright }

/-- The boundary-color projection of the common bounded literal profile. -/
def sourceLocalLayerCellBoundedProfileColorWord
    (profile : SourceLocalLayerCellBoundedProfile) : Fin 2 → Color :=
  fun step => (profile.profile.edgeColor step).toColor

/-- A positive exact five-coordinate entry for one actual source Cell is
supported by a Tait coloring of that same Cell's coordinatized serial tangle. -/
theorem sourceLocalLayerCoordinatizedComplementTangle_accepts_of_count_pos
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (left right : SourceLocalLayerCellProfile corridor hunique
      leftInterior hnext)
    (hpositive :
      let pair :=
        (sourceLocalLayerPair corridor hunique leftInterior hnext)
          |>.separatedLocalLayerPair hunique
      let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
        leftInterior hnext
      0 < pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary
        web.annular.cellulation.rotation boundary left right) :
    (sourceLocalLayerCoordinatizedComplementTangle corridor hunique
      leftInterior hnext).AcceptsBoundaryWords
        (sourceLocalLayerCellBoundedProfileColorWord
          (sourceLocalLayerCellProfileCode corridor hunique
            leftInterior hnext left))
        (sourceLocalLayerCellBoundedProfileColorWord
          (sourceLocalLayerCellProfileCode corridor hunique
            leftInterior hnext right)) := by
  let layers := sourceLocalLayerPair corridor hunique leftInterior hnext
  let pair := layers.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  rcases pair.exists_serialColoring_of_complementLiteralOpenProfileCountOfBoundary_pos
      web.annular.cellulation.rotation boundary left right hpositive with
    ⟨serialColoring, hserial, hleftWord, hrightWord⟩
  unfold CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords
  change
    (pair.sourceCrosscutComplementTwoSidedOpenTangleOfBoundary
      web.annular.cellulation.rotation boundary).AcceptsBoundaryWords _ _
  refine ⟨serialColoring, hserial, ?_, ?_⟩
  · rw [hleftWord]
    funext step
    rfl
  · rw [hrightWord]
    funext step
    rfl

/-- The common bounded literal transfer projects to support of the exact
coordinatized Cell morphism. -/
theorem sourceLocalLayerCellBoundedProfileTransfer_projects_to_tangleSupport
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (left right : SourceLocalLayerCellBoundedProfile)
    (htransfer : sourceLocalLayerCellBoundedProfileTransfer corridor hunique
      leftInterior hnext left right) :
    (sourceLocalLayerCoordinatizedComplementTangle corridor hunique
      leftInterior hnext).AcceptsBoundaryWords
        (sourceLocalLayerCellBoundedProfileColorWord left)
        (sourceLocalLayerCellBoundedProfileColorWord right) := by
  rcases htransfer with
    ⟨leftRaw, rightRaw, hleft, hright, hpositive⟩
  rw [← hleft, ← hright]
  exact sourceLocalLayerCoordinatizedComplementTangle_accepts_of_count_pos
    corridor hunique leftInterior hnext leftRaw rightRaw hpositive

/-- The actual heterogeneous word of literal five-coordinate Cell supports,
in source order. -/
noncomputable def sourceLocalLayerCellBoundedProfileTransferWord
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    List (SourceLocalLayerCellBoundedProfile →
      SourceLocalLayerCellBoundedProfile → Prop) :=
  List.ofFn fun offset =>
    sourceLocalLayerCellBoundedProfileTransfer corridor hunique
      (sourceLocalLayerInteriorAt offset)
      (sourceLocalLayerInteriorAt_hasNext offset)

/-- The same source-ordered word read as literal coordinatized open tangles. -/
noncomputable def sourceLocalLayerCoordinatizedComplementTangles
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    List (CoordinatizedTwoSidedOpenTangle (Fin 2)) :=
  List.ofFn fun offset =>
    sourceLocalLayerCoordinatizedComplementTangle corridor hunique
      (sourceLocalLayerInteriorAt offset)
      (sourceLocalLayerInteriorAt_hasNext offset)

private theorem forall₂_ofFn
    {α β : Type*} {relation : α → β → Prop} {n : Nat}
    (left : Fin n → α) (right : Fin n → β)
    (hpointwise : ∀ offset, relation (left offset) (right offset)) :
    List.Forall₂ relation (List.ofFn left) (List.ofFn right) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact List.Forall₂.cons (hpointwise 0)
        (ih (fun offset => left offset.succ) (fun offset => right offset.succ)
          (fun offset => hpointwise offset.succ))

/-- Every exact source letter projects pointwise to support of the same
literal open tangle.  No homogeneous alphabet or orientation quotient is
used. -/
theorem sourceLocalLayerCellBoundedProfileTransferWord_projects_to_tangleSupport
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    List.Forall₂
      (fun profileStep colorStep =>
        ∀ left right, profileStep left right →
          colorStep
            (sourceLocalLayerCellBoundedProfileColorWord left)
            (sourceLocalLayerCellBoundedProfileColorWord right))
      (sourceLocalLayerCellBoundedProfileTransferWord corridor hunique)
      ((sourceLocalLayerCoordinatizedComplementTangles corridor hunique).map
        CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords) := by
  unfold sourceLocalLayerCellBoundedProfileTransferWord
    sourceLocalLayerCoordinatizedComplementTangles
  rw [List.map_ofFn]
  apply forall₂_ofFn
  intro offset left right htransfer
  exact sourceLocalLayerCellBoundedProfileTransfer_projects_to_tangleSupport
    corridor hunique (sourceLocalLayerInteriorAt offset)
      (sourceLocalLayerInteriorAt_hasNext offset) left right htransfer

/-- A path through the exact heterogeneous five-coordinate source word gives
an exact color-support path through the corresponding literal tangle word. -/
theorem exactTransferWord_sourceLocalLayerCellBoundedProfileTransferWord_projects
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    {left right : SourceLocalLayerCellBoundedProfile}
    (hpath : ExactTransferWord
      (sourceLocalLayerCellBoundedProfileTransferWord corridor hunique)
      left right) :
    ExactTransferWord
      ((sourceLocalLayerCoordinatizedComplementTangles corridor hunique).map
        CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords)
      (sourceLocalLayerCellBoundedProfileColorWord left)
      (sourceLocalLayerCellBoundedProfileColorWord right) :=
  CoordinatizedTwoSidedOpenTangle.exactTransferWord_map_of_forall₂
    sourceLocalLayerCellBoundedProfileColorWord
    (sourceLocalLayerCellBoundedProfileTransferWord_projects_to_tangleSupport
      corridor hunique) hpath

@[simp]
theorem sourceLocalLayerCoordinatizedComplementTangles_length
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    (sourceLocalLayerCoordinatizedComplementTangles corridor hunique).length =
      blockLength - 3 := by
  simp [sourceLocalLayerCoordinatizedComplementTangles]

/-- The nonempty literal source word assembled as one heterogeneous serial
open tangle. -/
noncomputable def sourceLocalLayerComplementSerialComposite
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hcells : 0 < blockLength - 3) :
    CoordinatizedTwoSidedOpenTangle (Fin 2) := by
  let cells := sourceLocalLayerCoordinatizedComplementTangles corridor hunique
  have hcellsNe : cells ≠ [] := by
    intro hempty
    have hlength : cells.length = 0 := by rw [hempty]; rfl
    have hsourceLength : cells.length = blockLength - 3 := by
      exact sourceLocalLayerCoordinatizedComplementTangles_length
        corridor hunique
    omega
  exact CoordinatizedTwoSidedOpenTangle.composeNonempty
    (cells.head hcellsNe) cells.tail

/-- An exact path through the actual five-coordinate heterogeneous source
word colors its literal serial composite at the projected exterior words. -/
theorem sourceLocalLayerComplementSerialComposite_accepts_of_exactProfilePath
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hcells : 0 < blockLength - 3)
    {left right : SourceLocalLayerCellBoundedProfile}
    (hpath : ExactTransferWord
      (sourceLocalLayerCellBoundedProfileTransferWord corridor hunique)
      left right) :
    (sourceLocalLayerComplementSerialComposite corridor hunique hcells
      ).AcceptsBoundaryWords
        (sourceLocalLayerCellBoundedProfileColorWord left)
        (sourceLocalLayerCellBoundedProfileColorWord right) := by
  let cells := sourceLocalLayerCoordinatizedComplementTangles corridor hunique
  have hcellsNe : cells ≠ [] := by
    intro hempty
    have hlength : cells.length = 0 := by rw [hempty]; rfl
    have hsourceLength : cells.length = blockLength - 3 := by
      exact sourceLocalLayerCoordinatizedComplementTangles_length
        corridor hunique
    omega
  change
    (CoordinatizedTwoSidedOpenTangle.composeNonempty
      (cells.head hcellsNe) cells.tail).AcceptsBoundaryWords _ _
  rw [CoordinatizedTwoSidedOpenTangle.composeNonempty_acceptsBoundaryWords_iff_exactTransferWord]
  have hcons : cells.head hcellsNe :: cells.tail = cells :=
    List.cons_head_tail hcellsNe
  have hsupport :
      CoordinatizedTwoSidedOpenTangle.supportWord
          (cells.head hcellsNe) cells.tail =
        cells.map CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords := by
    change CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords
        (cells.head hcellsNe) ::
        cells.tail.map CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords =
      cells.map CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords
    exact congrArg
      (List.map CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords) hcons
  rw [hsupport]
  exact exactTransferWord_sourceLocalLayerCellBoundedProfileTransferWord_projects
    corridor hunique hpath

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
