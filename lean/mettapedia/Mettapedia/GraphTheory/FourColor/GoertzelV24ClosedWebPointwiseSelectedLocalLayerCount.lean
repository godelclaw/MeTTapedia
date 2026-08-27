import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedLocalLayerBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalComplementCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryProfileFiniteState

/-!
# Exact Count of a colouring-free literal Cell

The corrected local Cell is a `Formation.LocalLayerPair`.  Its two facial
rails carry pointwise-selected primal crossings, so the complete boundary and
the literal open-tangle `Count` require only the restricted interior-face
receipt.  No ambient colouring and no globally unique shared-edge hypothesis
enters this module.

The dependent exact profile is embedded faithfully in the established common
width-two, zero-terminal, eight-fragment carrier consumed by the finite Cell
transition.  Positivity of the transported relation is exactly existence of
one literal Tait colouring realizing the two selected boundary profiles.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SelectedDualPathTransversal
open GoertzelV24SelectedDualPathTransversal.SeparatedAlignedSelectedDualTransversals
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace Formation.LocalLayerPair

/-- A fixed canonical witness of the complete selected boundary.  All later
definitions use this same witness, so their dependent profile carriers agree
definitionally. -/
noncomputable def pointwiseSelectedSourceBoundaryData
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    SourceSelectedBoundaryData formation.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior) :=
  Classical.choice
    (layers.exists_pointwiseSelectedSourceBoundaryData hinterior)

/-- The exact dependent five-field profile carrier on either selected
boundary of one literal Cell. -/
abbrev PointwiseSelectedSourceLocalLayerCellProfile
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :=
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  pair.SourceSelectedComplementInterfaceProfile
    formation.annular.cellulation.rotation
    (layers.pointwiseSelectedSourceBoundaryData hinterior)

/-- Common finite carrier for all literal width-two Cell profiles. -/
abbrev PointwiseSelectedSourceLocalLayerCellBoundedProfile :=
  BoundedCorridorCutProfile 2 0 8

/-- The selected literal Cell has four boundary ports, and each port can
contribute at most two boundary-local face fragments. -/
theorem pointwiseSelectedSourceLocalLayerCell_faceFragmentCount_le_eight
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    let pair := layers.pointwiseSelectedLocalLayerPair hinterior
    Fintype.card (BoundaryRegionalFragment formation.annular.RS
      (vertexSetCrossingEdges formation.annular.RS
        (pair.componentSide
          (layers.pointwiseSelectedSourceBoundaryData hinterior).component)ᶜ)
      (vertexSetRegionEdges formation.annular.RS
        (pair.componentSide
          (layers.pointwiseSelectedSourceBoundaryData hinterior).component)ᶜ)) ≤ 8 := by
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let boundary := layers.pointwiseSelectedSourceBoundaryData hinterior
  let inside := (pair.componentSide boundary.component)ᶜ
  change Fintype.card (BoundaryRegionalFragment formation.annular.RS
      (vertexSetCrossingEdges formation.annular.RS inside)
      (vertexSetRegionEdges formation.annular.RS inside)) ≤ 8
  calc
    Fintype.card (BoundaryRegionalFragment formation.annular.RS
        (vertexSetCrossingEdges formation.annular.RS inside)
        (vertexSetRegionEdges formation.annular.RS inside)) ≤
        2 * Fintype.card (VertexSetCrossingEdge formation.annular.RS inside) :=
      vertexSetBoundaryGraphCutData_fragmentCount_le_two_mul_crossingPortCount_of_dartOccurrences
        formation.annular.RS inside
    _ = 8 := by
      have hcard : Fintype.card
          (VertexSetCrossingEdge formation.annular.RS inside) =
          pair.left.crosscut.walk.length + pair.right.crosscut.walk.length := by
        simpa [inside] using
          (Fintype.card_congr
            (pair.sourceSelectedComplementPort
              formation.annular.cellulation.rotation boundary)).symm
      rw [hcard]
      norm_num [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
        Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
        Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
        Formation.LocalLayerPair.firstLayer,
        Formation.LocalLayerPair.secondLayer,
        Formation.LocalLayerPair.firstWalk,
        Formation.LocalLayerPair.secondWalk]

/-- Faithful embedding of the exact dependent profile into the common finite
carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerCellProfileCode
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (profile : PointwiseSelectedSourceLocalLayerCellProfile hinterior layers) :
    PointwiseSelectedSourceLocalLayerCellBoundedProfile := by
  refine {
    faceFragmentCount := ⟨_, Nat.lt_succ_of_le
      (layers.pointwiseSelectedSourceLocalLayerCell_faceFragmentCount_le_eight
        hinterior)⟩
    profile := ?_ }
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  have hwidth : pair.left.crosscut.walk.length = 2 := by
    norm_num [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer,
      Formation.LocalLayerPair.firstWalk]
  rw [← hwidth]
  exact profile

theorem pointwiseSelectedSourceLocalLayerCellProfileCode_injective
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    Function.Injective
      (layers.pointwiseSelectedSourceLocalLayerCellProfileCode hinterior) := by
  intro left right heq
  dsimp only [pointwiseSelectedSourceLocalLayerCellProfileCode] at heq
  injection heq

/-- Positive support of the literal selected-Cell Count on the common finite
carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerCellBoundedProfileTransfer
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (left right : PointwiseSelectedSourceLocalLayerCellBoundedProfile) : Prop :=
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let boundary := layers.pointwiseSelectedSourceBoundaryData hinterior
  ∃ leftRaw rightRaw :
      PointwiseSelectedSourceLocalLayerCellProfile hinterior layers,
    layers.pointwiseSelectedSourceLocalLayerCellProfileCode hinterior leftRaw =
        left ∧
      layers.pointwiseSelectedSourceLocalLayerCellProfileCode hinterior rightRaw =
        right ∧
      0 < pair.sourceSelectedComplementLiteralOpenProfileCount
        formation.annular.cellulation.rotation boundary leftRaw rightRaw

noncomputable instance
    instDecidableRelPointwiseSelectedSourceLocalLayerCellBoundedProfileTransfer
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    DecidableRel
      (layers.pointwiseSelectedSourceLocalLayerCellBoundedProfileTransfer
        hinterior) := by
  classical
  intro left right
  unfold pointwiseSelectedSourceLocalLayerCellBoundedProfileTransfer
  infer_instance

/-- On encoded profiles, the common finite relation is exactly positivity of
the literal selected-boundary Count. -/
theorem pointwiseSelectedSourceLocalLayerCellBoundedProfileTransfer_code_iff
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (left right : PointwiseSelectedSourceLocalLayerCellProfile hinterior layers) :
    layers.pointwiseSelectedSourceLocalLayerCellBoundedProfileTransfer hinterior
        (layers.pointwiseSelectedSourceLocalLayerCellProfileCode hinterior left)
        (layers.pointwiseSelectedSourceLocalLayerCellProfileCode hinterior right) ↔
      let pair := layers.pointwiseSelectedLocalLayerPair hinterior
      let boundary := layers.pointwiseSelectedSourceBoundaryData hinterior
      0 < pair.sourceSelectedComplementLiteralOpenProfileCount
        formation.annular.cellulation.rotation boundary left right := by
  constructor
  · rintro ⟨leftRaw, rightRaw, hleft, hright, hpositive⟩
    have hleftRaw : leftRaw = left :=
      layers.pointwiseSelectedSourceLocalLayerCellProfileCode_injective
        hinterior hleft
    have hrightRaw : rightRaw = right :=
      layers.pointwiseSelectedSourceLocalLayerCellProfileCode_injective
        hinterior hright
    simpa only [hleftRaw, hrightRaw] using hpositive
  · intro hpositive
    exact ⟨left, right, rfl, rfl, hpositive⟩

/-- Concrete source semantics: a coded transition holds exactly when one
literal Tait colouring of this selected Cell realizes its two exact profiles. -/
theorem pointwiseSelectedSourceLocalLayerCellBoundedProfileTransfer_code_iff_exists_coloring
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (left right : PointwiseSelectedSourceLocalLayerCellProfile hinterior layers) :
    layers.pointwiseSelectedSourceLocalLayerCellBoundedProfileTransfer hinterior
        (layers.pointwiseSelectedSourceLocalLayerCellProfileCode hinterior left)
        (layers.pointwiseSelectedSourceLocalLayerCellProfileCode hinterior right) ↔
      let pair := layers.pointwiseSelectedLocalLayerPair hinterior
      let boundary := layers.pointwiseSelectedSourceBoundaryData hinterior
      ∃ cellColoring :
          pair.SourceSelectedComplementLiteralOpenTaitColoring
            formation.annular.cellulation.rotation boundary,
        pair.sourceSelectedComplementLiteralOpenLeftProfile
            formation.annular.cellulation.rotation boundary
            cellColoring.1 cellColoring.2 = left ∧
          pair.sourceSelectedComplementLiteralOpenRightProfile
            formation.annular.cellulation.rotation boundary
            cellColoring.1 cellColoring.2 = right := by
  rw [layers.pointwiseSelectedSourceLocalLayerCellBoundedProfileTransfer_code_iff
    hinterior]
  exact (layers.pointwiseSelectedLocalLayerPair hinterior
      |>.sourceSelectedComplementLiteralOpenProfileCount_pos_iff
        formation.annular.cellulation.rotation
        (layers.pointwiseSelectedSourceBoundaryData hinterior) left right)

end Formation.LocalLayerPair

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
