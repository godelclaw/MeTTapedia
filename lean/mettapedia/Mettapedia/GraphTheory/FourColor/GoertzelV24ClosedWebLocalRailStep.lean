import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalInterfaceOrientation

/-!
# Source-local Cell-3 rail steps

The closed-web carrier is not globally cubic.  Nevertheless, two consecutive
surviving side slots of one certified interior Cell-3 face determine adjacent
exterior faces: the only cubicity required is the three-dart rotation at their
single common corner.  This is the local incidence lemma needed to turn the
canonical rail coordinates into literal facial-dual rail segments.

This file constructs one local step.  It does not yet assert that repeated
steps append to simple end-capped rails or realize a global annular crosscut.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace LocalLayerFormation

/-- **L9 (local rail adjacency).** Consecutive surviving slots of one
source-derived Cell-3 face give a genuine exterior facial-dual edge.  Unlike
the framed-corridor analogue, this theorem assumes no global cubicity: it uses
only the certified three-dart rotation at the displayed interior corner. -/
theorem localPlacementSideFaces_adjacent_of_forwardStep
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (left right : {position // position ∈ placementSidePositions placement})
    (hsuccessor : right.1.val ≡ left.1.val + 1 [MOD 6]) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (localPlacementSideFace placement left)
        (localPlacementSideFace placement right) := by
  let leftDart := faceCycleDart web.annular.RS placement.root left.1
  let rightDart := faceCycleDart web.annular.RS placement.root right.1
  have hdarts : rightDart = web.annular.RS.phi leftDart := by
    exact faceCycleDart_successor_of_modEq web.annular.RS placement.root
      placement.orbit_card left.1 right.1 hsuccessor
  have hpositionsNe : left ≠ right := by
    intro heq
    have hvalEq : left.1.val = right.1.val :=
      congrArg (fun position => position.1.val) heq
    have hselfSuccessor : left.1.val ≡ left.1.val + 1 [MOD 6] := by
      simpa only [hvalEq] using hsuccessor
    have hleftBound : left.1.val < 6 := by
      simpa only [placement.orbit_card] using left.1.isLt
    interval_cases hleft : left.1.val <;>
      norm_num [Nat.ModEq, hleft] at hselfSuccessor
  have hfacesNe : dartOrbitFace web.annular.RS
      (web.annular.RS.alpha leftDart) ≠
      dartOrbitFace web.annular.RS
        (web.annular.RS.alpha (web.annular.RS.phi leftDart)) := by
    intro hfaces
    apply hpositionsNe
    apply localPlacementSideFace_injective (corridor := corridor) placement
    apply Subtype.ext
    change dartOrbitFace web.annular.RS (web.annular.RS.alpha leftDart) =
      dartOrbitFace web.annular.RS (web.annular.RS.alpha rightDart)
    rw [hdarts]
    exact hfaces
  have hcornerCard : (web.annular.RS.dartsAt
      (web.annular.RS.vertOf (web.annular.RS.alpha leftDart))).card = 3 := by
    apply InteriorFace.dartsAt_card_eq_three web
    change (localPlacementSideFace placement left).1 ∈
      web.annular.cellulation.interiorFaces
    exact localPlacementSideFace_internal (corridor := corridor) placement left
  have hadj := oppositeFaces_adjacent_at_locally_cubic_corner web.annular.RS
    (InteriorFace.vertexRotationCyclic web) leftDart hcornerCard hfacesNe
  simpa only [localPlacementSideFace, leftDart, rightDart, hdarts] using hadj

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
