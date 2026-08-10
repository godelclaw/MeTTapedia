import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutPlanarSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutTargetSide
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleEitherBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondSpliceEitherOrientation

/-!
# Orientation-independent source annular crosscut splice

The two source transversals determine a simple facial-dual loop, but that
geometric loop has no preferred traversal direction.  This module transfers
the two coherent choices into the planar splice API.  The source construction
therefore proves a real simple boundary without imposing an arbitrary global
orientation on it.

No profile, catalogue, or covering-style reduction is involved here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24DualCycleBoundaryFaceOrientation
open GoertzelV24DualCycleEitherBoundaryOrder
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PlanarBondSpliceEitherOrientation
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification
open GoertzelV24TwoEdgeCutCapGeometry
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The source crosscut's actual deleted boundary may follow its literal
facial-dual loop in either coherent direction.  This is not a weakening: each
branch is an explicit equality of concrete boundary permutations. -/
def SourceCrosscutBoundaryData.FollowsEitherDeletedBoundaryOrientation
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) : Prop :=
  CutsFollowEitherDeletedBoundaryOrientation data.toRotationSystem
    (boundary.deletedVertices data pair)
    (pair.left.crossingEdge hunique)
    (fun step : Fin pair.left.walk.length =>
      pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))
    (boundary.orderedCut_boundary_eq data pair)
    boundary.leftInjective
    (pair.sourceCrosscutOrderedCutSidesData data boundary).rightInjective
    (pair.sourceCrosscutOrderedCutSidesData data boundary).disjoint

private theorem permCongr_trans_eq
    {A B C : Type*} (first : A ≃ B) (second : B ≃ C)
    (perm : Equiv.Perm A) :
    (first.trans second).permCongr perm =
      second.permCongr (first.permCongr perm) := by
  rfl

/-- If retained boundary darts face the source face of every dual-loop step,
the source crosscut reads the inverse opposite boundary order. -/
theorem sourceCrosscut_deletedBoundarySuccessor_eq_inverse_oppositeBoundaryOrder
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hsource : BoundaryDartsUseDualCycleSourceFaces data pair.dualLoop
      (boundary.deletedVertices data pair)
      (pair.sourceCrosscutDualLoopBoundaryEquiv data boundary)) :
    deletedRegionBoundarySuccessor data.toRotationSystem
        (boundary.deletedVertices data pair) =
      (orderedBoundaryPositionEquiv data.toRotationSystem
        (boundary.deletedVertices data pair)
        (pair.left.crossingEdge hunique)
        (fun step : Fin pair.left.walk.length =>
          pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))
        (boundary.orderedCut_boundary_eq data pair)
        boundary.leftInjective
        (pair.sourceCrosscutOrderedCutSidesData data boundary).rightInjective
        (pair.sourceCrosscutOrderedCutSidesData data boundary).disjoint).permCongr
          (oppositeBoundaryCycle pair.left.walk.length)⁻¹ := by
  rw [deletedBoundarySuccessor_eq_prev_dualCycleBoundaryOrder
    data htwoSided pair.dualLoop pair.dualLoop_isCycle
    (boundary.deletedVertices data pair)
    (pair.sourceCrosscut_vertexSetCrossingEdges_eq_dualLoopCrossingEdges
      data boundary)
    (pair.sourceCrosscutDualLoopBoundaryEquiv data boundary)
    (pair.sourceCrosscutDualLoopBoundaryEquiv_bijective data boundary)
    (pair.sourceCrosscutDualLoopBoundaryEquiv_edge_eq_dualLoopCrossing
      data boundary)
    hsource]
  let loopBoundaryEquiv := pair.sourceCrosscutDualLoopBoundaryEquiv data boundary
  have hchosen : Equiv.ofBijective (loopBoundaryEquiv :
      Fin pair.dualLoop.length →
        BoundaryDart data.toRotationSystem
          (deletedRegionKeep (boundary.deletedVertices data pair)))
      loopBoundaryEquiv.bijective = loopBoundaryEquiv := by
    apply Equiv.ext
    intro step
    rfl
  rw [hchosen]
  let loopPositionEquiv := pair.sourceCrosscutDualLoopPositionEquiv data
  let boundaryPositionEquiv := orderedBoundaryPositionEquiv
    data.toRotationSystem (boundary.deletedVertices data pair)
    (pair.left.crossingEdge hunique)
    (fun step : Fin pair.left.walk.length =>
      pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))
    (boundary.orderedCut_boundary_eq data pair)
    boundary.leftInjective
    (pair.sourceCrosscutOrderedCutSidesData data boundary).rightInjective
    (pair.sourceCrosscutOrderedCutSidesData data boundary).disjoint
  change (loopPositionEquiv.trans boundaryPositionEquiv).permCongr
      (finRotate pair.dualLoop.length)⁻¹ =
    boundaryPositionEquiv.permCongr
      (oppositeBoundaryCycle pair.left.walk.length)⁻¹
  rw [permCongr_trans_eq]
  have hforward := pair.sourceCrosscutDualLoopPosition_rotate_eq_oppositeBoundaryCycle
    data
  have hinverse : loopPositionEquiv.permCongr
      (finRotate pair.dualLoop.length)⁻¹ =
      (oppositeBoundaryCycle pair.left.walk.length)⁻¹ := by
    calc
      loopPositionEquiv.permCongr (finRotate pair.dualLoop.length)⁻¹ =
          (loopPositionEquiv.permCongr
            (finRotate pair.dualLoop.length))⁻¹ := by
            rfl
      _ = (oppositeBoundaryCycle pair.left.walk.length)⁻¹ := by
        rw [hforward]
  rw [hinverse]

/-- A literal source annular crosscut always supplies one of the two coherent
deleted-boundary orientations.  The target-facing branch uses the propagated
target-side geometry; the complementary branch proves source-face retention
and reads the inverse cycle. -/
theorem SourceCrosscutBoundaryData.followsEitherDeletedBoundaryOrientation
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    boundary.FollowsEitherDeletedBoundaryOrientation data pair := by
  unfold SourceCrosscutBoundaryData.FollowsEitherDeletedBoundaryOrientation
  by_cases htarget : ∃ step,
      deletedRegionKeep (boundary.deletedVertices data pair)
        (data.toRotationSystem.vertOf
          (dualWalkTargetFaceDart hunique pair.dualLoop step))
  · left
    have hfaces :=
      boundary.dualLoopBoundaryFacesTarget_of_exists_targetFaceDart_kept
        data htwoSided pair htarget
    exact boundary.followsOppositeDeletedBoundaryOrder_of_dualLoopFacesTarget
      data htwoSided pair hfaces
  · right
    have hnotTarget : ∀ step,
        ¬ deletedRegionKeep (boundary.deletedVertices data pair)
          (data.toRotationSystem.vertOf
            (dualWalkTargetFaceDart hunique pair.dualLoop step)) := by
      intro step hkept
      exact htarget ⟨step, hkept⟩
    have hsourceKept := sourceFaceDarts_kept_of_targetFaceDarts_not_kept
      data pair.dualLoop (boundary.deletedVertices data pair)
      (pair.sourceCrosscut_vertexSetCrossingEdges_eq_dualLoopCrossingEdges
        data boundary) hnotTarget
    have hsourceFaces :=
      boundaryDartsUseDualCycleSourceFaces_of_sourceFaceDarts_kept
        data pair.dualLoop (boundary.deletedVertices data pair)
        (pair.sourceCrosscut_vertexSetCrossingEdges_eq_dualLoopCrossingEdges
          data boundary)
        (pair.sourceCrosscutDualLoopBoundaryEquiv data boundary)
        (pair.sourceCrosscutDualLoopBoundaryEquiv_edge_eq_dualLoopCrossing
          data boundary)
        hsourceKept
    exact pair.sourceCrosscut_deletedBoundarySuccessor_eq_inverse_oppositeBoundaryOrder
      data htwoSided boundary hsourceFaces

/-- The literal source crosscut splice remains a spherical cubic map under
either coherent boundary orientation.  All non-orientation premises remain
the concrete cut, side-connectivity, and matched-port data already constructed
from the two source transversals. -/
theorem sourceCrosscutLayerSplice_orbitSphericalCubicMapData_of_eitherOrientation
    (data : Data G)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint data)
    (horder : boundary.FollowsEitherDeletedBoundaryOrientation data pair) :
    OrbitSphericalCubicMapData
      (pair.sourceCrosscutLayerSpliceData data boundary hseparated).output := by
  let deleted := boundary.deletedVertices data pair
  let leftCrossing := pair.left.crossingEdge hunique
  let rightCrossing : Fin pair.left.walk.length → G.edgeSet :=
    fun step => pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)
  have hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges data.toRotationSystem deleted := by
    exact boundary.orderedCut_boundary_eq data pair
  have hleftInjective : Function.Injective leftCrossing :=
    boundary.leftInjective
  have hrightInjective : Function.Injective rightCrossing :=
    (pair.sourceCrosscutOrderedCutSidesData data boundary).rightInjective
  have hdisjoint : Disjoint (orderedCut leftCrossing) (orderedCut rightCrossing) :=
    (pair.sourceCrosscutOrderedCutSidesData data boundary).disjoint
  have hn : 0 < pair.left.walk.length := sourceCrosscut_width_pos data pair
  have hsides := SourceCrosscutBoundaryData.deletedRegion_sides_connected
    data htwoSided hconnected pair boundary
  have houter := SourceCrosscutBoundaryData.outer_not_mem_deletedVertices
    data pair boundary
  have hkeep := SourceCrosscutBoundaryData.deletedRegionKeep_eq_componentSide
    data pair boundary
  have hseam : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (deletedRegionKeep deleted) leftCrossing
            (leftCrossing_outward data.toRotationSystem deleted leftCrossing
              rightCrossing hboundary) step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (deletedRegionKeep deleted) rightCrossing
            (rightCrossing_outward data.toRotationSystem deleted leftCrossing
              rightCrossing hboundary) step).1.1.1 := by
    intro step
    let leftDart := orderedBoundaryDart data.toRotationSystem
      (deletedRegionKeep deleted) leftCrossing
      (leftCrossing_outward data.toRotationSystem deleted leftCrossing
        rightCrossing hboundary) step
    let rightDart := orderedBoundaryDart data.toRotationSystem
      (deletedRegionKeep deleted) rightCrossing
      (rightCrossing_outward data.toRotationSystem deleted leftCrossing
        rightCrossing hboundary) step
    apply hseparated step
      (data.toRotationSystem.vertOf leftDart.1.1.1)
      (data.toRotationSystem.vertOf rightDart.1.1.1)
    · rw [data.toRotationSystem.mem_endpoints_iff]
      refine ⟨leftDart.1.1.1,
        data.toRotationSystem.mem_dartsOn.2 ?_, rfl⟩
      exact orderedBoundaryDart_edgeOf data.toRotationSystem
        (deletedRegionKeep deleted) leftCrossing
        (leftCrossing_outward data.toRotationSystem deleted leftCrossing
          rightCrossing hboundary) step
    · rw [data.toRotationSystem.mem_endpoints_iff]
      refine ⟨rightDart.1.1.1,
        data.toRotationSystem.mem_dartsOn.2 ?_, rfl⟩
      exact orderedBoundaryDart_edgeOf data.toRotationSystem
        (deletedRegionKeep deleted) rightCrossing
        (rightCrossing_outward data.toRotationSystem deleted leftCrossing
          rightCrossing hboundary) step
  have hgeneric :=
    orbitSphericalCubicMapData_orderedCutSplice_of_planar_bond_of_either_orientation
      data deleted leftCrossing rightCrossing hboundary hleftInjective
        hrightInjective hdisjoint hn (by
          simpa [SourceCrosscutBoundaryData.FollowsEitherDeletedBoundaryOrientation,
            deleted, leftCrossing, rightCrossing] using horder)
        hsphere htwoSided hconnected hrotation hsides.1 hsides.2 houter hseam
  have htransported :=
    orbitSphericalCubicMapData_orderedCutRetainedVertexRotationSystem_congr_keep
      data.toRotationSystem hkeep leftCrossing rightCrossing
      (leftCrossing_outward data.toRotationSystem deleted leftCrossing
        rightCrossing hboundary)
      (rightCrossing_outward data.toRotationSystem deleted leftCrossing
        rightCrossing hboundary)
      boundary.leftCrosses
      (fun step => boundary.rightCrosses (Fin.cast pair.length_eq step))
      hleftInjective hrightInjective
      (deletedRegionBoundaryCover data.toRotationSystem deleted leftCrossing
        rightCrossing hboundary)
      (pair.sourceCrosscutOrderedCutSidesData data boundary).cover
      hdisjoint
      (by exact houter)
      boundary.outer_kept
      hseam
      (fun step =>
        pair.sourceCrosscutSeamEndpoints_of_matchedCrossingsVertexDisjoint
          data boundary hseparated step)
      hgeneric
  unfold sourceCrosscutLayerSpliceData sourceCrosscutSpliceData
  unfold OrderedCutSidesData.splice sourceCrosscutOrderedCutSidesData
  unfold sourceCrosscutLeftCutData sourceCrosscutRightCutData
  unfold sourceCrosscutCutData OrderedCutSpliceData.output
  exact htransported

/-- The source's paired simple transversals now construct a spherical cubic
splice without a caller-supplied orientation choice. -/
theorem sourceCrosscutLayerSplice_orbitSphericalCubicMapData
    (data : Data G)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint data) :
    OrbitSphericalCubicMapData
      (pair.sourceCrosscutLayerSpliceData data boundary hseparated).output := by
  exact pair.sourceCrosscutLayerSplice_orbitSphericalCubicMapData_of_eitherOrientation
    data hsphere htwoSided hconnected hrotation boundary hseparated
      (boundary.followsEitherDeletedBoundaryOrientation data htwoSided pair)

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
