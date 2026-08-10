import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutConnectedSides
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutDualLoopBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondSpliceEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutCapGeometry

/-!
# Planar output of a source annular crosscut splice

The paired source crosscut now supplies the two connected graph sides and
the exact finite boundary of the deleted region.  This module attaches those
facts to the generic planar-bond splice theorem.  The remaining order premise
is kept as its exact computed permutation statement so the next construction
has a single, visible geometric target.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PlanarBondSpliceEuler
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

/-- The still-geometric part of the source crosscut splice: the two actual
source interfaces occur in the opposite order around the deleted side. -/
def SourceCrosscutBoundaryData.FollowsOppositeDeletedBoundaryOrder
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
  CutsFollowOppositeDeletedBoundaryOrder data.toRotationSystem
    (boundary.deletedVertices data pair)
    (pair.left.crossingEdge hunique)
    (fun step : Fin pair.left.walk.length =>
      pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))
    (boundary.orderedCut_boundary_eq data pair)
    boundary.leftInjective
    (pair.sourceCrosscutOrderedCutSidesData data boundary).rightInjective
    (pair.sourceCrosscutOrderedCutSidesData data boundary).disjoint

/-- The actual source crosscut boundary has the planar splice order once its
concrete retained-side darts are oriented by the corresponding facial-dual
loop.  Thus the remaining source-formation obligation is precisely the
target-face incidence, not an abstract boundary permutation. -/
theorem SourceCrosscutBoundaryData.followsOppositeDeletedBoundaryOrder_of_dualLoopFacesTarget
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
    (hfaces : boundary.DualLoopBoundaryFacesTarget data pair) :
    boundary.FollowsOppositeDeletedBoundaryOrder data pair := by
  unfold SourceCrosscutBoundaryData.FollowsOppositeDeletedBoundaryOrder
  exact pair.sourceCrosscut_deletedBoundarySuccessor_eq_oppositeBoundaryOrder
    data htwoSided boundary hfaces

/-- A nondegenerate aligned crosscut has a positive common interface width. -/
theorem sourceCrosscut_width_pos
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    0 < pair.left.walk.length := by
  rcases pair.nondegenerate with hleft | hright
  · omega
  · rw [← pair.length_eq] at hright
    omega

/-- Once the source boundary has its actual cyclic order, the concrete
layer splice is again a spherical cubic map.  All other planar-bond premises
are derived here from the paired simple crosscut. -/
theorem sourceCrosscutLayerSplice_orbitSphericalCubicMapData_of_boundaryOrder
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
    (horder : boundary.FollowsOppositeDeletedBoundaryOrder data pair) :
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
  have hgeneric := orbitSphericalCubicMapData_orderedCutSplice_of_planar_bond
    data deleted leftCrossing rightCrossing hboundary hleftInjective
      hrightInjective hdisjoint hn (by
        simpa [SourceCrosscutBoundaryData.FollowsOppositeDeletedBoundaryOrder,
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
      (by
        exact houter)
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

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
