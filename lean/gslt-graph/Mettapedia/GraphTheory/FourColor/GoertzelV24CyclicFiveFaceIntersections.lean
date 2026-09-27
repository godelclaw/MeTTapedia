import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicTwoEdgeCyclicCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24SharedFacesTwoEdgeSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CyclicFiveFaceIntersections

open GoertzelV24CubicTwoEdgeCyclicCut
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SharedFacesTwoEdgeSeparator
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Under cyclic 5-edge connectivity, two distinct quotient faces of a
graph-backed cellular sphere cannot share two distinct primal edges. -/
theorem edge_eq_of_mem_distinct_orbitFace_pair
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (hcyclicFive : CyclicallyFiveEdgeConnected G)
    {left right : OrbitFace data.toRotationSystem} (hfaces : left ≠ right)
    {first second : G.edgeSet}
    (hfirstLeft : first ∈ orbitFaceBoundary data.toRotationSystem left)
    (hfirstRight : first ∈ orbitFaceBoundary data.toRotationSystem right)
    (hsecondLeft : second ∈ orbitFaceBoundary data.toRotationSystem left)
    (hsecondRight : second ∈ orbitFaceBoundary data.toRotationSystem right) :
    first = second := by
  by_contra hedges
  have hdelete := not_connected_deleteEdges_pair_of_shared_face_pair
    data htwoSided hdual hconnected hsphere hfaces hedges
      hfirstLeft hfirstRight hsecondLeft hsecondRight
  obtain ⟨cut, hcutCard⟩ :=
    exists_smallCyclicEdgeCut_card_le_two_of_not_connected_deleteEdges_pair
      (data.toRotationSystem_isCubic_iff.mp hsphere.cubic)
      hconnected first second hdelete
  exact hcyclicFive.not_smallCyclicEdgeCut_card_le_four cut
    (le_trans hcutCard (by omega))

/-- The facial-dual connectedness needed by the separator theorem is computed
from connectedness of the graph-backed primal graph and the actual cyclic
vertex rotations. -/
theorem edge_eq_of_mem_distinct_orbitFace_pair_of_vertexRotation
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hcyclicFive : CyclicallyFiveEdgeConnected G)
    {left right : OrbitFace data.toRotationSystem} (hfaces : left ≠ right)
    {first second : G.edgeSet}
    (hfirstLeft : first ∈ orbitFaceBoundary data.toRotationSystem left)
    (hfirstRight : first ∈ orbitFaceBoundary data.toRotationSystem right)
    (hsecondLeft : second ∈ orbitFaceBoundary data.toRotationSystem left)
    (hsecondRight : second ∈ orbitFaceBoundary data.toRotationSystem right) :
    first = second := by
  have hprimal :
      (rotationPrimalGraph data.toRotationSystem).Connected := by
    rw [rotationPrimalGraph_toRotationSystem_eq]
    exact hconnected
  have hdual := orbitFaceInteriorDual_connected data.toRotationSystem
    hsphere.cubic hprimal hrotation
  exact edge_eq_of_mem_distinct_orbitFace_pair data htwoSided hdual
    hconnected hsphere hcyclicFive hfaces
      hfirstLeft hfirstRight hsecondLeft hsecondRight

/-- In a cyclically 5-edge-connected graph-backed cellular sphere, every two
distinct quotient faces share at most one interior edge. This is the computed
incidence property required for canonical corridor rungs. -/
theorem pairwiseUniqueSharedInteriorEdges_of_cyclicallyFiveEdgeConnected
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hcyclicFive : CyclicallyFiveEdgeConnected G) :
    PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) := by
  intro left _hleft right _hright hfaces
  rw [Finset.card_le_one]
  intro first hfirst second hsecond
  rcases (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem))).1 hfirst with
      ⟨_hfirstInterior, hfirstLeft, hfirstRight⟩
  rcases (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem))).1 hsecond with
      ⟨_hsecondInterior, hsecondLeft, hsecondRight⟩
  exact edge_eq_of_mem_distinct_orbitFace_pair_of_vertexRotation
    data htwoSided hconnected hsphere hrotation hcyclicFive hfaces
      hfirstLeft hfirstRight hsecondLeft hsecondRight

end


end GoertzelV24CyclicFiveFaceIntersections

end Mettapedia.GraphTheory.FourColor
