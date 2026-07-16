import Mettapedia.GraphTheory.FourColor.GoertzelV24SharedFacesTwoEdgeSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutNormalization

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalFaceIntersections

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24SharedFacesTwoEdgeSeparator
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoEdgeCutNormalization
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Two distinct quotient faces of a graph-backed vertex-minimal Tait
counterexample cannot share two distinct primal edges. Facial linear algebra
makes such an edge pair a separator, while exact-cut minimality says deleting
the pair leaves the graph connected. -/
theorem edge_eq_of_mem_distinct_orbitFace_pair
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {left right : OrbitFace graphData.toRotationSystem}
    (hfaces : left ≠ right)
    {first second : G.edgeSet}
    (hfirstLeft : first ∈
      orbitFaceBoundary graphData.toRotationSystem left)
    (hfirstRight : first ∈
      orbitFaceBoundary graphData.toRotationSystem right)
    (hsecondLeft : second ∈
      orbitFaceBoundary graphData.toRotationSystem left)
    (hsecondRight : second ∈
      orbitFaceBoundary graphData.toRotationSystem right) :
    first = second := by
  by_contra hedges
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hdual := orbitFaceInteriorDual_connected
    graphData.toRotationSystem minimal.spherical.cubic
      minimal.primalConnected minimal.vertexRotationCyclic
  have hdisconnected := not_connected_deleteEdges_pair_of_shared_face_pair
    graphData minimal.facesTwoSided hdual hconnected minimal.spherical
      hfaces hedges hfirstLeft hfirstRight hsecondLeft hsecondRight
  exact hdisconnected
    (deleteEdges_pair_connected_of_vertexMinimalTaitCounterexample
      graphData minimal first second hedges)

/-- The quotient facial incidence of a graph-backed vertex-minimal Tait
counterexample has a unique shared interior edge for every adjacent pair of
distinct faces. This is the canonical-rung hypothesis used by corridor and
fusion-chain constructions. -/
theorem pairwiseUniqueSharedInteriorEdges
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :
    PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)) := by
  intro left _hleft right _hright hfaces
  rw [Finset.card_le_one]
  intro first hfirst second hsecond
  rcases (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).1 hfirst with
      ⟨_hfirstInterior, hfirstLeft, hfirstRight⟩
  rcases (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).1 hsecond with
      ⟨_hsecondInterior, hsecondLeft, hsecondRight⟩
  exact edge_eq_of_mem_distinct_orbitFace_pair
    graphData minimal hfaces hfirstLeft hfirstRight
      hsecondLeft hsecondRight

end

end GoertzelV24MinimalFaceIntersections

end Mettapedia.GraphTheory.FourColor
