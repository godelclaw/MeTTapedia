import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceIntersections
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutCollarChord

/-!
# Dual triangles in a minimal Tait counterexample

The bounded-interaction step in the source is a closed-map statement before
it is transported to a cut-open collar.  Three pairwise adjacent facial
orbits form a literal length-three dual cycle.  In a vertex-minimal Tait
counterexample, cyclic five-edge-connectivity forces the corresponding
three-edge primal separator to cut off exactly one vertex.

This is the closed-map half of the adjacent Cell-3 rail classification.  It
does not identify a cut-open annular carrier with the closed minimal map, and
it does not assume that identification as a field.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalDualTriangleClassification

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalFaceIntersections
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24CubicSmallBoundaryCycle
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

local instance minimalDualTriangleLocallyFinite : G.LocallyFinite :=
  collarFiniteGraphLocallyFinite G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The literal facial-dual triangle determined by three pairwise adjacent
faces, based at the first face. -/
def dualTriangleWalk
    (graphData : Data G)
    {first second third : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (hfirstSecond : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj first second)
    (hsecondThird : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj second third)
    (hthirdFirst : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj third first) :
    (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Walk first first :=
  .cons hfirstSecond (.cons hsecondThird (.cons hthirdFirst .nil))

@[simp] theorem dualTriangleWalk_length
    (graphData : Data G)
    {first second third : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (hfirstSecond : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj first second)
    (hsecondThird : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj second third)
    (hthirdFirst : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj third first) :
    (dualTriangleWalk graphData hfirstSecond hsecondThird
      hthirdFirst).length = 3 := by
  simp [dualTriangleWalk]

theorem dualTriangleWalk_isCycle
    (graphData : Data G)
    {first second third : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (hfirstSecond : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj first second)
    (hsecondThird : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj second third)
    (hthirdFirst : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj third first) :
    (dualTriangleWalk graphData hfirstSecond hsecondThird
      hthirdFirst).IsCycle := by
  simp [dualTriangleWalk, SimpleGraph.Walk.isCycle_def,
    SimpleGraph.Walk.isTrail_def, hfirstSecond.ne,
    hfirstSecond.ne.symm, hsecondThird.ne,
    hthirdFirst.ne, hthirdFirst.ne.symm]

/-- **Closed bounded interaction.** A facial-dual triangle in a graph-backed
vertex-minimal Tait counterexample cuts off a singleton primal component, and
the boundary of that component is exactly the three crossed primal edges.

The result is intentionally phrased on the closed ambient map.  Applying it
to the source's open annular Cell-3 carrier still requires the explicit
cap-deletion/face-transport construction. -/
theorem exists_singleton_primalCut_of_dual_triangle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first second third : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (hfirstSecond : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj first second)
    (hsecondThird : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj second third)
    (hthirdFirst : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj third first) :
    let walk := dualTriangleWalk graphData hfirstSecond hsecondThird hthirdFirst
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal) walk
    ∃ component :
        (G.deleteEdges
          (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
            (pairwiseUniqueSharedInteriorEdges graphData minimal) walk)
          ).ConnectedComponent,
      Nat.card {vertex : V // vertex ∈ component.supp} = 1 ∧
        crossingEdgeFinset G (fun vertex => vertex ∈ component.supp) =
          removed := by
  dsimp only
  have hregular : G.IsRegularOfDegree 3 :=
    graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hcyclic : CyclicallyFiveEdgeConnected G :=
    GoertzelV24FourEdgeCutGluing.cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
      graphData minimal
  have hwalkCycle := dualTriangleWalk_isCycle graphData
    hfirstSecond hsecondThird hthirdFirst
  have hdelete :
      ¬ (G.deleteEdges
        (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
          (pairwiseUniqueSharedInteriorEdges graphData minimal)
          (dualTriangleWalk graphData hfirstSecond hsecondThird hthirdFirst))).Connected := by
    exact
      GoertzelV24DualCycleSeparator.not_connected_deleteEdges_dualWalkPrimalCut_of_isCycle
        graphData minimal.facesTwoSided
        (orbitFaceInteriorDual_connected graphData.toRotationSystem
          minimal.spherical.cubic minimal.primalConnected
          minimal.vertexRotationCyclic)
        hconnected minimal.spherical
        (pairwiseUniqueSharedInteriorEdges graphData minimal)
        (dualTriangleWalk graphData hfirstSecond hsecondThird hthirdFirst)
        hwalkCycle
  exact
    GoertzelV24DualCycleSeparator.exists_primalCut_component_card_eq_one_and_boundary_eq_of_isCycle_of_length_eq_three
      graphData hregular hconnected hcyclic
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      (dualTriangleWalk graphData hfirstSecond hsecondThird hthirdFirst)
      hwalkCycle (dualTriangleWalk_length graphData
        hfirstSecond hsecondThird hthirdFirst) hdelete

/-- The three primal edges crossed by a dual triangle in a graph-backed
vertex-minimal counterexample are all incident with one ambient vertex.

This is the exact local consequence of the singleton separator used by the
source's radius-one collar description: the dual triangle is the link of a
single primal vertex, rather than an arbitrary separating triangle.  The
statement remains on the closed ambient map; transporting it to a literal
open annulus is a separate formation theorem. -/
theorem exists_vertex_mem_all_crossed_edges_of_dual_triangle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first second third : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (hfirstSecond : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj first second)
    (hsecondThird : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj second third)
    (hthirdFirst : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj third first) :
    let walk := dualTriangleWalk graphData hfirstSecond hsecondThird hthirdFirst
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal) walk
    ∃ vertex : V, ∀ edge ∈ removed, vertex ∈ edge.1 := by
  dsimp only
  rcases exists_singleton_primalCut_of_dual_triangle graphData minimal
      hfirstSecond hsecondThird hthirdFirst with
    ⟨component, hcard, hboundary⟩
  let vertex : V := component.nonempty_supp.choose
  have hvertex : vertex ∈ component.supp :=
    component.nonempty_supp.choose_spec
  have hsubsingleton :
      Subsingleton {candidate : V // candidate ∈ component.supp} :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  refine ⟨vertex, ?_⟩
  intro edge hedge
  have hcrossing : edge ∈
      crossingEdgeFinset G (fun candidate => candidate ∈ component.supp) := by
    rw [hboundary]
    exact hedge
  rcases (mem_crossingEdgeFinset_iff
      (fun candidate => candidate ∈ component.supp) edge).1 hcrossing with
    ⟨inside, outside, hinsideEdge, _houtsideEdge, hinside, _houtside⟩
  have heq : inside = vertex :=
    congrArg Subtype.val
      (hsubsingleton.elim ⟨inside, hinside⟩ ⟨vertex, hvertex⟩)
  simpa only [heq] using hinsideEdge

end

end GoertzelV24MinimalDualTriangleClassification

end Mettapedia.GraphTheory.FourColor
