import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalDualTriangleClassification
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionEndpointIncidence

/-!
# Minimal dual triangles retain their primal corner under opening

The closed L1 classification says that the three primal edges crossed by a
facial-dual triangle in a graph-backed vertex-minimal counterexample meet at
one ambient vertex.  This file transports that incidence through a literal
opening whenever the first face of the triangle is wholly retained.

This is the generic cap-deletion part of the Cell-3 formation bridge.  It does
not construct the source annulus from the closed minimal map, identify its
selected corridor faces with these opened face orbits, or assert that every
newer-Fable corridor type is the strict three-flank type.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionMinimalDualTriangleIncidence

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalDualTriangleClassification
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OpenRegionEndpointIncidence
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Regard the face orbit of a dart as an ambient face in the full facial
carrier. -/
def ambientFaceOfDart (RS : RotationSystem V G.edgeSet) (root : RS.D) :
    AmbientFace (Finset.univ : Finset (OrbitFace RS)) :=
  ⟨dartOrbitFace RS root, Finset.mem_univ _⟩

/-- **L1 (closed-to-open corner transport).** Let three ambient faces form a
facial-dual triangle in a graph-backed vertex-minimal Tait counterexample.
On the first face, choose the two canonical primal edges leading to the other
two faces.  If that entire first face survives a literal opening, then the two
computed open-face edges still have one common retained endpoint.

The returned face-cycle coordinates are constructed from the canonical
closed edges; they are not caller-supplied reindexing data. -/
theorem exists_common_open_endpoint_of_retained_dual_triangle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (keep : V → Prop)
    (outer : Dart graphData.toRotationSystem keep)
    (firstRoot secondRoot thirdRoot : graphData.toRotationSystem.D)
    (hfirstRetained : FaceFullyRetained graphData.toRotationSystem keep firstRoot)
    (hfirstSecond :
      (interiorDualGraph
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))).Adj
        (ambientFaceOfDart graphData.toRotationSystem firstRoot)
        (ambientFaceOfDart graphData.toRotationSystem secondRoot))
    (hsecondThird :
      (interiorDualGraph
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))).Adj
        (ambientFaceOfDart graphData.toRotationSystem secondRoot)
        (ambientFaceOfDart graphData.toRotationSystem thirdRoot))
    (hthirdFirst :
      (interiorDualGraph
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))).Adj
        (ambientFaceOfDart graphData.toRotationSystem thirdRoot)
        (ambientFaceOfDart graphData.toRotationSystem firstRoot)) :
    ∃ firstSecondPoint firstThirdPoint :
        {point // graphData.toRotationSystem.phi.SameCycle firstRoot point},
      ∃ openVertex : Vertex graphData.toRotationSystem keep,
        openVertex ∈
            (rotationSystem graphData.toRotationSystem keep outer).endpoints
              (openFaceEdge graphData.toRotationSystem keep outer firstRoot
                hfirstRetained firstSecondPoint) ∧
          openVertex ∈
            (rotationSystem graphData.toRotationSystem keep outer).endpoints
              (openFaceEdge graphData.toRotationSystem keep outer firstRoot
                hfirstRetained firstThirdPoint) := by
  let RS := graphData.toRotationSystem
  let allFaces : Finset (OrbitFace RS) := Finset.univ
  let hunique := pairwiseUniqueSharedInteriorEdges graphData minimal
  let firstSecondEdge := sharedInteriorEdgeOfAdjOfPairwiseUnique
    (orbitFaceBoundary RS) allFaces hunique hfirstSecond
  let thirdFirstEdge := sharedInteriorEdgeOfAdjOfPairwiseUnique
    (orbitFaceBoundary RS) allFaces hunique hthirdFirst
  rcases exists_vertex_mem_three_shared_edges_of_dual_triangle graphData minimal
      hfirstSecond hsecondThird hthirdFirst with
    ⟨vertex, hvertexFirstSecond, _hvertexSecondThird, hvertexThirdFirst⟩
  have hfirstSecondOnFirst :
      firstSecondEdge ∈ orbitFaceBoundary RS (dartOrbitFace RS firstRoot) := by
    exact (mem_sharedInteriorEdges_iff
      (orbitFaceBoundary RS) allFaces).1
        (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
          (orbitFaceBoundary RS) allFaces hunique hfirstSecond) |>.2.1
  have hthirdFirstOnFirst :
      thirdFirstEdge ∈ orbitFaceBoundary RS (dartOrbitFace RS firstRoot) := by
    exact (mem_sharedInteriorEdges_iff
      (orbitFaceBoundary RS) allFaces).1
        (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
          (orbitFaceBoundary RS) allFaces hunique hthirdFirst) |>.2.2
  rcases (mem_orbitFaceBoundary_iff RS (dartOrbitFace RS firstRoot)
      firstSecondEdge).1 hfirstSecondOnFirst with
    ⟨firstSecondDart, hfirstSecondFace, hfirstSecondEdge⟩
  rcases (mem_orbitFaceBoundary_iff RS (dartOrbitFace RS firstRoot)
      thirdFirstEdge).1 hthirdFirstOnFirst with
    ⟨firstThirdDart, hfirstThirdFace, hfirstThirdEdge⟩
  have hfirstSecondCycle : RS.phi.SameCycle firstRoot firstSecondDart := by
    apply (RS.mem_faceOrbit).1
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit RS firstRoot]
    exact hfirstSecondFace
  have hfirstThirdCycle : RS.phi.SameCycle firstRoot firstThirdDart := by
    apply (RS.mem_faceOrbit).1
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit RS firstRoot]
    exact hfirstThirdFace
  let firstSecondPoint : {point // RS.phi.SameCycle firstRoot point} :=
    ⟨firstSecondDart, hfirstSecondCycle⟩
  let firstThirdPoint : {point // RS.phi.SameCycle firstRoot point} :=
    ⟨firstThirdDart, hfirstThirdCycle⟩
  have hvertexFirstSecondEndpoints : vertex ∈ RS.endpoints firstSecondEdge := by
    apply (mem_simpleGraphRotationSystem_endpoints_iff
      graphData firstSecondEdge vertex).2
    exact hvertexFirstSecond
  have hvertexFirstThirdEndpoints : vertex ∈ RS.endpoints thirdFirstEdge := by
    apply (mem_simpleGraphRotationSystem_endpoints_iff
      graphData thirdFirstEdge vertex).2
    exact hvertexThirdFirst
  have hvertexFirstSecondPoint :
      vertex ∈ RS.endpoints (RS.edgeOf firstSecondPoint.1) := by
    rw [hfirstSecondEdge]
    exact hvertexFirstSecondEndpoints
  have hvertexFirstThirdPoint :
      vertex ∈ RS.endpoints (RS.edgeOf firstThirdPoint.1) := by
    rw [hfirstThirdEdge]
    exact hvertexFirstThirdEndpoints
  rcases exists_common_retainedVertex_of_ambient_endpoints
      RS keep outer firstRoot firstRoot hfirstRetained hfirstRetained
      firstSecondPoint firstThirdPoint vertex
      hvertexFirstSecondPoint hvertexFirstThirdPoint with
    ⟨openVertex, hfirstSecondOpen, hfirstThirdOpen⟩
  exact ⟨firstSecondPoint, firstThirdPoint, openVertex,
    hfirstSecondOpen, hfirstThirdOpen⟩

end

end GoertzelV24OpenRegionMinimalDualTriangleIncidence

end Mettapedia.GraphTheory.FourColor
