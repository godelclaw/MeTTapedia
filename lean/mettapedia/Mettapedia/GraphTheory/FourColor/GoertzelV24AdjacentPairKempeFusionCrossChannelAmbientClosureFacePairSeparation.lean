import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureFaceCutPair
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceIntersections

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24MinimalFaceIntersections

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance ambientClosureFacePairGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The unordered pair of quotient faces incident to an edge, represented by
the two sides of a canonical dart. -/
def edgeOrbitFacePair (graphData : Data G) (edge : G.edgeSet) :
    Finset (OrbitFace graphData.toRotationSystem) :=
  {dartOrbitFace graphData.toRotationSystem
      (graphData.toRotationSystem.dartRepresentative edge),
    dartOrbitFace graphData.toRotationSystem
      (graphData.toRotationSystem.alpha
        (graphData.toRotationSystem.dartRepresentative edge))}

/-- Distinct edges of a graph-backed vertex-minimal spherical
counterexample have distinct unordered pairs of incident quotient faces. -/
theorem edgeOrbitFacePair_injective_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :
    Function.Injective (edgeOrbitFacePair graphData) := by
  intro first second hpairs
  let RS := graphData.toRotationSystem
  let firstDart := RS.dartRepresentative first
  let secondDart := RS.dartRepresentative second
  have hfirstEdge : RS.edgeOf firstDart = first :=
    RS.dartRepresentative_edgeOf first
  have hsecondEdge : RS.edgeOf secondDart = second :=
    RS.dartRepresentative_edgeOf second
  have hfaces : dartOrbitFace RS firstDart ≠
      dartOrbitFace RS (RS.alpha firstDart) :=
    minimal.facesTwoSided firstDart
  have hfirstLeft : first ∈
      orbitFaceBoundary RS (dartOrbitFace RS firstDart) := by
    rw [← hfirstEdge]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS firstDart
  have hfirstRight : first ∈
      orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha firstDart)) := by
    rw [← hfirstEdge, ← RS.edge_alpha firstDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS
      (RS.alpha firstDart)
  have hpair :
      ({dartOrbitFace RS firstDart,
          dartOrbitFace RS (RS.alpha firstDart)} :
        Finset (OrbitFace RS)) =
        {dartOrbitFace RS secondDart,
          dartOrbitFace RS (RS.alpha secondDart)} := by
    simpa only [edgeOrbitFacePair, RS, firstDart, secondDart] using hpairs
  have hsecondLeft : second ∈
      orbitFaceBoundary RS (dartOrbitFace RS firstDart) := by
    have hmem : dartOrbitFace RS firstDart ∈
        ({dartOrbitFace RS secondDart,
            dartOrbitFace RS (RS.alpha secondDart)} :
          Finset (OrbitFace RS)) := by
      rw [← hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem
    · rw [hmem, ← hsecondEdge]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS secondDart
    · rw [hmem, ← hsecondEdge, ← RS.edge_alpha secondDart]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS
        (RS.alpha secondDart)
  have hsecondRight : second ∈
      orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha firstDart)) := by
    have hmem : dartOrbitFace RS (RS.alpha firstDart) ∈
        ({dartOrbitFace RS secondDart,
            dartOrbitFace RS (RS.alpha secondDart)} :
          Finset (OrbitFace RS)) := by
      rw [← hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem
    · rw [hmem, ← hsecondEdge]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS secondDart
    · rw [hmem, ← hsecondEdge, ← RS.edge_alpha secondDart]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS
        (RS.alpha secondDart)
  exact edge_eq_of_mem_distinct_orbitFace_pair graphData minimal hfaces
    hfirstLeft hfirstRight hsecondLeft hsecondRight

end

end GoertzelV24MinimalFaceIntersections

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The selected retained cross edge and restored central edge have distinct
actual quotient-face incidence pairs in a graph-backed minimal map. Thus the
two binary cut coordinates do not collapse these edges to one facial pair. -/
theorem retainedCrossEdgeOrbitFacePair_ne_centralEdgeOrbitFacePair
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    edgeOrbitFacePair graphData (retainedEdgeToAmbientEdge data cross) ≠
      edgeOrbitFacePair graphData (centralEdge data) := by
  intro hpairs
  have hedges := edgeOrbitFacePair_injective_of_minimal
    graphData minimal hpairs
  exact retainedEdgeToAmbientEdge_ne_centralEdge data cross hedges

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
