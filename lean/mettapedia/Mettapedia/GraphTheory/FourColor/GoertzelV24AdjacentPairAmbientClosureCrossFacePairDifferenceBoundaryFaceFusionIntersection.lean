import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionSuccessor

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- If both cross-free fusion successors use a retained edge, that edge
comes from the remote facial boundary. The old exact closures cannot supply
it: their only common edges are the omitted cross and the deleted central
edge. -/
theorem CrossCentralExactFaceCutPair.successorIntersection_mem_remoteFace
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (face : OrbitFace graphData.toRotationSystem)
    {firstRoot : V} (firstFusion : G.Walk firstRoot firstRoot)
    (hfirstSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ firstFusion.edges →
        edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    {secondRoot : V} (secondFusion : G.Walk secondRoot secondRoot)
    (hsecondSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ secondFusion.edges →
        edge.1 ∈
            (data.alternateOppositePortClosure pair.suffixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (firstSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hfirstCross : cross.1 ∉ firstSuccessor.edges)
    (hfirstSubset : (data.retainedWalkToAmbient firstSuccessor).edges ⊆
      firstFusion.edges)
    (secondSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hsecondSubset : (data.retainedWalkToAmbient secondSuccessor).edges ⊆
      secondFusion.edges)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hfirst : edge.1 ∈ firstSuccessor.edges)
    (hsecond : edge.1 ∈ secondSuccessor.edges) :
    retainedEdgeToAmbientEdge data edge ∈
      orbitFaceBoundary graphData.toRotationSystem face := by
  have hfirstAmbient : (retainedEdgeToAmbientEdge data edge).1 ∈
      (data.retainedWalkToAmbient firstSuccessor).edges :=
    (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
      data firstSuccessor edge).2 hfirst
  have hsecondAmbient : (retainedEdgeToAmbientEdge data edge).1 ∈
      (data.retainedWalkToAmbient secondSuccessor).edges :=
    (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
      data secondSuccessor edge).2 hsecond
  rcases hfirstSupport (retainedEdgeToAmbientEdge data edge)
      (hfirstSubset hfirstAmbient) with hfirstClosure | hfirstFace
  · rcases hsecondSupport (retainedEdgeToAmbientEdge data edge)
        (hsecondSubset hsecondAmbient) with hsecondClosure | hsecondFace
    · have hcommon :=
        (data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
          pair.prefixTrail pair.suffixTrail cross
            pair.retainedIntersectionExact
              (retainedEdgeToAmbientEdge data edge).1).1
          ⟨hfirstClosure, hsecondClosure⟩
      rcases hcommon with hcross | hcentral
      · have hambient : retainedEdgeToAmbientEdge data edge =
            retainedEdgeToAmbientEdge data cross := Subtype.ext hcross
        have hedge : edge = cross :=
          data.retainedEdgeToAmbientEdge_injective hambient
        exact False.elim (hfirstCross (hedge ▸ hfirst))
      · exact False.elim
          ((retainedEdgeToAmbientEdge_ne_centralEdge data edge)
            (Subtype.ext hcentral))
    · exact hsecondFace
  · exact hfirstFace

/-- The two cross-free successors therefore have an exact geometric
alternative: they are edge-disjoint, or one can select a common retained
edge whose ambient image lies on the remote face. -/
theorem CrossCentralExactFaceCutPair.successorEdges_disjoint_or_exists_remoteFaceIntersection
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (face : OrbitFace graphData.toRotationSystem)
    {firstRoot : V} (firstFusion : G.Walk firstRoot firstRoot)
    (hfirstSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ firstFusion.edges →
        edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    {secondRoot : V} (secondFusion : G.Walk secondRoot secondRoot)
    (hsecondSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ secondFusion.edges →
        edge.1 ∈
            (data.alternateOppositePortClosure pair.suffixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (firstSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hfirstCross : cross.1 ∉ firstSuccessor.edges)
    (hfirstSubset : (data.retainedWalkToAmbient firstSuccessor).edges ⊆
      firstFusion.edges)
    (secondSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hsecondSubset : (data.retainedWalkToAmbient secondSuccessor).edges ⊆
      secondFusion.edges) :
    firstSuccessor.edges.Disjoint secondSuccessor.edges ∨
      ∃ edge : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet,
        edge.1 ∈ firstSuccessor.edges ∧
          edge.1 ∈ secondSuccessor.edges ∧
          retainedEdgeToAmbientEdge data edge ∈
            orbitFaceBoundary graphData.toRotationSystem face := by
  by_cases hdisjoint :
      firstSuccessor.edges.Disjoint secondSuccessor.edges
  · exact Or.inl hdisjoint
  · right
    rw [List.disjoint_left] at hdisjoint
    push Not at hdisjoint
    rcases hdisjoint with ⟨edgeValue, hfirst, hsecond⟩
    let edge : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet :=
      ⟨edgeValue, firstSuccessor.edges_subset_edgeSet hfirst⟩
    refine ⟨edge, hfirst, hsecond, ?_⟩
    exact pair.successorIntersection_mem_remoteFace face
      firstFusion hfirstSupport secondFusion hsecondSupport
        firstSuccessor hfirstCross hfirstSubset secondSuccessor
          hsecondSubset edge hfirst hsecond

/-- Resolving a pair of cross-free remote-face fusions leaves only three
compositional outcomes. One fusion is already a retained cycle, both
central returns expose edge-disjoint successor paths, or the exposed paths
have a selected common edge on the remote face. -/
theorem CrossCentralExactFaceCutPair.fusionCyclePair_retainedCycle_or_successorPair
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    {firstRoot : V} (firstFusion : G.Walk firstRoot firstRoot)
    (hfirstCycle : firstFusion.IsCycle)
    (hfirstCross : (retainedEdgeToAmbientEdge data cross).1 ∉
      firstFusion.edges)
    (hfirstSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ firstFusion.edges →
        edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    {secondRoot : V} (secondFusion : G.Walk secondRoot secondRoot)
    (hsecondCycle : secondFusion.IsCycle)
    (hsecondCross : (retainedEdgeToAmbientEdge data cross).1 ∉
      secondFusion.edges)
    (hsecondSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ secondFusion.edges →
        edge.1 ∈
            (data.alternateOppositePortClosure pair.suffixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face) :
    ( ∃ (hroot : firstRoot ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨firstRoot, hroot⟩ ⟨firstRoot, hroot⟩),
      retainedFusion.IsCycle ∧
        data.retainedWalkToAmbient retainedFusion = firstFusion) ∨
    ( ∃ (hroot : secondRoot ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨secondRoot, hroot⟩ ⟨secondRoot, hroot⟩),
      retainedFusion.IsCycle ∧
        data.retainedWalkToAmbient retainedFusion = secondFusion) ∨
    ∃ (firstSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2))
        (secondSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 1) (data.retainedPort 3)),
      firstSuccessor.IsPath ∧
        cross.1 ∉ firstSuccessor.edges ∧
        (data.oppositePortClosure firstSuccessor).IsCycle ∧
        (data.retainedWalkToAmbient firstSuccessor).edges ⊆
          firstFusion.edges ∧
      secondSuccessor.IsPath ∧
        cross.1 ∉ secondSuccessor.edges ∧
        (data.alternateOppositePortClosure secondSuccessor).IsCycle ∧
        (data.retainedWalkToAmbient secondSuccessor).edges ⊆
          secondFusion.edges ∧
      (firstSuccessor.edges.Disjoint secondSuccessor.edges ∨
        ∃ edge : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet,
          edge.1 ∈ firstSuccessor.edges ∧
            edge.1 ∈ secondSuccessor.edges ∧
            retainedEdgeToAmbientEdge data edge ∈
              orbitFaceBoundary graphData.toRotationSystem face) := by
  rcases pair.fusionCyclePair_resolution face hboundary
      firstFusion hfirstCycle hfirstCross hfirstSupport
      secondFusion hsecondCycle hsecondCross hsecondSupport with
    ⟨hfirst, hsecond⟩
  rcases hfirst with hfirstRetained |
      ⟨firstSuccessor, hfirstPath, hfirstAvoids, hfirstClosure,
        hfirstSubset⟩
  · exact Or.inl hfirstRetained
  · rcases hsecond with hsecondRetained |
        ⟨secondSuccessor, hsecondPath, hsecondAvoids, hsecondClosure,
          hsecondSubset⟩
    · exact Or.inr (Or.inl hsecondRetained)
    · right
      right
      refine ⟨firstSuccessor, secondSuccessor,
        hfirstPath, hfirstAvoids, hfirstClosure, hfirstSubset,
        hsecondPath, hsecondAvoids, hsecondClosure, hsecondSubset, ?_⟩
      exact pair.successorEdges_disjoint_or_exists_remoteFaceIntersection
        face firstFusion hfirstSupport secondFusion hsecondSupport
          firstSuccessor hfirstAvoids hfirstSubset secondSuccessor
            hsecondSubset

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
