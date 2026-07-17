import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionIntersection

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkFaceCut
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

/-- Any two opposite-port trails with one exact retained intersection can
be promoted to a cross-central exact face-cut pair in a graph-backed
minimal spherical map. -/
theorem exists_crossCentralExactFaceCutPair_of_exact_retainedIntersection
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hprefixTrail : (data.oppositePortClosure prefixTrail).IsTrail)
    (hsuffixTrail :
      (data.alternateOppositePortClosure suffixTrail).IsTrail)
    (hintersection : ∀ edge : Sym2
        (retainedVertexSet data.firstVertex data.secondVertex),
      edge ∈ prefixTrail.edges ∧ edge ∈ suffixTrail.edges ↔
        edge = cross.1) :
    ∃ pair : CrossCentralExactFaceCutPair graphData data cross,
      pair.prefixTrail = prefixTrail ∧ pair.suffixTrail = suffixTrail := by
  rcases exists_exactOrbitFaceCutPair_of_minimal graphData minimal
      (data.oppositePortClosure prefixTrail)
      (data.alternateOppositePortClosure suffixTrail)
      hprefixTrail hsuffixTrail with
    ⟨prefixLabels, suffixLabels, hprefixBoundary, hsuffixBoundary,
      hprefixExact, hsuffixExact, hjoint⟩
  have hedgesDistinct : (retainedEdgeToAmbientEdge data cross).1 ≠
      centralEdgeValue data := by
    intro hedge
    exact retainedEdgeToAmbientEdge_ne_centralEdge data cross
      (Subtype.ext hedge)
  have hjointExact : ∀ dart : graphData.toRotationSystem.D,
      (prefixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
            prefixLabels (dartOrbitFace graphData.toRotationSystem
              (graphData.toRotationSystem.alpha dart)) ∧
        suffixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
            suffixLabels (dartOrbitFace graphData.toRotationSystem
              (graphData.toRotationSystem.alpha dart))) ↔
        (graphData.toRotationSystem.edgeOf dart).1 =
            (retainedEdgeToAmbientEdge data cross).1 ∨
          (graphData.toRotationSystem.edgeOf dart).1 =
            centralEdgeValue data := by
    intro dart
    rw [hjoint dart]
    exact data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
      prefixTrail suffixTrail cross hintersection
        (graphData.toRotationSystem.edgeOf dart).1
  refine ⟨{
    prefixTrail := prefixTrail
    suffixTrail := suffixTrail
    prefixLabels := prefixLabels
    suffixLabels := suffixLabels
    prefixTrail_isTrail := hprefixTrail
    suffixTrail_isTrail := hsuffixTrail
    prefixBoundary := hprefixBoundary
    suffixBoundary := hsuffixBoundary
    prefixExact := hprefixExact
    suffixExact := hsuffixExact
    retainedIntersectionExact := hintersection
    edgesDistinct := hedgesDistinct
    jointExact := hjointExact }, rfl, rfl⟩

/-- A selected common edge of two successor paths becomes a new exact cross
whenever it is their unique common retained edge. -/
theorem exists_rebasedCrossCentralExactFaceCutPair_of_unique_successorIntersection
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (nextCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hprefixCycle :
      (data.oppositePortClosure prefixSuccessor).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure suffixSuccessor).IsCycle)
    (hprefixCross : nextCross.1 ∈ prefixSuccessor.edges)
    (hsuffixCross : nextCross.1 ∈ suffixSuccessor.edges)
    (hunique : ∀ candidate : (DeletedAdjacentPairGraph G
        data.firstVertex data.secondVertex).edgeSet,
      candidate.1 ∈ prefixSuccessor.edges →
        candidate.1 ∈ suffixSuccessor.edges →
          candidate = nextCross) :
    ∃ pair : CrossCentralExactFaceCutPair graphData data nextCross,
      pair.prefixTrail = prefixSuccessor ∧
        pair.suffixTrail = suffixSuccessor := by
  have hintersection : ∀ edge : Sym2
      (retainedVertexSet data.firstVertex data.secondVertex),
      edge ∈ prefixSuccessor.edges ∧ edge ∈ suffixSuccessor.edges ↔
        edge = nextCross.1 := by
    intro edge
    constructor
    · rintro ⟨hprefix, hsuffix⟩
      let candidate : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet :=
        ⟨edge, prefixSuccessor.edges_subset_edgeSet hprefix⟩
      exact congrArg Subtype.val (hunique candidate hprefix hsuffix)
    · intro hedge
      rw [hedge]
      exact ⟨hprefixCross, hsuffixCross⟩
  exact exists_crossCentralExactFaceCutPair_of_exact_retainedIntersection
    graphData minimal data nextCross prefixSuccessor suffixSuccessor
      hprefixCycle.isTrail hsuffixCycle.isTrail hintersection

/-- Under a singleton common-edge condition, the localized successor
alternative either completes as two edge-disjoint paths or rebases the
exact pair at a strictly different edge of the same remote face. -/
theorem CrossCentralExactFaceCutPair.successorEdges_disjoint_or_exists_rebasedExactPair
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
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
    (prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hprefixAvoids : cross.1 ∉ prefixSuccessor.edges)
    (hprefixCycle :
      (data.oppositePortClosure prefixSuccessor).IsCycle)
    (hprefixSubset : (data.retainedWalkToAmbient prefixSuccessor).edges ⊆
      firstFusion.edges)
    (suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hsuffixCycle :
      (data.alternateOppositePortClosure suffixSuccessor).IsCycle)
    (hsuffixSubset : (data.retainedWalkToAmbient suffixSuccessor).edges ⊆
      secondFusion.edges)
    (hsubsingleton : ∀ left right : (DeletedAdjacentPairGraph G
        data.firstVertex data.secondVertex).edgeSet,
      left.1 ∈ prefixSuccessor.edges →
      left.1 ∈ suffixSuccessor.edges →
      right.1 ∈ prefixSuccessor.edges →
      right.1 ∈ suffixSuccessor.edges → left = right) :
    prefixSuccessor.edges.Disjoint suffixSuccessor.edges ∨
      ∃ (nextCross : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet)
          (nextPair : CrossCentralExactFaceCutPair graphData data nextCross),
        nextCross ≠ cross ∧
          retainedEdgeToAmbientEdge data nextCross ∈
            orbitFaceBoundary graphData.toRotationSystem face ∧
          nextPair.prefixTrail = prefixSuccessor ∧
          nextPair.suffixTrail = suffixSuccessor := by
  rcases pair.successorEdges_disjoint_or_exists_remoteFaceIntersection
      face firstFusion hfirstSupport secondFusion hsecondSupport
      prefixSuccessor hprefixAvoids hprefixSubset suffixSuccessor
        hsuffixSubset with hdisjoint |
      ⟨nextCross, hprefixCross, hsuffixCross, hnextNe, hnextFace⟩
  · exact Or.inl hdisjoint
  · right
    have hunique : ∀ candidate : (DeletedAdjacentPairGraph G
        data.firstVertex data.secondVertex).edgeSet,
      candidate.1 ∈ prefixSuccessor.edges →
        candidate.1 ∈ suffixSuccessor.edges →
          candidate = nextCross := by
      intro candidate hcandidatePrefix hcandidateSuffix
      exact hsubsingleton candidate nextCross hcandidatePrefix
        hcandidateSuffix hprefixCross hsuffixCross
    rcases exists_rebasedCrossCentralExactFaceCutPair_of_unique_successorIntersection
        graphData minimal data nextCross prefixSuccessor suffixSuccessor
          hprefixCycle hsuffixCycle hprefixCross hsuffixCross hunique with
      ⟨nextPair, hprefixEq, hsuffixEq⟩
    exact ⟨nextCross, nextPair, hnextNe, hnextFace,
      hprefixEq, hsuffixEq⟩

/-- Two localized successors are edge-disjoint, yield an exact rebase at
their unique common edge, or have two distinct common edges on the same
remote face. -/
theorem CrossCentralExactFaceCutPair.successorEdges_disjoint_or_rebased_or_two_remoteFaceIntersections
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
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
    (prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hprefixAvoids : cross.1 ∉ prefixSuccessor.edges)
    (hprefixCycle :
      (data.oppositePortClosure prefixSuccessor).IsCycle)
    (hprefixSubset : (data.retainedWalkToAmbient prefixSuccessor).edges ⊆
      firstFusion.edges)
    (suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hsuffixCycle :
      (data.alternateOppositePortClosure suffixSuccessor).IsCycle)
    (hsuffixSubset : (data.retainedWalkToAmbient suffixSuccessor).edges ⊆
      secondFusion.edges) :
    prefixSuccessor.edges.Disjoint suffixSuccessor.edges ∨
      (∃ (nextCross : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet)
          (nextPair : CrossCentralExactFaceCutPair graphData data nextCross),
        nextCross ≠ cross ∧
          retainedEdgeToAmbientEdge data nextCross ∈
            orbitFaceBoundary graphData.toRotationSystem face ∧
          nextPair.prefixTrail = prefixSuccessor ∧
          nextPair.suffixTrail = suffixSuccessor) ∨
      ∃ left right : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet,
        left ≠ right ∧
          left.1 ∈ prefixSuccessor.edges ∧
          left.1 ∈ suffixSuccessor.edges ∧
          right.1 ∈ prefixSuccessor.edges ∧
          right.1 ∈ suffixSuccessor.edges ∧
          retainedEdgeToAmbientEdge data left ∈
            orbitFaceBoundary graphData.toRotationSystem face ∧
          retainedEdgeToAmbientEdge data right ∈
            orbitFaceBoundary graphData.toRotationSystem face := by
  classical
  by_cases hsubsingleton : ∀ left right : (DeletedAdjacentPairGraph G
      data.firstVertex data.secondVertex).edgeSet,
    left.1 ∈ prefixSuccessor.edges →
    left.1 ∈ suffixSuccessor.edges →
    right.1 ∈ prefixSuccessor.edges →
    right.1 ∈ suffixSuccessor.edges → left = right
  · rcases pair.successorEdges_disjoint_or_exists_rebasedExactPair minimal
        face firstFusion hfirstSupport secondFusion hsecondSupport
        prefixSuccessor hprefixAvoids hprefixCycle hprefixSubset
        suffixSuccessor hsuffixCycle hsuffixSubset hsubsingleton with
      hdisjoint | hrebase
    · exact Or.inl hdisjoint
    · exact Or.inr (Or.inl hrebase)
  · right
    right
    push Not at hsubsingleton
    rcases hsubsingleton with
      ⟨left, right, hleftPrefix, hleftSuffix, hrightPrefix,
        hrightSuffix, hne⟩
    have hleftFace := pair.successorIntersection_mem_remoteFace face
      firstFusion hfirstSupport secondFusion hsecondSupport
        prefixSuccessor hprefixAvoids hprefixSubset suffixSuccessor
        hsuffixSubset left hleftPrefix hleftSuffix
    have hrightFace := pair.successorIntersection_mem_remoteFace face
      firstFusion hfirstSupport secondFusion hsecondSupport
        prefixSuccessor hprefixAvoids hprefixSubset suffixSuccessor
        hsuffixSubset right hrightPrefix hrightSuffix
    exact ⟨left, right, hne, hleftPrefix, hleftSuffix,
      hrightPrefix, hrightSuffix, hleftFace, hrightFace⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
