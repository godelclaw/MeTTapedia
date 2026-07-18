import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunSplice

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} [DecidableEq Vertex]
  {Graph : SimpleGraph Vertex}

/-- Two edge-disjoint paths with a common end produce a support-certified
cycle as soon as they meet at any other vertex. -/
theorem IsPath.exists_cycle_of_common_support_ne_end_of_edges_disjoint
    {firstStart secondStart commonEnd : Vertex}
    {first : Graph.Walk firstStart commonEnd}
    {second : Graph.Walk secondStart commonEnd}
    (hfirstPath : first.IsPath) (hsecondPath : second.IsPath)
    (hdisjoint : first.edges.Disjoint second.edges)
    {vertex : Vertex} (hfirstVertex : vertex ∈ first.support)
    (hsecondVertex : vertex ∈ second.support)
    (hne : vertex ≠ commonEnd) :
    ∃ root : Vertex, ∃ cycle : Graph.Walk root root,
      cycle.IsCycle ∧
        cycle.edges ⊆ first.edges ++ second.edges ∧
        cycle.length ≤ first.length + second.length := by
  let firstTail := first.dropUntil vertex hfirstVertex
  let secondTail := second.dropUntil vertex hsecondVertex
  have hfirstTailPath : firstTail.IsPath :=
    hfirstPath.dropUntil hfirstVertex
  have hsecondTailPath : secondTail.IsPath :=
    hsecondPath.dropUntil hsecondVertex
  have htailDisjoint : firstTail.edges.Disjoint secondTail.edges := by
    rw [List.disjoint_left]
    intro edge hfirstEdge hsecondEdge
    exact (List.disjoint_left.mp hdisjoint)
      ((first.isSubwalk_dropUntil hfirstVertex).edges_subset
        (by simpa only [firstTail] using hfirstEdge))
      ((second.isSubwalk_dropUntil hsecondVertex).edges_subset
        (by simpa only [secondTail] using hsecondEdge))
  have htailsNe : firstTail ≠ secondTail := by
    intro heq
    have hnotNil : ¬ firstTail.Nil :=
      SimpleGraph.Walk.not_nil_of_ne hne
    have hedgesNe : firstTail.edges ≠ [] :=
      SimpleGraph.Walk.edges_eq_nil.not.mpr hnotNil
    rcases List.exists_mem_of_ne_nil firstTail.edges hedgesNe with
      ⟨edge, hedge⟩
    have hsecondEdge : edge ∈ secondTail.edges := by
      rw [← heq]
      exact hedge
    exact (List.disjoint_left.mp htailDisjoint) hedge hsecondEdge
  rcases hfirstTailPath.exists_isCycle_of_ne hsecondTailPath htailsNe with
    ⟨left, right, firstPiece, secondPiece,
      hfirstPiece, hsecondPiece, hcycle⟩
  have hfirstSub : firstPiece.IsSubwalk first :=
    hfirstPiece.trans (first.isSubwalk_dropUntil hfirstVertex)
  have hsecondSub : secondPiece.IsSubwalk second :=
    hsecondPiece.trans (second.isSubwalk_dropUntil hsecondVertex)
  refine ⟨left, firstPiece.append secondPiece.reverse, hcycle, ?_, ?_⟩
  · intro edge hedge
    rw [SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse, List.mem_append,
      List.mem_reverse] at hedge
    rw [List.mem_append]
    exact hedge.imp
      (fun h ↦ hfirstSub.edges_subset h)
      (fun h ↦ hsecondSub.edges_subset h)
  · rw [SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse]
    exact Nat.add_le_add
      (length_le_of_isSubwalk hfirstSub)
      (length_le_of_isSubwalk hsecondSub)

/-- Dually, two edge-disjoint paths with a common start produce a
support-certified cycle as soon as they meet at any later vertex. -/
theorem IsPath.exists_cycle_of_common_support_ne_start_of_edges_disjoint
    {commonStart firstEnd secondEnd : Vertex}
    {first : Graph.Walk commonStart firstEnd}
    {second : Graph.Walk commonStart secondEnd}
    (hfirstPath : first.IsPath) (hsecondPath : second.IsPath)
    (hdisjoint : first.edges.Disjoint second.edges)
    {vertex : Vertex} (hfirstVertex : vertex ∈ first.support)
    (hsecondVertex : vertex ∈ second.support)
    (hne : vertex ≠ commonStart) :
    ∃ root : Vertex, ∃ cycle : Graph.Walk root root,
      cycle.IsCycle ∧
        cycle.edges ⊆ first.edges ++ second.edges ∧
        cycle.length ≤ first.length + second.length := by
  have hreverseDisjoint : first.reverse.edges.Disjoint
      second.reverse.edges := by
    simpa only [SimpleGraph.Walk.edges_reverse,
      List.disjoint_reverse_left, List.disjoint_reverse_right] using
        hdisjoint
  rcases hfirstPath.reverse.exists_cycle_of_common_support_ne_end_of_edges_disjoint
      hsecondPath.reverse hreverseDisjoint
      (by simpa only [SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using hfirstVertex)
      (by simpa only [SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using hsecondVertex) hne with
    ⟨root, cycle, hcycle, hedges, hlength⟩
  exact ⟨root, cycle, hcycle, by
    intro edge hedge
    have := hedges hedge
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_append,
      List.mem_reverse] using this, by
    simpa only [SimpleGraph.Walk.length_reverse] using hlength⟩

end SimpleGraph.Walk

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

/-- A cycle extracted from an extra intersection of the two incoming
arms or the two outgoing arms. -/
inductive LocalizedCommonRunParallelArmCycle
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) where
  | incoming
      (root : retainedVertexSet data.firstVertex data.secondVertex)
      (cycle : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk root root)
      (cycle_isCycle : cycle.IsCycle)
      (cycle_edges_subset : cycle.edges ⊆
        splice.trunk.prefixIncomingArm.edges ++
          splice.trunk.suffixIncomingArm.edges)
      (cycle_length_le : cycle.length ≤
        splice.trunk.prefixIncomingArm.length +
          splice.trunk.suffixIncomingArm.length)
  | outgoing
      (root : retainedVertexSet data.firstVertex data.secondVertex)
      (cycle : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk root root)
      (cycle_isCycle : cycle.IsCycle)
      (cycle_edges_subset : cycle.edges ⊆
        splice.trunk.prefixOutgoingArm.edges ++
          splice.trunk.suffixOutgoingArm.edges)
      (cycle_length_le : cycle.length ≤
        splice.trunk.prefixOutgoingArm.length +
          splice.trunk.suffixOutgoingArm.length)

/-- In the clean parallel-arm state, the incoming arms share only their
merge vertex and the outgoing arms share only their split vertex. -/
structure LocalizedCommonRunCleanParallelArms
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) where
  incoming_common_vertex : ∀ vertex,
    vertex ∈ splice.trunk.prefixIncomingArm.support →
      vertex ∈ splice.trunk.suffixIncomingArm.support →
      vertex = (pair.prefixSharedEdgeDart profile.firstRank).fst
  outgoing_common_vertex : ∀ vertex,
    vertex ∈ splice.trunk.prefixOutgoingArm.support →
      vertex ∈ splice.trunk.suffixOutgoingArm.support →
      vertex = (pair.prefixSharedEdgeDart profile.lastRank).snd

/-- Every four-arm splice either contains a support-certified cycle in
one of its parallel arm pairs or has unique merge and split intersections. -/
theorem LocalizedAlignedCommonRunSplice.parallelArmCycle_or_clean
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    Nonempty (LocalizedCommonRunParallelArmCycle splice) ∨
      Nonempty (LocalizedCommonRunCleanParallelArms splice) := by
  classical
  have harms := splice.arms_arePaths
  have hcross := splice.crossArms_pairwise_disjoint
  by_cases hincoming : ∃ vertex,
      vertex ∈ splice.trunk.prefixIncomingArm.support ∧
        vertex ∈ splice.trunk.suffixIncomingArm.support ∧
        vertex ≠ (pair.prefixSharedEdgeDart profile.firstRank).fst
  · rcases hincoming with
      ⟨vertex, hprefixVertex, hsuffixVertex, hne⟩
    rcases harms.1.exists_cycle_of_common_support_ne_end_of_edges_disjoint
        harms.2.2.1 hcross.1 hprefixVertex hsuffixVertex hne with
      ⟨root, cycle, hcycle, hedges, hlength⟩
    exact Or.inl ⟨LocalizedCommonRunParallelArmCycle.incoming
      root cycle hcycle hedges hlength⟩
  · have hincomingClean : ∀ vertex,
        vertex ∈ splice.trunk.prefixIncomingArm.support →
          vertex ∈ splice.trunk.suffixIncomingArm.support →
          vertex = (pair.prefixSharedEdgeDart profile.firstRank).fst := by
      intro vertex hprefixVertex hsuffixVertex
      by_contra hne
      exact hincoming ⟨vertex, hprefixVertex, hsuffixVertex, hne⟩
    by_cases houtgoing : ∃ vertex,
        vertex ∈ splice.trunk.prefixOutgoingArm.support ∧
          vertex ∈ splice.trunk.suffixOutgoingArm.support ∧
          vertex ≠ (pair.prefixSharedEdgeDart profile.lastRank).snd
    · rcases houtgoing with
        ⟨vertex, hprefixVertex, hsuffixVertex, hne⟩
      rcases harms.2.1.exists_cycle_of_common_support_ne_start_of_edges_disjoint
          harms.2.2.2 hcross.2.2.2 hprefixVertex hsuffixVertex hne with
        ⟨root, cycle, hcycle, hedges, hlength⟩
      exact Or.inl ⟨LocalizedCommonRunParallelArmCycle.outgoing
        root cycle hcycle hedges hlength⟩
    · exact Or.inr ⟨{
        incoming_common_vertex := hincomingClean
        outgoing_common_vertex := by
          intro vertex hprefixVertex hsuffixVertex
          by_contra hne
          exact houtgoing
            ⟨vertex, hprefixVertex, hsuffixVertex, hne⟩ }⟩

/-- The fusion-chain normal form with every four-arm splice resolved into
a parallel-arm cycle or unique merge and split intersections. -/
inductive LocalizedFusionChainVertexResolution
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  | parallelArmCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : LocalizedAlignedCommonRunSplice profile)
      (cycle : Nonempty (LocalizedCommonRunParallelArmCycle splice))
  | cleanParallelArms
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : LocalizedAlignedCommonRunSplice profile)
      (clean : Nonempty (LocalizedCommonRunCleanParallelArms splice))
  | alignedBubbleCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (bubble : Nonempty (LocalizedAlignedBubblePrimalCycle profile))
  | strictlyShorterMixedPortCycles
      (descent : Nonempty
        (LocalizedStrictlyShorterMixedPortCycles pair oldCross face))
  | orderInversionPrimalCycle
      (descent : Nonempty
        (LocalizedOrderInversionPrimalCycle pair oldCross face))

/-- Resolve every exact four-arm splice branch at its parallel-arm vertex
intersections. -/
theorem LocalizedFusionChainSpliceResolution.nonempty_vertexResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (resolution : LocalizedFusionChainSpliceResolution pair oldCross face) :
    Nonempty (LocalizedFusionChainVertexResolution pair oldCross face) := by
  cases resolution with
  | commonRunSplice profile splice =>
      rcases splice with ⟨splice⟩
      rcases splice.parallelArmCycle_or_clean with hcycle | hclean
      · exact ⟨LocalizedFusionChainVertexResolution.parallelArmCycle
          profile splice hcycle⟩
      · exact ⟨LocalizedFusionChainVertexResolution.cleanParallelArms
          profile splice hclean⟩
  | alignedBubbleCycle profile bubble =>
      exact ⟨LocalizedFusionChainVertexResolution.alignedBubbleCycle
        profile bubble⟩
  | strictlyShorterMixedPortCycles descent =>
      exact ⟨
        LocalizedFusionChainVertexResolution.strictlyShorterMixedPortCycles
          descent⟩
  | orderInversionPrimalCycle descent =>
      exact ⟨LocalizedFusionChainVertexResolution.orderInversionPrimalCycle
        descent⟩

/-- A width-at-least-two successor profile reaches the vertex-resolved
fusion-chain normal form under its inherited path certificates. -/
theorem LocalizedSuccessorFusionChainProfile.nonempty_vertexResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)}
    {suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3)}
    (successor : LocalizedSuccessorFusionChainProfile oldCross face
      prefixSuccessor suffixSuccessor)
    (hprefix : successor.pair.prefixTrail.IsPath)
    (hsuffix : successor.pair.suffixTrail.IsPath) :
    Nonempty (LocalizedFusionChainVertexResolution successor.pair oldCross
      face) := by
  rcases successor.nonempty_spliceResolution hprefix hsuffix with
    ⟨resolution⟩
  exact resolution.nonempty_vertexResolution

/-- The successor-pair trichotomy with its width-at-least-two branch
resolved at all parallel-arm vertex intersections. -/
def LocalizedFusionSuccessorResolution.VertexOutcome
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    {face : OrbitFace graphData.toRotationSystem}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    (successors : LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion) : Prop :=
    successors.prefixSuccessor.edges.Disjoint
        successors.suffixSuccessor.edges ∨
      (∃ (nextCross : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet)
          (nextPair : CrossCentralExactFaceCutPair graphData data nextCross),
        nextCross ≠ cross ∧
          retainedEdgeToAmbientEdge data nextCross ∈
            orbitFaceBoundary graphData.toRotationSystem face ∧
          nextPair.prefixTrail = successors.prefixSuccessor ∧
          nextPair.suffixTrail = successors.suffixSuccessor) ∨
      (∃ successor : LocalizedSuccessorFusionChainProfile cross face
          successors.prefixSuccessor successors.suffixSuccessor,
        Nonempty (LocalizedFusionChainVertexResolution successor.pair cross
          face))

/-- Every resolved successor pair realizes its vertex-refined outcome. -/
theorem LocalizedFusionSuccessorResolution.finite_vertex_outcome
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    {face : OrbitFace graphData.toRotationSystem}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    (successors : LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion) :
    successors.VertexOutcome := by
  unfold LocalizedFusionSuccessorResolution.VertexOutcome
  rcases successors.finite_outcome with hdisjoint | hrebase | hprofile
  · exact Or.inl hdisjoint
  · exact Or.inr (Or.inl hrebase)
  · rcases hprofile with ⟨successor⟩
    have hprefix : successor.pair.prefixTrail.IsPath := by
      rw [successor.prefix_eq]
      exact successors.prefix_isPath
    have hsuffix : successor.pair.suffixTrail.IsPath := by
      rw [successor.suffix_eq]
      exact successors.suffix_isPath
    exact Or.inr (Or.inr ⟨successor,
      successor.nonempty_vertexResolution hprefix hsuffix⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end


end Mettapedia.GraphTheory.FourColor
