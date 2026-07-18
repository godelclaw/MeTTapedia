import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunVertexIntersection

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} [DecidableEq Vertex]
  {Graph : SimpleGraph Vertex}

/-- If a path into a junction and an edge-disjoint path out of that
junction meet at another vertex, their two segments to the junction contain
a support-certified cycle. -/
theorem IsPath.exists_cycle_of_incoming_outgoing_common_vertex
    {incomingStart junction outgoingEnd : Vertex}
    {incoming : Graph.Walk incomingStart junction}
    {outgoing : Graph.Walk junction outgoingEnd}
    (hincomingPath : incoming.IsPath) (houtgoingPath : outgoing.IsPath)
    (hdisjoint : incoming.edges.Disjoint outgoing.edges)
    {vertex : Vertex} (hincomingVertex : vertex ∈ incoming.support)
    (houtgoingVertex : vertex ∈ outgoing.support)
    (hne : vertex ≠ junction) :
    ∃ root : Vertex, ∃ cycle : Graph.Walk root root,
      cycle.IsCycle ∧
        cycle.edges ⊆ incoming.edges ++ outgoing.edges ∧
        cycle.length ≤ incoming.length + outgoing.length := by
  let incomingTail := incoming.dropUntil vertex hincomingVertex
  let outgoingHead := outgoing.takeUntil vertex houtgoingVertex
  have hincomingTailPath : incomingTail.IsPath :=
    hincomingPath.dropUntil hincomingVertex
  have houtgoingHeadReversePath : outgoingHead.reverse.IsPath :=
    (houtgoingPath.takeUntil houtgoingVertex).reverse
  have hsegmentsDisjoint : incomingTail.edges.Disjoint
      outgoingHead.reverse.edges := by
    rw [List.disjoint_left]
    intro edge hincomingEdge houtgoingEdge
    have hincomingFull : edge ∈ incoming.edges :=
      (incoming.isSubwalk_dropUntil hincomingVertex).edges_subset
        (by simpa only [incomingTail] using hincomingEdge)
    have houtgoingHeadEdge : edge ∈ outgoingHead.edges := by
      simpa only [SimpleGraph.Walk.edges_reverse,
        List.mem_reverse] using houtgoingEdge
    have houtgoingFull : edge ∈ outgoing.edges :=
      (outgoing.isSubwalk_takeUntil houtgoingVertex).edges_subset
        (by simpa only [outgoingHead] using houtgoingHeadEdge)
    exact (List.disjoint_left.mp hdisjoint)
      hincomingFull houtgoingFull
  rcases hincomingTailPath.exists_cycle_of_common_support_ne_end_of_edges_disjoint
      houtgoingHeadReversePath hsegmentsDisjoint
      incomingTail.start_mem_support outgoingHead.reverse.start_mem_support
      hne with
    ⟨root, cycle, hcycle, hedges, hlength⟩
  refine ⟨root, cycle, hcycle, ?_, ?_⟩
  · intro edge hedge
    have hedgeSegments :
        edge ∈ incomingTail.edges ++ outgoingHead.reverse.edges :=
      hedges hedge
    rw [List.mem_append] at hedgeSegments
    rcases hedgeSegments with hincomingEdge | houtgoingEdge
    · exact List.mem_append_left _
        ((incoming.isSubwalk_dropUntil hincomingVertex).edges_subset
          (by simpa only [incomingTail] using hincomingEdge))
    · apply List.mem_append_right
      exact (outgoing.isSubwalk_takeUntil houtgoingVertex).edges_subset
        (by
          have : edge ∈ outgoingHead.edges := by
            simpa only [SimpleGraph.Walk.edges_reverse,
              List.mem_reverse] using houtgoingEdge
          simpa only [outgoingHead] using this)
  · calc
      cycle.length ≤ incomingTail.length + outgoingHead.reverse.length :=
        hlength
      _ ≤ incoming.length + outgoing.length := by
        rw [SimpleGraph.Walk.length_reverse]
        exact Nat.add_le_add
          (length_le_of_isSubwalk
            (incoming.isSubwalk_dropUntil hincomingVertex))
          (length_le_of_isSubwalk
            (outgoing.isSubwalk_takeUntil houtgoingVertex))

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

/-- The prefix successor from its first port through the final edge of the
common trunk. -/
def LocalizedAlignedCommonRunSplice.prefixThroughTrunk
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (_splice : LocalizedAlignedCommonRunSplice profile) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 0)
      (pair.prefixSharedEdgeDart profile.lastRank).snd :=
  (pair.prefixTrail.take
    ((pair.prefixSharedEdgePositionEmbedding profile.lastRank).val + 1)).copy
      rfl (by
        simp only [RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart,
          SimpleGraph.Walk.dartAtEdgePosition_snd])

/-- The suffix successor from its first port through the final edge of the
same oriented common trunk. -/
def LocalizedAlignedCommonRunSplice.suffixThroughTrunk
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (_splice : LocalizedAlignedCommonRunSplice profile) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 1)
      (pair.prefixSharedEdgeDart profile.lastRank).snd :=
  (pair.suffixTrail.take
    ((pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv profile.lastRank)).val + 1)).copy rfl (by
        calc
          pair.suffixTrail.getVert
                ((pair.suffixSharedEdgePositionEmbedding
                  (pair.sharedEdgeOrderEquiv profile.lastRank)).val + 1) =
              (pair.suffixSharedEdgeDart profile.lastRank).snd := by
            simp only [
              RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDart,
              SimpleGraph.Walk.dartAtEdgePosition_snd]
          _ = (pair.prefixSharedEdgeDart profile.lastRank).snd :=
            congrArg (fun dart ↦ dart.snd)
              (profile.darts_eq profile.lastRank))

/-- The prefix walk through the common trunk is a path. -/
theorem LocalizedAlignedCommonRunSplice.prefixThroughTrunk_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    splice.prefixThroughTrunk.IsPath := by
  rw [LocalizedAlignedCommonRunSplice.prefixThroughTrunk,
    SimpleGraph.Walk.isPath_copy]
  exact splice.prefix_isPath.take _

/-- The suffix walk through the common trunk is a path. -/
theorem LocalizedAlignedCommonRunSplice.suffixThroughTrunk_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    splice.suffixThroughTrunk.IsPath := by
  rw [LocalizedAlignedCommonRunSplice.suffixThroughTrunk,
    SimpleGraph.Walk.isPath_copy]
  exact splice.suffix_isPath.take _

/-- The prefix walk through the common trunk uses only prefix-successor
edges. -/
theorem LocalizedAlignedCommonRunSplice.prefixThroughTrunk_edges_subset
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    splice.prefixThroughTrunk.edges ⊆ pair.prefixTrail.edges := by
  intro edge hedge
  exact (SimpleGraph.Walk.isSubwalk_take pair.prefixTrail _).edges_subset
    (by simpa only [LocalizedAlignedCommonRunSplice.prefixThroughTrunk,
      SimpleGraph.Walk.edges_copy] using hedge)

/-- The suffix walk through the common trunk uses only suffix-successor
edges. -/
theorem LocalizedAlignedCommonRunSplice.suffixThroughTrunk_edges_subset
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    splice.suffixThroughTrunk.edges ⊆ pair.suffixTrail.edges := by
  intro edge hedge
  exact (SimpleGraph.Walk.isSubwalk_take pair.suffixTrail _).edges_subset
    (by simpa only [LocalizedAlignedCommonRunSplice.suffixThroughTrunk,
      SimpleGraph.Walk.edges_copy] using hedge)

/-- The prefix incoming arm is supported on the prefix walk through the
trunk. -/
theorem LocalizedAlignedCommonRunSplice.prefixIncoming_support_subset_throughTrunk
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    ∀ vertex, vertex ∈ splice.trunk.prefixIncomingArm.support →
      vertex ∈ splice.prefixThroughTrunk.support := by
  intro vertex hvertex
  have hpositions :
      (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val ≤
        (pair.prefixSharedEdgePositionEmbedding profile.lastRank).val + 1 := by
    have hlt := (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2
      profile.firstRank_lt_lastRank
    omega
  have hsub := pair.prefixTrail.take_isSubwalk_take hpositions
  rw [LocalizedAlignedCommonRunSplice.prefixThroughTrunk,
    SimpleGraph.Walk.support_copy]
  exact hsub.support_subset (by
    simpa only [LocalizedAlignedCommonRunTrunk.prefixIncomingArm,
      SimpleGraph.Walk.support_copy] using hvertex)

/-- The suffix incoming arm is supported on the suffix walk through the
trunk. -/
theorem LocalizedAlignedCommonRunSplice.suffixIncoming_support_subset_throughTrunk
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    ∀ vertex, vertex ∈ splice.trunk.suffixIncomingArm.support →
      vertex ∈ splice.suffixThroughTrunk.support := by
  intro vertex hvertex
  have hpositions :
      (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv profile.firstRank)).val ≤
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv profile.lastRank)).val + 1 := by
    have hlt := (pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2
      (profile.sharedEdgeOrderEquiv_lt profile.firstRank_lt_lastRank)
    omega
  have hsub := pair.suffixTrail.take_isSubwalk_take hpositions
  rw [LocalizedAlignedCommonRunSplice.suffixThroughTrunk,
    SimpleGraph.Walk.support_copy]
  exact hsub.support_subset (by
    simpa only [LocalizedAlignedCommonRunTrunk.suffixIncomingArm,
      SimpleGraph.Walk.support_copy] using hvertex)

/-- The prefix walk through the trunk and the suffix outgoing arm share no
edge. -/
theorem LocalizedAlignedCommonRunSplice.prefixThroughTrunk_disjoint_suffixOutgoing
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    splice.prefixThroughTrunk.edges.Disjoint
      splice.trunk.suffixOutgoingArm.edges := by
  rw [List.disjoint_left]
  intro edge hprefix hsuffix
  exact (List.disjoint_left.mp
      splice.trunk.suffixOutgoingArm_disjoint_prefixTrail)
    hsuffix (splice.prefixThroughTrunk_edges_subset hprefix)

/-- The suffix walk through the trunk and the prefix outgoing arm share no
edge. -/
theorem LocalizedAlignedCommonRunSplice.suffixThroughTrunk_disjoint_prefixOutgoing
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    splice.suffixThroughTrunk.edges.Disjoint
      splice.trunk.prefixOutgoingArm.edges := by
  rw [List.disjoint_left]
  intro edge hsuffix hprefix
  exact (List.disjoint_left.mp
      splice.trunk.prefixOutgoingArm_disjoint_suffixTrail)
    hprefix (splice.suffixThroughTrunk_edges_subset hsuffix)

/-- A cycle extracted from an extra intersection of crossed arms, closed
through the common trunk. -/
inductive LocalizedCommonRunCrossedArmCycle
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) where
  | prefixIncoming_suffixOutgoing
      (root : retainedVertexSet data.firstVertex data.secondVertex)
      (cycle : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk root root)
      (cycle_isCycle : cycle.IsCycle)
      (cycle_edges_subset : cycle.edges ⊆
        splice.prefixThroughTrunk.edges ++
          splice.trunk.suffixOutgoingArm.edges)
      (cycle_length_le : cycle.length ≤
        splice.prefixThroughTrunk.length +
          splice.trunk.suffixOutgoingArm.length)
  | suffixIncoming_prefixOutgoing
      (root : retainedVertexSet data.firstVertex data.secondVertex)
      (cycle : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk root root)
      (cycle_isCycle : cycle.IsCycle)
      (cycle_edges_subset : cycle.edges ⊆
        splice.suffixThroughTrunk.edges ++
          splice.trunk.prefixOutgoingArm.edges)
      (cycle_length_le : cycle.length ≤
        splice.suffixThroughTrunk.length +
          splice.trunk.prefixOutgoingArm.length)

/-- In the clean crossed-arm state, either crossed pair can meet only at
the common-trunk split vertex. -/
structure LocalizedCommonRunCleanCrossedArms
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) where
  prefixIncoming_suffixOutgoing_common_vertex : ∀ vertex,
    vertex ∈ splice.trunk.prefixIncomingArm.support →
      vertex ∈ splice.trunk.suffixOutgoingArm.support →
      vertex = (pair.prefixSharedEdgeDart profile.lastRank).snd
  suffixIncoming_prefixOutgoing_common_vertex : ∀ vertex,
    vertex ∈ splice.trunk.suffixIncomingArm.support →
      vertex ∈ splice.trunk.prefixOutgoingArm.support →
      vertex = (pair.prefixSharedEdgeDart profile.lastRank).snd

/-- Every four-arm splice either contains a support-certified cycle in
a crossed arm pair, closed through the common trunk, or has no crossed
intersection away from the split vertex. -/
theorem LocalizedAlignedCommonRunSplice.crossedArmCycle_or_clean
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    Nonempty (LocalizedCommonRunCrossedArmCycle splice) ∨
      Nonempty (LocalizedCommonRunCleanCrossedArms splice) := by
  classical
  have harms := splice.arms_arePaths
  by_cases hprefixSuffix : ∃ vertex,
      vertex ∈ splice.trunk.prefixIncomingArm.support ∧
        vertex ∈ splice.trunk.suffixOutgoingArm.support ∧
        vertex ≠ (pair.prefixSharedEdgeDart profile.lastRank).snd
  · rcases hprefixSuffix with
      ⟨vertex, hprefixVertex, hsuffixVertex, hne⟩
    rcases (splice.prefixThroughTrunk_isPath).exists_cycle_of_incoming_outgoing_common_vertex
          harms.2.2.2
          splice.prefixThroughTrunk_disjoint_suffixOutgoing
          (splice.prefixIncoming_support_subset_throughTrunk
            vertex hprefixVertex)
          hsuffixVertex hne with
      ⟨root, cycle, hcycle, hedges, hlength⟩
    exact Or.inl ⟨
      LocalizedCommonRunCrossedArmCycle.prefixIncoming_suffixOutgoing
        root cycle hcycle hedges hlength⟩
  · have hprefixSuffixClean : ∀ vertex,
        vertex ∈ splice.trunk.prefixIncomingArm.support →
          vertex ∈ splice.trunk.suffixOutgoingArm.support →
          vertex = (pair.prefixSharedEdgeDart profile.lastRank).snd := by
      intro vertex hprefixVertex hsuffixVertex
      by_contra hne
      exact hprefixSuffix
        ⟨vertex, hprefixVertex, hsuffixVertex, hne⟩
    by_cases hsuffixPrefix : ∃ vertex,
        vertex ∈ splice.trunk.suffixIncomingArm.support ∧
          vertex ∈ splice.trunk.prefixOutgoingArm.support ∧
          vertex ≠ (pair.prefixSharedEdgeDart profile.lastRank).snd
    · rcases hsuffixPrefix with
        ⟨vertex, hsuffixVertex, hprefixVertex, hne⟩
      rcases (splice.suffixThroughTrunk_isPath).exists_cycle_of_incoming_outgoing_common_vertex
            harms.2.1
            splice.suffixThroughTrunk_disjoint_prefixOutgoing
            (splice.suffixIncoming_support_subset_throughTrunk
              vertex hsuffixVertex)
            hprefixVertex hne with
        ⟨root, cycle, hcycle, hedges, hlength⟩
      exact Or.inl ⟨
        LocalizedCommonRunCrossedArmCycle.suffixIncoming_prefixOutgoing
          root cycle hcycle hedges hlength⟩
    · exact Or.inr ⟨{
        prefixIncoming_suffixOutgoing_common_vertex := hprefixSuffixClean
        suffixIncoming_prefixOutgoing_common_vertex := by
          intro vertex hsuffixVertex hprefixVertex
          by_contra hne
          exact hsuffixPrefix
            ⟨vertex, hsuffixVertex, hprefixVertex, hne⟩ }⟩

/-- The fusion-chain normal form with both parallel and crossed arm
intersections resolved. -/
inductive LocalizedFusionChainCrossedResolution
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  | parallelArmCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : LocalizedAlignedCommonRunSplice profile)
      (cycle : Nonempty (LocalizedCommonRunParallelArmCycle splice))
  | crossedArmCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : LocalizedAlignedCommonRunSplice profile)
      (cycle : Nonempty (LocalizedCommonRunCrossedArmCycle splice))
  | cleanFourArms
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : LocalizedAlignedCommonRunSplice profile)
      (parallel : Nonempty (LocalizedCommonRunCleanParallelArms splice))
      (crossed : Nonempty (LocalizedCommonRunCleanCrossedArms splice))
  | alignedBubbleCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (bubble : Nonempty (LocalizedAlignedBubblePrimalCycle profile))
  | strictlyShorterMixedPortCycles
      (descent : Nonempty
        (LocalizedStrictlyShorterMixedPortCycles pair oldCross face))
  | orderInversionPrimalCycle
      (descent : Nonempty
        (LocalizedOrderInversionPrimalCycle pair oldCross face))

/-- Resolve the clean-parallel branch of the vertex normal form at its
two crossed arm pairs. -/
theorem LocalizedFusionChainVertexResolution.nonempty_crossedResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (resolution : LocalizedFusionChainVertexResolution pair oldCross face) :
    Nonempty (LocalizedFusionChainCrossedResolution pair oldCross face) := by
  cases resolution with
  | parallelArmCycle profile splice cycle =>
      exact ⟨LocalizedFusionChainCrossedResolution.parallelArmCycle
        profile splice cycle⟩
  | cleanParallelArms profile splice parallel =>
      rcases splice.crossedArmCycle_or_clean with cycle | crossed
      · exact ⟨LocalizedFusionChainCrossedResolution.crossedArmCycle
          profile splice cycle⟩
      · exact ⟨LocalizedFusionChainCrossedResolution.cleanFourArms
          profile splice parallel crossed⟩
  | alignedBubbleCycle profile bubble =>
      exact ⟨LocalizedFusionChainCrossedResolution.alignedBubbleCycle
        profile bubble⟩
  | strictlyShorterMixedPortCycles descent =>
      exact ⟨
        LocalizedFusionChainCrossedResolution.strictlyShorterMixedPortCycles
          descent⟩
  | orderInversionPrimalCycle descent =>
      exact ⟨LocalizedFusionChainCrossedResolution.orderInversionPrimalCycle
        descent⟩

/-- A width-at-least-two successor profile reaches the arm-intersection
resolved fusion-chain normal form under its inherited path certificates. -/
theorem LocalizedSuccessorFusionChainProfile.nonempty_crossedResolution
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
    Nonempty (LocalizedFusionChainCrossedResolution successor.pair oldCross
      face) := by
  rcases successor.nonempty_vertexResolution hprefix hsuffix with
    ⟨resolution⟩
  exact resolution.nonempty_crossedResolution

/-- The successor-pair trichotomy with its width-at-least-two branch
resolved at every parallel and crossed arm intersection. -/
def LocalizedFusionSuccessorResolution.CrossedOutcome
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
        Nonempty (LocalizedFusionChainCrossedResolution successor.pair cross
          face))

/-- Every resolved successor pair realizes its arm-intersection-refined
outcome. -/
theorem LocalizedFusionSuccessorResolution.finite_crossed_outcome
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
    successors.CrossedOutcome := by
  unfold LocalizedFusionSuccessorResolution.CrossedOutcome
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
      successor.nonempty_crossedResolution hprefix hsuffix⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
