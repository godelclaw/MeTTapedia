import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunVertexIntersection
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphTaitBridge

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

omit [DecidableEq Vertex] in
/-- A path vertex strictly after a cut index cannot occur in the support of
the prefix ending at that cut. -/
theorem IsPath.getVert_not_mem_support_take_of_lt
    {start finish : Vertex} {walk : Graph.Walk start finish}
    (hpath : walk.IsPath) {cut later : Nat} (hcutLater : cut < later)
    (hlater : later ≤ walk.length) :
    walk.getVert later ∉ (walk.take cut).support := by
  intro hmem
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem with
    ⟨position, hposition, hpositionLength⟩
  have htakeLength : (walk.take cut).length ≤ cut := by
    calc
      (walk.take cut).length = (walk.take cut).edges.length :=
        (walk.take cut).length_edges.symm
      _ = (walk.edges.take cut).length := by
        rw [SimpleGraph.Walk.edges_take]
      _ ≤ cut := List.length_take_le cut walk.edges
  have hpositionCut : position ≤ cut :=
    hpositionLength.trans htakeLength
  have hpositionFull : position ≤ walk.length := by
    omega
  have hvertices : walk.getVert position = walk.getVert later := by
    rw [← hposition, SimpleGraph.Walk.take_getVert,
      Nat.min_eq_right hpositionCut]
  have hindices := hpath.getVert_injOn
    (by simpa only [Set.mem_setOf_eq] using hpositionFull)
    (by simpa only [Set.mem_setOf_eq] using hlater)
    hvertices
  omega

omit [DecidableEq Vertex] in
/-- Two separated pieces of a path, one ending before the other begins,
have disjoint vertex supports. -/
theorem IsPath.support_take_disjoint_support_drop_of_lt
    {start finish : Vertex} {walk : Graph.Walk start finish}
    (hpath : walk.IsPath) {left right : Nat} (hleftRight : left < right)
    (hright : right ≤ walk.length) :
    (walk.take left).support.Disjoint (walk.drop right).support := by
  rw [List.disjoint_left]
  intro vertex hleftVertex hrightVertex
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hleftVertex with
    ⟨leftPosition, hleftPosition, hleftLength⟩
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hrightVertex with
    ⟨rightPosition, hrightPosition, hrightLength⟩
  have hleftPositionLe : leftPosition ≤ left := by
    simpa only [SimpleGraph.Walk.take_length,
      Nat.min_eq_left (hleftRight.le.trans hright)] using hleftLength
  have hrightPositionLe : right + rightPosition ≤ walk.length := by
    rw [SimpleGraph.Walk.drop_length] at hrightLength
    omega
  have hvertices :
      walk.getVert leftPosition = walk.getVert (right + rightPosition) := by
    calc
      walk.getVert leftPosition =
          (walk.take left).getVert leftPosition := by
        rw [SimpleGraph.Walk.take_getVert,
          Nat.min_eq_right hleftPositionLe]
      _ = vertex := hleftPosition
      _ = (walk.drop right).getVert rightPosition :=
        hrightPosition.symm
      _ = walk.getVert (right + rightPosition) := by
        rw [SimpleGraph.Walk.drop_getVert]
  have hindices := hpath.getVert_injOn
    (by
      simp only [Set.mem_setOf_eq]
      omega)
    (by simpa only [Set.mem_setOf_eq] using hrightPositionLe)
    hvertices
  omega

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

/-- The split vertex does not occur on the prefix incoming arm. -/
theorem LocalizedAlignedCommonRunSplice.split_not_mem_prefixIncoming_support
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    (pair.prefixSharedEdgeDart profile.lastRank).snd ∉
      splice.trunk.prefixIncomingArm.support := by
  have hpositions :
      (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val <
        (pair.prefixSharedEdgePositionEmbedding profile.lastRank).val + 1 := by
    have hlt := (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2
      profile.firstRank_lt_lastRank
    omega
  have hlater :
      (pair.prefixSharedEdgePositionEmbedding profile.lastRank).val + 1 ≤
        pair.prefixTrail.length := by
    have hlt :=
      (pair.prefixSharedEdgePositionEmbedding profile.lastRank).isLt
    have hlength := pair.prefixTrail.length_edges
    omega
  have hnot := splice.prefix_isPath.getVert_not_mem_support_take_of_lt
    hpositions hlater
  intro hsplit
  apply hnot
  simpa only [LocalizedAlignedCommonRunTrunk.prefixIncomingArm,
    SimpleGraph.Walk.support_copy,
    RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart,
    SimpleGraph.Walk.dartAtEdgePosition_snd] using hsplit

/-- The split vertex does not occur on the suffix incoming arm. -/
theorem LocalizedAlignedCommonRunSplice.split_not_mem_suffixIncoming_support
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    (pair.prefixSharedEdgeDart profile.lastRank).snd ∉
      splice.trunk.suffixIncomingArm.support := by
  have hpositions :
      (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv profile.firstRank)).val <
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv profile.lastRank)).val + 1 := by
    have hlt := (pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2
      (profile.sharedEdgeOrderEquiv_lt profile.firstRank_lt_lastRank)
    omega
  have hlater :
      (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv profile.lastRank)).val + 1 ≤
        pair.suffixTrail.length := by
    have hlt := (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv profile.lastRank)).isLt
    have hlength := pair.suffixTrail.length_edges
    omega
  have hnot := splice.suffix_isPath.getVert_not_mem_support_take_of_lt
    hpositions hlater
  intro hsplit
  apply hnot
  rw [LocalizedAlignedCommonRunTrunk.suffixIncomingArm,
    SimpleGraph.Walk.support_copy] at hsplit
  have hsplitVertex :
      pair.suffixTrail.getVert
          ((pair.suffixSharedEdgePositionEmbedding
            (pair.sharedEdgeOrderEquiv profile.lastRank)).val + 1) =
        (pair.prefixSharedEdgeDart profile.lastRank).snd := by
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
          (profile.darts_eq profile.lastRank)
  rw [hsplitVertex]
  exact hsplit

/-- The incoming and outgoing prefix arms have disjoint vertex supports. -/
theorem LocalizedAlignedCommonRunSplice.prefixArms_support_disjoint
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    splice.trunk.prefixIncomingArm.support.Disjoint
      splice.trunk.prefixOutgoingArm.support := by
  have hpositions :
      (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val <
        (pair.prefixSharedEdgePositionEmbedding profile.lastRank).val + 1 := by
    have hlt := (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2
      profile.firstRank_lt_lastRank
    omega
  have hlater :
      (pair.prefixSharedEdgePositionEmbedding profile.lastRank).val + 1 ≤
        pair.prefixTrail.length := by
    have hlt :=
      (pair.prefixSharedEdgePositionEmbedding profile.lastRank).isLt
    have hlength := pair.prefixTrail.length_edges
    omega
  simpa only [LocalizedAlignedCommonRunTrunk.prefixIncomingArm,
    LocalizedAlignedCommonRunTrunk.prefixOutgoingArm,
    SimpleGraph.Walk.support_copy] using
      splice.prefix_isPath.support_take_disjoint_support_drop_of_lt
        hpositions hlater

/-- The incoming and outgoing suffix arms have disjoint vertex supports. -/
theorem LocalizedAlignedCommonRunSplice.suffixArms_support_disjoint
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    splice.trunk.suffixIncomingArm.support.Disjoint
      splice.trunk.suffixOutgoingArm.support := by
  have hpositions :
      (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv profile.firstRank)).val <
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv profile.lastRank)).val + 1 := by
    have hlt := (pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2
      (profile.sharedEdgeOrderEquiv_lt profile.firstRank_lt_lastRank)
    omega
  have hlater :
      (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv profile.lastRank)).val + 1 ≤
        pair.suffixTrail.length := by
    have hlt := (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv profile.lastRank)).isLt
    have hlength := pair.suffixTrail.length_edges
    omega
  simpa only [LocalizedAlignedCommonRunTrunk.suffixIncomingArm,
    LocalizedAlignedCommonRunTrunk.suffixOutgoingArm,
    SimpleGraph.Walk.support_copy] using
      splice.suffix_isPath.support_take_disjoint_support_drop_of_lt
        hpositions hlater

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

/-- In the clean crossed-arm state, both crossed pairs have disjoint vertex
supports. -/
structure LocalizedCommonRunCleanCrossedArms
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) where
  prefixIncoming_suffixOutgoing_disjoint :
    splice.trunk.prefixIncomingArm.support.Disjoint
      splice.trunk.suffixOutgoingArm.support
  suffixIncoming_prefixOutgoing_disjoint :
    splice.trunk.suffixIncomingArm.support.Disjoint
      splice.trunk.prefixOutgoingArm.support

/-- The complete clean intersection matrix for a four-arm splice. Parallel
incoming arms meet only at the merge, parallel outgoing arms meet only at
the split, and all four remaining arm pairs have disjoint vertex supports. -/
structure LocalizedCommonRunCleanFourArms
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) where
  parallel : LocalizedCommonRunCleanParallelArms splice
  crossed : LocalizedCommonRunCleanCrossedArms splice
  prefixIncoming_prefixOutgoing_disjoint :
    splice.trunk.prefixIncomingArm.support.Disjoint
      splice.trunk.prefixOutgoingArm.support
  suffixIncoming_suffixOutgoing_disjoint :
    splice.trunk.suffixIncomingArm.support.Disjoint
      splice.trunk.suffixOutgoingArm.support

/-- Parallel and crossed cleanliness assemble into the complete six-pair
intersection matrix. -/
def LocalizedAlignedCommonRunSplice.toCleanFourArms
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (parallel : LocalizedCommonRunCleanParallelArms splice)
    (crossed : LocalizedCommonRunCleanCrossedArms splice) :
    LocalizedCommonRunCleanFourArms splice where
  parallel := parallel
  crossed := crossed
  prefixIncoming_prefixOutgoing_disjoint :=
    splice.prefixArms_support_disjoint
  suffixIncoming_suffixOutgoing_disjoint :=
    splice.suffixArms_support_disjoint

/-- The three possible incoming-arm states at the common-trunk merge. At
most one incoming arm can collapse because its two starting ports are
distinct. -/
inductive LocalizedCommonRunMergeArmState
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) where
  | internal
      (prefix_not_nil : ¬ splice.trunk.prefixIncomingArm.Nil)
      (suffix_not_nil : ¬ splice.trunk.suffixIncomingArm.Nil)
  | prefixPort
      (prefix_nil : splice.trunk.prefixIncomingArm.Nil)
      (merge_eq_port :
        (pair.prefixSharedEdgeDart profile.firstRank).fst =
          data.retainedPort 0)
      (suffix_not_nil : ¬ splice.trunk.suffixIncomingArm.Nil)
  | suffixPort
      (suffix_nil : splice.trunk.suffixIncomingArm.Nil)
      (merge_eq_port :
        (pair.prefixSharedEdgeDart profile.firstRank).fst =
          data.retainedPort 1)
      (prefix_not_nil : ¬ splice.trunk.prefixIncomingArm.Nil)

/-- The three possible outgoing-arm states at the common-trunk split. At
most one outgoing arm can collapse because its two ending ports are
distinct. -/
inductive LocalizedCommonRunSplitArmState
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) where
  | internal
      (prefix_not_nil : ¬ splice.trunk.prefixOutgoingArm.Nil)
      (suffix_not_nil : ¬ splice.trunk.suffixOutgoingArm.Nil)
  | prefixPort
      (prefix_nil : splice.trunk.prefixOutgoingArm.Nil)
      (split_eq_port :
        (pair.prefixSharedEdgeDart profile.lastRank).snd =
          data.retainedPort 2)
      (suffix_not_nil : ¬ splice.trunk.suffixOutgoingArm.Nil)
  | suffixPort
      (suffix_nil : splice.trunk.suffixOutgoingArm.Nil)
      (split_eq_port :
        (pair.prefixSharedEdgeDart profile.lastRank).snd =
          data.retainedPort 3)
      (prefix_not_nil : ¬ splice.trunk.prefixOutgoingArm.Nil)

/-- Every merge is either internal to both incoming arms or is exactly one
of their two distinct starting ports. -/
def LocalizedAlignedCommonRunSplice.mergeArmState
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    LocalizedCommonRunMergeArmState splice := by
  by_cases hprefix : splice.trunk.prefixIncomingArm.Nil
  · have hsuffix : ¬ splice.trunk.suffixIncomingArm.Nil := by
      intro hsuffix
      exact (data.retainedPort_injective.ne
        (by decide : (0 : Fin 4) ≠ 1))
        (hprefix.eq.trans hsuffix.eq.symm)
    exact LocalizedCommonRunMergeArmState.prefixPort hprefix
      hprefix.eq.symm hsuffix
  · by_cases hsuffix : splice.trunk.suffixIncomingArm.Nil
    · exact LocalizedCommonRunMergeArmState.suffixPort hsuffix
        hsuffix.eq.symm hprefix
    · exact LocalizedCommonRunMergeArmState.internal hprefix hsuffix

/-- Every split is either internal to both outgoing arms or is exactly one
of their two distinct ending ports. -/
def LocalizedAlignedCommonRunSplice.splitArmState
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    LocalizedCommonRunSplitArmState splice := by
  by_cases hprefix : splice.trunk.prefixOutgoingArm.Nil
  · have hsuffix : ¬ splice.trunk.suffixOutgoingArm.Nil := by
      intro hsuffix
      exact (data.retainedPort_injective.ne
        (by decide : (2 : Fin 4) ≠ 3))
        (hprefix.eq.symm.trans hsuffix.eq)
    exact LocalizedCommonRunSplitArmState.prefixPort hprefix
      hprefix.eq hsuffix
  · by_cases hsuffix : splice.trunk.suffixOutgoingArm.Nil
    · exact LocalizedCommonRunSplitArmState.suffixPort hsuffix
        hsuffix.eq hprefix
    · exact LocalizedCommonRunSplitArmState.internal hprefix hsuffix

/-- If both incoming arms are nonempty, the merge is not one of the four
retained ports. -/
theorem LocalizedCommonRunCleanFourArms.merge_ne_retainedPort_of_internal
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (clean : LocalizedCommonRunCleanFourArms splice)
    (hprefix : ¬ splice.trunk.prefixIncomingArm.Nil)
    (hsuffix : ¬ splice.trunk.suffixIncomingArm.Nil) :
    ∀ port : Fin 4,
      (pair.prefixSharedEdgeDart profile.firstRank).fst ≠
        data.retainedPort port := by
  intro port
  fin_cases port
  · intro heq
    exact hprefix ((splice.arms_arePaths.1.nil_iff_eq).2 heq.symm)
  · intro heq
    exact hsuffix ((splice.arms_arePaths.2.2.1.nil_iff_eq).2 heq.symm)
  · intro heq
    have heq' :
        (pair.prefixSharedEdgeDart profile.firstRank).fst =
          data.retainedPort 2 := by simpa using heq
    exact (List.disjoint_left.mp
        clean.prefixIncoming_prefixOutgoing_disjoint)
      (by
        rw [← heq']
        exact splice.trunk.prefixIncomingArm.end_mem_support)
      splice.trunk.prefixOutgoingArm.end_mem_support
  · intro heq
    have heq' :
        (pair.prefixSharedEdgeDart profile.firstRank).fst =
          data.retainedPort 3 := by simpa using heq
    exact (List.disjoint_left.mp
        clean.crossed.prefixIncoming_suffixOutgoing_disjoint)
      (by
        rw [← heq']
        exact splice.trunk.prefixIncomingArm.end_mem_support)
      splice.trunk.suffixOutgoingArm.end_mem_support

/-- If both outgoing arms are nonempty, the split is not one of the four
retained ports. -/
theorem LocalizedCommonRunCleanFourArms.split_ne_retainedPort_of_internal
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (clean : LocalizedCommonRunCleanFourArms splice)
    (hprefix : ¬ splice.trunk.prefixOutgoingArm.Nil)
    (hsuffix : ¬ splice.trunk.suffixOutgoingArm.Nil) :
    ∀ port : Fin 4,
      (pair.prefixSharedEdgeDart profile.lastRank).snd ≠
        data.retainedPort port := by
  intro port
  fin_cases port
  · intro heq
    have heq' :
        (pair.prefixSharedEdgeDart profile.lastRank).snd =
          data.retainedPort 0 := by simpa using heq
    exact (List.disjoint_left.mp
        clean.prefixIncoming_prefixOutgoing_disjoint)
      splice.trunk.prefixIncomingArm.start_mem_support
      (by
        rw [← heq']
        exact splice.trunk.prefixOutgoingArm.start_mem_support)
  · intro heq
    have heq' :
        (pair.prefixSharedEdgeDart profile.lastRank).snd =
          data.retainedPort 1 := by simpa using heq
    exact (List.disjoint_left.mp
        clean.suffixIncoming_suffixOutgoing_disjoint)
      splice.trunk.suffixIncomingArm.start_mem_support
      (by
        rw [← heq']
        exact splice.trunk.suffixOutgoingArm.start_mem_support)
  · intro heq
    exact hprefix ((splice.arms_arePaths.2.1.nil_iff_eq).2 heq)
  · intro heq
    exact hsuffix ((splice.arms_arePaths.2.2.2.nil_iff_eq).2 heq)

/-- The retained degree prescribed by a merge-arm state. -/
def LocalizedCommonRunMergeArmState.retainedDegree
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunMergeArmState splice → Nat
  | .internal _ _ => 3
  | .prefixPort _ _ _ => 2
  | .suffixPort _ _ _ => 2

/-- The retained degree prescribed by a split-arm state. -/
def LocalizedCommonRunSplitArmState.retainedDegree
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunSplitArmState splice → Nat
  | .internal _ _ => 3
  | .prefixPort _ _ _ => 2
  | .suffixPort _ _ _ => 2

/-- In a cubic ambient graph, the merge has exactly the retained degree
specified by its internal-or-port state. -/
theorem LocalizedCommonRunCleanFourArms.merge_incidentEdgeFinset_card
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (clean : LocalizedCommonRunCleanFourArms splice)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (state : LocalizedCommonRunMergeArmState splice) :
    (incidentEdgeFinset
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
      (pair.prefixSharedEdgeDart profile.firstRank).fst).card =
        state.retainedDegree := by
  have hambient : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    GoertzelV24SimpleGraphTaitBridge.incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData hcubic
  have hwell := data.degreeTwoBoundaryData_wellFormed hambient
  cases state with
  | internal hprefix hsuffix =>
      exact hwell.2.2 _
        (clean.merge_ne_retainedPort_of_internal hprefix hsuffix)
  | prefixPort _ heq _ =>
      rw [heq]
      exact hwell.2.1 0
  | suffixPort _ heq _ =>
      rw [heq]
      exact hwell.2.1 1

/-- In a cubic ambient graph, the split has exactly the retained degree
specified by its internal-or-port state. -/
theorem LocalizedCommonRunCleanFourArms.split_incidentEdgeFinset_card
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (clean : LocalizedCommonRunCleanFourArms splice)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (state : LocalizedCommonRunSplitArmState splice) :
    (incidentEdgeFinset
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
      (pair.prefixSharedEdgeDart profile.lastRank).snd).card =
        state.retainedDegree := by
  have hambient : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    GoertzelV24SimpleGraphTaitBridge.incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData hcubic
  have hwell := data.degreeTwoBoundaryData_wellFormed hambient
  cases state with
  | internal hprefix hsuffix =>
      exact hwell.2.2 _
        (clean.split_ne_retainedPort_of_internal hprefix hsuffix)
  | prefixPort _ heq _ =>
      rw [heq]
      exact hwell.2.1 2
  | suffixPort _ heq _ =>
      rw [heq]
      exact hwell.2.1 3

/-- Every four-arm splice either contains a support-certified cycle in
a crossed arm pair, closed through the common trunk, or both crossed arm
pairs have disjoint vertex supports. -/
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
        prefixIncoming_suffixOutgoing_disjoint := by
          rw [List.disjoint_left]
          intro vertex hprefixVertex hsuffixVertex
          have heq := hprefixSuffixClean vertex hprefixVertex hsuffixVertex
          exact splice.split_not_mem_prefixIncoming_support
            (heq ▸ hprefixVertex)
        suffixIncoming_prefixOutgoing_disjoint := by
          rw [List.disjoint_left]
          intro vertex hsuffixVertex hprefixVertex
          have heq :
              vertex =
                (pair.prefixSharedEdgeDart profile.lastRank).snd := by
            by_contra hne
            exact hsuffixPrefix
              ⟨vertex, hsuffixVertex, hprefixVertex, hne⟩
          exact splice.split_not_mem_suffixIncoming_support
            (heq ▸ hsuffixVertex) }⟩

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
      (clean : Nonempty (LocalizedCommonRunCleanFourArms splice))
      (mergeState : LocalizedCommonRunMergeArmState splice)
      (splitState : LocalizedCommonRunSplitArmState splice)
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
      · rcases parallel with ⟨parallel⟩
        rcases crossed with ⟨crossed⟩
        exact ⟨LocalizedFusionChainCrossedResolution.cleanFourArms
          profile splice ⟨splice.toCleanFourArms parallel crossed⟩
            splice.mergeArmState splice.splitArmState⟩
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
