import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileSignedMonodromy

namespace List

/-- In a duplicate-free list, the element at a position does not occur
strictly before that position. -/
theorem Nodup.get_not_mem_take {Alpha : Type*} {items : List Alpha}
    (hnodup : items.Nodup) (position : Fin items.length) :
    items.get position ∉ items.take position.val := by
  intro hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨index, hindex, heq⟩
  have hindexLt : index < position.val := by
    simpa using hindex
  have heqFull : items[index] = items[position.val] := by
    simpa using heq
  have hpositions : index = position.val :=
    hnodup.getElem_inj_iff.mp heqFull
  omega

/-- In a duplicate-free list, the element at a position does not occur
strictly after that position. -/
theorem Nodup.get_not_mem_drop_succ {Alpha : Type*} {items : List Alpha}
    (hnodup : items.Nodup) (position : Fin items.length) :
    items.get position ∉ items.drop (position.val + 1) := by
  intro hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨index, hindex, heq⟩
  have hshiftedLt : position.val + 1 + index < items.length := by
    rw [List.length_drop] at hindex
    have hposition := position.isLt
    omega
  let shifted : Fin items.length :=
    ⟨position.val + 1 + index, hshiftedLt⟩
  have heqFull : items.get shifted = items.get position := by
    change items[position.val + 1 + index] = items.get position
    simpa only [List.getElem_drop] using heq
  have hpositions : position.val + 1 + index = position.val :=
    hnodup.getElem_inj_iff.mp heqFull
  omega

end List

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} {Graph : SimpleGraph Vertex}

/-- The source of the dart at an exact edge position is the vertex just
before that edge. -/
@[simp] theorem dartAtEdgePosition_fst {left right : Vertex}
    (walk : Graph.Walk left right)
    (position : Fin walk.edges.length) :
    (walk.dartAtEdgePosition position).fst =
      walk.getVert position.val := by
  simp [dartAtEdgePosition, SimpleGraph.Walk.darts_getElem_eq_getVert]

/-- The target of the dart at an exact edge position is the vertex just
after that edge. -/
@[simp] theorem dartAtEdgePosition_snd {left right : Vertex}
    (walk : Graph.Walk left right)
    (position : Fin walk.edges.length) :
    (walk.dartAtEdgePosition position).snd =
      walk.getVert (position.val + 1) := by
  simp [dartAtEdgePosition, SimpleGraph.Walk.darts_getElem_eq_getVert]

/-- If two walks traverse selected copies of one edge in opposite
directions, switch from the prefix of the first walk to the suffix of the
second immediately after that edge.  The common edge itself is omitted. -/
def prefixFirstSuffixSecondAtReversedDart
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hreverse : secondWalk.dartAtEdgePosition secondPosition =
      (firstWalk.dartAtEdgePosition firstPosition).symm) :
    Graph.Walk firstLeft secondRight :=
  let hjoin : secondWalk.getVert (secondPosition.val + 1) =
      firstWalk.getVert firstPosition.val := by
    simpa using congrArg (fun dart => dart.snd) hreverse
  (firstWalk.take firstPosition.val).append
    ((secondWalk.drop (secondPosition.val + 1)).copy hjoin rfl)

/-- The complementary switch follows the prefix of the second walk and
the suffix of the first, again omitting the oppositely traversed edge. -/
def prefixSecondSuffixFirstAtReversedDart
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hreverse : secondWalk.dartAtEdgePosition secondPosition =
      (firstWalk.dartAtEdgePosition firstPosition).symm) :
    Graph.Walk secondLeft firstRight :=
  let hjoin : firstWalk.getVert (firstPosition.val + 1) =
      secondWalk.getVert secondPosition.val := by
    simpa using (congrArg (fun dart => dart.fst) hreverse).symm
  (secondWalk.take secondPosition.val).append
    ((firstWalk.drop (firstPosition.val + 1)).copy hjoin rfl)

/-- The first switch contains exactly the strict first prefix followed by
the strict second suffix. -/
@[simp] theorem prefixFirstSuffixSecondAtReversedDart_edges
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hreverse : secondWalk.dartAtEdgePosition secondPosition =
      (firstWalk.dartAtEdgePosition firstPosition).symm) :
    (firstWalk.prefixFirstSuffixSecondAtReversedDart secondWalk
        firstPosition secondPosition hreverse).edges =
      firstWalk.edges.take firstPosition.val ++
        secondWalk.edges.drop (secondPosition.val + 1) := by
  simp [prefixFirstSuffixSecondAtReversedDart,
    SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_take,
    SimpleGraph.Walk.edges_drop]

/-- The complementary switch contains exactly the strict second prefix
followed by the strict first suffix. -/
@[simp] theorem prefixSecondSuffixFirstAtReversedDart_edges
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hreverse : secondWalk.dartAtEdgePosition secondPosition =
      (firstWalk.dartAtEdgePosition firstPosition).symm) :
    (firstWalk.prefixSecondSuffixFirstAtReversedDart secondWalk
        firstPosition secondPosition hreverse).edges =
      secondWalk.edges.take secondPosition.val ++
        firstWalk.edges.drop (firstPosition.val + 1) := by
  simp [prefixSecondSuffixFirstAtReversedDart,
    SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_take,
    SimpleGraph.Walk.edges_drop]

/-- If both source edge lists are duplicate-free, the selected common
edge is absent from the first switched walk. -/
theorem selectedEdge_not_mem_prefixFirstSuffixSecondAtReversedDart_edges
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hreverse : secondWalk.dartAtEdgePosition secondPosition =
      (firstWalk.dartAtEdgePosition firstPosition).symm)
    (hfirstNodup : firstWalk.edges.Nodup)
    (hsecondNodup : secondWalk.edges.Nodup) :
    firstWalk.edges.get firstPosition ∉
      (firstWalk.prefixFirstSuffixSecondAtReversedDart secondWalk
        firstPosition secondPosition hreverse).edges := by
  have hedge : secondWalk.edges.get secondPosition =
      firstWalk.edges.get firstPosition := by
    have hdartEdge := congrArg SimpleGraph.Dart.edge hreverse
    simpa using hdartEdge
  rw [prefixFirstSuffixSecondAtReversedDart_edges]
  intro hmem
  rcases List.mem_append.mp hmem with hprefix | hsuffix
  · exact hfirstNodup.get_not_mem_take firstPosition hprefix
  · apply hsecondNodup.get_not_mem_drop_succ secondPosition
    rw [hedge]
    exact hsuffix

/-- Under the same hypothesis, the common edge is absent from the
complementary switched walk as well. -/
theorem selectedEdge_not_mem_prefixSecondSuffixFirstAtReversedDart_edges
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hreverse : secondWalk.dartAtEdgePosition secondPosition =
      (firstWalk.dartAtEdgePosition firstPosition).symm)
    (hfirstNodup : firstWalk.edges.Nodup)
    (hsecondNodup : secondWalk.edges.Nodup) :
    firstWalk.edges.get firstPosition ∉
      (firstWalk.prefixSecondSuffixFirstAtReversedDart secondWalk
        firstPosition secondPosition hreverse).edges := by
  have hedge : secondWalk.edges.get secondPosition =
      firstWalk.edges.get firstPosition := by
    have hdartEdge := congrArg SimpleGraph.Dart.edge hreverse
    simpa using hdartEdge
  rw [prefixSecondSuffixFirstAtReversedDart_edges]
  intro hmem
  rcases List.mem_append.mp hmem with hprefix | hsuffix
  · apply hsecondNodup.get_not_mem_take secondPosition
    rw [hedge]
    exact hprefix
  · exact hfirstNodup.get_not_mem_drop_succ firstPosition hsuffix

/-- Exact length of the first switched walk. -/
@[simp] theorem prefixFirstSuffixSecondAtReversedDart_length
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hreverse : secondWalk.dartAtEdgePosition secondPosition =
      (firstWalk.dartAtEdgePosition firstPosition).symm) :
    (firstWalk.prefixFirstSuffixSecondAtReversedDart secondWalk
        firstPosition secondPosition hreverse).length =
      firstPosition.val +
        (secondWalk.length - (secondPosition.val + 1)) := by
  simp only [prefixFirstSuffixSecondAtReversedDart,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length]
  have hfirst : firstPosition.val < firstWalk.length := by
    simpa using firstPosition.isLt
  omega

/-- Exact length of the complementary switched walk. -/
@[simp] theorem prefixSecondSuffixFirstAtReversedDart_length
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hreverse : secondWalk.dartAtEdgePosition secondPosition =
      (firstWalk.dartAtEdgePosition firstPosition).symm) :
    (firstWalk.prefixSecondSuffixFirstAtReversedDart secondWalk
        firstPosition secondPosition hreverse).length =
      secondPosition.val +
        (firstWalk.length - (firstPosition.val + 1)) := by
  simp only [prefixSecondSuffixFirstAtReversedDart,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length]
  have hsecond : secondPosition.val < secondWalk.length := by
    simpa using secondPosition.isLt
  omega

/-- The two switches together remove exactly the two selected edge
occurrences from the total source length. -/
theorem reversedDartSplices_length_add_add_two
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hreverse : secondWalk.dartAtEdgePosition secondPosition =
      (firstWalk.dartAtEdgePosition firstPosition).symm) :
    (firstWalk.prefixFirstSuffixSecondAtReversedDart secondWalk
          firstPosition secondPosition hreverse).length +
        (firstWalk.prefixSecondSuffixFirstAtReversedDart secondWalk
          firstPosition secondPosition hreverse).length + 2 =
      firstWalk.length + secondWalk.length := by
  rw [prefixFirstSuffixSecondAtReversedDart_length,
    prefixSecondSuffixFirstAtReversedDart_length]
  have hfirst : firstPosition.val < firstWalk.length := by
    simpa using firstPosition.isLt
  have hsecond : secondPosition.val < secondWalk.length := by
    simpa using secondPosition.isLt
  omega

/-- Consequently, the total switched length is strictly smaller than the
total length of the two source walks. -/
theorem reversedDartSplices_length_add_lt
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hreverse : secondWalk.dartAtEdgePosition secondPosition =
      (firstWalk.dartAtEdgePosition firstPosition).symm) :
    (firstWalk.prefixFirstSuffixSecondAtReversedDart secondWalk
          firstPosition secondPosition hreverse).length +
        (firstWalk.prefixSecondSuffixFirstAtReversedDart secondWalk
          firstPosition secondPosition hreverse).length <
      firstWalk.length + secondWalk.length := by
  have hsum := firstWalk.reversedDartSplices_length_add_add_two secondWalk
    firstPosition secondPosition hreverse
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

/-- Switch from the `0–2` profile path to the `1–3` profile path after
an oppositely traversed shared edge.  This is the mixed `0–3` channel. -/
def RetainedIntersectionExactFaceCutPair.zeroToThreeSpliceAtReversedSharedEdge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 0) (data.retainedPort 3) :=
  pair.prefixTrail.prefixFirstSuffixSecondAtReversedDart pair.suffixTrail
    (pair.prefixSharedEdgePositionEmbedding position)
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv position)) hreverse

/-- The complementary switch is the mixed `1–2` channel. -/
def RetainedIntersectionExactFaceCutPair.oneToTwoSpliceAtReversedSharedEdge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 1) (data.retainedPort 2) :=
  pair.prefixTrail.prefixSecondSuffixFirstAtReversedDart pair.suffixTrail
    (pair.prefixSharedEdgePositionEmbedding position)
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv position)) hreverse

/-- Bypass any repeated vertices in the switched `0–3` walk. -/
def RetainedIntersectionExactFaceCutPair.zeroToThreePathAtReversedSharedEdge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 0) (data.retainedPort 3) :=
  (pair.zeroToThreeSpliceAtReversedSharedEdge position hreverse).bypass

/-- Bypass any repeated vertices in the complementary `1–2` walk. -/
def RetainedIntersectionExactFaceCutPair.oneToTwoPathAtReversedSharedEdge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 1) (data.retainedPort 2) :=
  (pair.oneToTwoSpliceAtReversedSharedEdge position hreverse).bypass

/-- The switched `0–3` reduction is a path. -/
theorem RetainedIntersectionExactFaceCutPair.zeroToThreePathAtReversedSharedEdge_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (pair.zeroToThreePathAtReversedSharedEdge position hreverse).IsPath :=
  (pair.zeroToThreeSpliceAtReversedSharedEdge position hreverse).bypass_isPath

/-- The switched `1–2` reduction is a path. -/
theorem RetainedIntersectionExactFaceCutPair.oneToTwoPathAtReversedSharedEdge_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (pair.oneToTwoPathAtReversedSharedEdge position hreverse).IsPath :=
  (pair.oneToTwoSpliceAtReversedSharedEdge position hreverse).bypass_isPath

/-- The selected shared edge is physically absent from the raw `0–3`
switch. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_not_mem_zeroToThreeSplice_edges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (pair.sharedEdgeAt position).1 ∉
      (pair.zeroToThreeSpliceAtReversedSharedEdge position hreverse).edges := by
  have hselected : (pair.sharedEdgeAt position).1 =
      pair.prefixTrail.edges.get
        (pair.prefixSharedEdgePositionEmbedding position) := by
    exact pair.prefixSharedEdgePositionEmbedding_preserves_edge position
  rw [hselected]
  exact pair.prefixTrail.selectedEdge_not_mem_prefixFirstSuffixSecondAtReversedDart_edges
    pair.suffixTrail (pair.prefixSharedEdgePositionEmbedding position)
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv position)) hreverse
      pair.prefixRetained_isTrail.edges_nodup
      pair.suffixRetained_isTrail.edges_nodup

/-- The complementary raw switch omits the same physical edge. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_not_mem_oneToTwoSplice_edges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (pair.sharedEdgeAt position).1 ∉
      (pair.oneToTwoSpliceAtReversedSharedEdge position hreverse).edges := by
  have hselected : (pair.sharedEdgeAt position).1 =
      pair.prefixTrail.edges.get
        (pair.prefixSharedEdgePositionEmbedding position) := by
    exact pair.prefixSharedEdgePositionEmbedding_preserves_edge position
  rw [hselected]
  exact pair.prefixTrail.selectedEdge_not_mem_prefixSecondSuffixFirstAtReversedDart_edges
    pair.suffixTrail (pair.prefixSharedEdgePositionEmbedding position)
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv position)) hreverse
      pair.prefixRetained_isTrail.edges_nodup
      pair.suffixRetained_isTrail.edges_nodup

/-- Bypassing the `0–3` switch cannot reintroduce the removed edge. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_not_mem_zeroToThreePath_edges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (pair.sharedEdgeAt position).1 ∉
      (pair.zeroToThreePathAtReversedSharedEdge position hreverse).edges := by
  intro hmem
  apply pair.sharedEdgeAt_not_mem_zeroToThreeSplice_edges position hreverse
  exact SimpleGraph.Walk.edges_bypass_subset_edges
    (pair.zeroToThreeSpliceAtReversedSharedEdge position hreverse) hmem

/-- Nor can bypassing the `1–2` switch reintroduce it. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_not_mem_oneToTwoPath_edges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (pair.sharedEdgeAt position).1 ∉
      (pair.oneToTwoPathAtReversedSharedEdge position hreverse).edges := by
  intro hmem
  apply pair.sharedEdgeAt_not_mem_oneToTwoSplice_edges position hreverse
  exact SimpleGraph.Walk.edges_bypass_subset_edges
    (pair.oneToTwoSpliceAtReversedSharedEdge position hreverse) hmem

/-- At the profile level, the two raw switches remove exactly two edge
occurrences from the two source trails. -/
theorem RetainedIntersectionExactFaceCutPair.reversedSharedEdgeSplices_length_add_add_two
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (pair.zeroToThreeSpliceAtReversedSharedEdge position hreverse).length +
        (pair.oneToTwoSpliceAtReversedSharedEdge position hreverse).length +
        2 =
      pair.prefixTrail.length + pair.suffixTrail.length := by
  exact pair.prefixTrail.reversedDartSplices_length_add_add_two
    pair.suffixTrail (pair.prefixSharedEdgePositionEmbedding position)
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv position)) hreverse

/-- Path reduction cannot increase either switched length, so the total
mixed-channel path length remains strictly smaller than the source total. -/
theorem RetainedIntersectionExactFaceCutPair.reversedSharedEdgePaths_length_add_lt
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (pair.zeroToThreePathAtReversedSharedEdge position hreverse).length +
        (pair.oneToTwoPathAtReversedSharedEdge position hreverse).length <
      pair.prefixTrail.length + pair.suffixTrail.length := by
  have hzero :=
    (pair.zeroToThreeSpliceAtReversedSharedEdge position hreverse).length_bypass_le_length
  have hone :=
    (pair.oneToTwoSpliceAtReversedSharedEdge position hreverse).length_bypass_le_length
  have hsum := pair.reversedSharedEdgeSplices_length_add_add_two
    position hreverse
  change
    (pair.zeroToThreeSpliceAtReversedSharedEdge position hreverse).bypass.length +
        (pair.oneToTwoSpliceAtReversedSharedEdge position hreverse).bypass.length <
      pair.prefixTrail.length + pair.suffixTrail.length
  omega

/-- Closing the switched `0–3` path through the restored adjacent pair
produces a genuine mixed-channel cycle. -/
theorem RetainedIntersectionExactFaceCutPair.zeroToThreeCrossSidePortClosure_isCycle
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (data.crossSidePortClosure 0 1
      (pair.zeroToThreePathAtReversedSharedEdge position hreverse)).IsCycle := by
  apply data.crossSidePortClosure_isCycle
  exact pair.zeroToThreePathAtReversedSharedEdge_isPath position hreverse

/-- Closing the complementary `1–2` path gives the other mixed-channel
cycle. -/
theorem RetainedIntersectionExactFaceCutPair.oneToTwoCrossSidePortClosure_isCycle
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    (data.crossSidePortClosure 1 0
      (pair.oneToTwoPathAtReversedSharedEdge position hreverse)).IsCycle := by
  apply data.crossSidePortClosure_isCycle
  exact pair.oneToTwoPathAtReversedSharedEdge_isPath position hreverse

/-- The geometric output of resolving a localized reversed profile dart:
two mixed-port paths, their cycle closures, and a strict total-length
descent, while retaining the localized edge that triggered the switch. -/
structure LocalizedStrictlyShorterMixedPortCycles
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  selectedEdge : (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).edgeSet
  selectedEdge_ne_oldCross : selectedEdge ≠ oldCross
  selectedAmbientEdge_mem_face :
    retainedEdgeToAmbientEdge data selectedEdge ∈
      orbitFaceBoundary graphData.toRotationSystem face
  zeroToThreePath :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 0) (data.retainedPort 3)
  oneToTwoPath :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 1) (data.retainedPort 2)
  zeroToThree_isPath : zeroToThreePath.IsPath
  oneToTwo_isPath : oneToTwoPath.IsPath
  zeroToThree_closure_isCycle :
    (data.crossSidePortClosure 0 1 zeroToThreePath).IsCycle
  oneToTwo_closure_isCycle :
    (data.crossSidePortClosure 1 0 oneToTwoPath).IsCycle
  selectedEdge_not_mem_zeroToThreePath :
    selectedEdge.1 ∉ zeroToThreePath.edges
  selectedEdge_not_mem_oneToTwoPath :
    selectedEdge.1 ∉ oneToTwoPath.edges
  total_length_lt :
    zeroToThreePath.length + oneToTwoPath.length <
      pair.prefixTrail.length + pair.suffixTrail.length

/-- Resolve a reversed shared dart into its canonical strictly shorter
mixed-port cycle pair. -/
def LocalizedReversedSharedEdgeDart.toLocalizedStrictlyShorterMixedPortCycles
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedReversedSharedEdgeDart pair oldCross face) :
    LocalizedStrictlyShorterMixedPortCycles pair oldCross face where
  selectedEdge := pair.sharedEdgeAt witness.position
  selectedEdge_ne_oldCross := witness.edge_ne_oldCross
  selectedAmbientEdge_mem_face := witness.ambient_edge_mem_face
  zeroToThreePath := pair.zeroToThreePathAtReversedSharedEdge
    witness.position witness.retained_reversed
  oneToTwoPath := pair.oneToTwoPathAtReversedSharedEdge
    witness.position witness.retained_reversed
  zeroToThree_isPath :=
    pair.zeroToThreePathAtReversedSharedEdge_isPath witness.position
      witness.retained_reversed
  oneToTwo_isPath :=
    pair.oneToTwoPathAtReversedSharedEdge_isPath witness.position
      witness.retained_reversed
  zeroToThree_closure_isCycle :=
    pair.zeroToThreeCrossSidePortClosure_isCycle witness.position
      witness.retained_reversed
  oneToTwo_closure_isCycle :=
    pair.oneToTwoCrossSidePortClosure_isCycle witness.position
      witness.retained_reversed
  selectedEdge_not_mem_zeroToThreePath :=
    pair.sharedEdgeAt_not_mem_zeroToThreePath_edges witness.position
      witness.retained_reversed
  selectedEdge_not_mem_oneToTwoPath :=
    pair.sharedEdgeAt_not_mem_oneToTwoPath_edges witness.position
      witness.retained_reversed
  total_length_lt := pair.reversedSharedEdgePaths_length_add_lt
    witness.position witness.retained_reversed

/-- A localized reversed-dart obstruction canonically supplies two
strictly shorter mixed-channel paths and their ambient cycle closures. -/
theorem LocalizedReversedSharedEdgeDart.exists_strictlyShorterMixedPortCycles
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedReversedSharedEdgeDart pair oldCross face) :
    (pair.zeroToThreePathAtReversedSharedEdge witness.position
        witness.retained_reversed).IsPath ∧
      (pair.oneToTwoPathAtReversedSharedEdge witness.position
        witness.retained_reversed).IsPath ∧
      (data.crossSidePortClosure 0 1
        (pair.zeroToThreePathAtReversedSharedEdge witness.position
          witness.retained_reversed)).IsCycle ∧
      (data.crossSidePortClosure 1 0
        (pair.oneToTwoPathAtReversedSharedEdge witness.position
          witness.retained_reversed)).IsCycle ∧
      (pair.zeroToThreePathAtReversedSharedEdge witness.position
            witness.retained_reversed).length +
          (pair.oneToTwoPathAtReversedSharedEdge witness.position
            witness.retained_reversed).length <
        pair.prefixTrail.length + pair.suffixTrail.length := by
  exact ⟨pair.zeroToThreePathAtReversedSharedEdge_isPath
      witness.position witness.retained_reversed,
    pair.oneToTwoPathAtReversedSharedEdge_isPath
      witness.position witness.retained_reversed,
    pair.zeroToThreeCrossSidePortClosure_isCycle
      witness.position witness.retained_reversed,
    pair.oneToTwoCrossSidePortClosure_isCycle
      witness.position witness.retained_reversed,
    pair.reversedSharedEdgePaths_length_add_lt
      witness.position witness.retained_reversed⟩

/-- After resolving the sign branch, every localized signed profile has
the sharper normal form: identity, an order-inverting interval pair, or a
strictly shorter pair of mixed-port cycles. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy_eq_refl_or_exists_localizedPathIntervalInversion_or_strictlyShorterMixedPortCycles
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hprefixPath : pair.prefixTrail.IsPath)
    (hsuffixPath : pair.suffixTrail.IsPath)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem)
    (hlocalized : ∀ edge ∈ pair.sharedEdges,
      edge ≠ oldCross ∧
        retainedEdgeToAmbientEdge data edge ∈
          orbitFaceBoundary graphData.toRotationSystem face) :
    pair.sharedEdgeSignedMonodromy =
        Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) ∨
      Nonempty (LocalizedSharedEdgePathIntervalInversion pair oldCross face) ∨
      Nonempty (LocalizedStrictlyShorterMixedPortCycles pair oldCross face) := by
  rcases pair.sharedEdgeSignedMonodromy_eq_refl_or_exists_localizedPathIntervalInversion_or_reversedSharedEdgeDart
      hprefixPath hsuffixPath oldCross face hlocalized with
    hidentity | hinversion | hreversed
  · exact Or.inl hidentity
  · exact Or.inr (Or.inl hinversion)
  · rcases hreversed with ⟨witness⟩
    exact Or.inr (Or.inr
      ⟨witness.toLocalizedStrictlyShorterMixedPortCycles⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
