import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunCrossedIntersection

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} {Graph : SimpleGraph Vertex}

/-- The edge-set member traversed first by a nonempty walk. -/
def firstEdgeSet {start finish : Vertex}
    (walk : Graph.Walk start finish) (hnil : ¬ walk.Nil) : Graph.edgeSet :=
  ⟨(walk.firstDart hnil).edge, (walk.firstDart hnil).edge_mem⟩

/-- The edge-set member traversed last by a nonempty walk. -/
def lastEdgeSet {start finish : Vertex}
    (walk : Graph.Walk start finish) (hnil : ¬ walk.Nil) : Graph.edgeSet :=
  ⟨(walk.lastDart hnil).edge, (walk.lastDart hnil).edge_mem⟩

@[simp] theorem firstEdgeSet_val {start finish : Vertex}
    (walk : Graph.Walk start finish) (hnil : ¬ walk.Nil) :
    (walk.firstEdgeSet hnil).1 = (walk.firstDart hnil).edge := rfl

@[simp] theorem lastEdgeSet_val {start finish : Vertex}
    (walk : Graph.Walk start finish) (hnil : ¬ walk.Nil) :
    (walk.lastEdgeSet hnil).1 = (walk.lastDart hnil).edge := rfl

theorem firstEdgeSet_val_mem_edges {start finish : Vertex}
    (walk : Graph.Walk start finish) (hnil : ¬ walk.Nil) :
    (walk.firstEdgeSet hnil).1 ∈ walk.edges := by
  simpa only [firstEdgeSet_val, walk.edge_firstDart] using
    walk.mk_start_snd_mem_edges hnil

theorem lastEdgeSet_val_mem_edges {start finish : Vertex}
    (walk : Graph.Walk start finish) (hnil : ¬ walk.Nil) :
    (walk.lastEdgeSet hnil).1 ∈ walk.edges := by
  simpa only [lastEdgeSet_val, walk.edge_lastDart] using
    walk.mk_penultimate_end_mem_edges hnil

theorem firstEdgeSet_mem_incidentEdgeFinset {start finish : Vertex}
    [DecidableEq Vertex] [Fintype Graph.edgeSet]
    (walk : Graph.Walk start finish) (hnil : ¬ walk.Nil) :
    walk.firstEdgeSet hnil ∈
      Mettapedia.GraphTheory.FourColor.incidentEdgeFinset Graph start := by
  simp [Mettapedia.GraphTheory.FourColor.incidentEdgeFinset,
    firstEdgeSet, SimpleGraph.Walk.firstDart]

theorem lastEdgeSet_mem_incidentEdgeFinset {start finish : Vertex}
    [DecidableEq Vertex] [Fintype Graph.edgeSet]
    (walk : Graph.Walk start finish) (hnil : ¬ walk.Nil) :
    walk.lastEdgeSet hnil ∈
      Mettapedia.GraphTheory.FourColor.incidentEdgeFinset Graph finish := by
  simp [Mettapedia.GraphTheory.FourColor.incidentEdgeFinset,
    lastEdgeSet, SimpleGraph.Walk.lastDart]

/-- Edge-set members drawn from disjoint edge lists are distinct. -/
theorem edgeSet_ne_of_val_mem_of_val_mem_of_disjoint
    {leftEdges rightEdges : List (Sym2 Vertex)}
    {left right : Graph.edgeSet}
    (hdisjoint : leftEdges.Disjoint rightEdges)
    (hleft : left.1 ∈ leftEdges) (hright : right.1 ∈ rightEdges) :
    left ≠ right := by
  intro heq
  subst right
  exact (List.disjoint_left.mp hdisjoint) hleft hright

end SimpleGraph.Walk

namespace SimpleGraph.Dart

universe u

variable {Vertex : Type u} [DecidableEq Vertex]
  {Graph : SimpleGraph Vertex}

/-- The edge underlying a dart is incident to every vertex at which that
dart is based. -/
theorem edgeSet_mem_incidentEdgeFinset_of_fst_eq
    [Fintype Graph.edgeSet] (dart : Graph.Dart) {vertex : Vertex}
    (hfst : dart.fst = vertex) :
    (⟨dart.edge, dart.edge_mem⟩ : Graph.edgeSet) ∈
      Mettapedia.GraphTheory.FourColor.incidentEdgeFinset Graph vertex := by
  subst vertex
  simp only [Mettapedia.GraphTheory.FourColor.incidentEdgeFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  change dart.fst ∈ s(dart.fst, dart.snd)
  exact Sym2.mem_iff.mpr (Or.inl rfl)

end SimpleGraph.Dart

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

/-- The edge-set member underlying a selected common-run dart. -/
@[simp] theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart_edgeSet
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (⟨(pair.prefixSharedEdgeDart position).edge,
        (pair.prefixSharedEdgeDart position).edge_mem⟩ :
      (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet) = pair.sharedEdgeAt position := by
  apply Subtype.ext
  exact pair.prefixSharedEdgeDart_edge position

/-- A selected shared edge occurs on the prefix successor. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_val_mem_prefixTrail_edges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (pair.sharedEdgeAt position).1 ∈ pair.prefixTrail.edges :=
  ((pair.mem_sharedEdges_iff (pair.sharedEdgeAt position)).1
    (pair.sharedEdgeAt_mem_sharedEdges position)).1

/-- A selected shared edge occurs on the suffix successor. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_val_mem_suffixTrail_edges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (pair.sharedEdgeAt position).1 ∈ pair.suffixTrail.edges :=
  ((pair.mem_sharedEdges_iff (pair.sharedEdgeAt position)).1
    (pair.sharedEdgeAt_mem_sharedEdges position)).2

/-- The canonically oriented retained darts based at a common-run merge. -/
def LocalizedCommonRunMergeArmState.outgoingDarts
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) :
    List (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart :=
  match state with
  | .internal hprefix hsuffix =>
      [(splice.trunk.prefixIncomingArm.lastDart hprefix).symm,
        (splice.trunk.suffixIncomingArm.lastDart hsuffix).symm,
        pair.prefixSharedEdgeDart profile.firstRank]
  | .prefixPort _ _ hsuffix =>
      [(splice.trunk.suffixIncomingArm.lastDart hsuffix).symm,
        pair.prefixSharedEdgeDart profile.firstRank]
  | .suffixPort _ _ hprefix =>
      [(splice.trunk.prefixIncomingArm.lastDart hprefix).symm,
        pair.prefixSharedEdgeDart profile.firstRank]

/-- The canonically oriented retained darts based at a common-run split. -/
def LocalizedCommonRunSplitArmState.outgoingDarts
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) :
    List (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart :=
  match state with
  | .internal hprefix hsuffix =>
      [(pair.prefixSharedEdgeDart profile.lastRank).symm,
        splice.trunk.prefixOutgoingArm.firstDart hprefix,
        splice.trunk.suffixOutgoingArm.firstDart hsuffix]
  | .prefixPort _ _ hsuffix =>
      [(pair.prefixSharedEdgeDart profile.lastRank).symm,
        splice.trunk.suffixOutgoingArm.firstDart hsuffix]
  | .suffixPort _ _ hprefix =>
      [(pair.prefixSharedEdgeDart profile.lastRank).symm,
        splice.trunk.prefixOutgoingArm.firstDart hprefix]

/-- The retained edge word named by a merge state. -/
def LocalizedCommonRunMergeArmState.edgeList
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) :
    List (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
  match state with
  | .internal hprefix hsuffix =>
      [splice.trunk.prefixIncomingArm.lastEdgeSet hprefix,
        splice.trunk.suffixIncomingArm.lastEdgeSet hsuffix,
        pair.sharedEdgeAt profile.firstRank]
  | .prefixPort _ _ hsuffix =>
      [splice.trunk.suffixIncomingArm.lastEdgeSet hsuffix,
        pair.sharedEdgeAt profile.firstRank]
  | .suffixPort _ _ hprefix =>
      [splice.trunk.prefixIncomingArm.lastEdgeSet hprefix,
        pair.sharedEdgeAt profile.firstRank]

/-- The retained edge word named by a split state. -/
def LocalizedCommonRunSplitArmState.edgeList
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) :
    List (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
  match state with
  | .internal hprefix hsuffix =>
      [pair.sharedEdgeAt profile.lastRank,
        splice.trunk.prefixOutgoingArm.firstEdgeSet hprefix,
        splice.trunk.suffixOutgoingArm.firstEdgeSet hsuffix]
  | .prefixPort _ _ hsuffix =>
      [pair.sharedEdgeAt profile.lastRank,
        splice.trunk.suffixOutgoingArm.firstEdgeSet hsuffix]
  | .suffixPort _ _ hprefix =>
      [pair.sharedEdgeAt profile.lastRank,
        splice.trunk.prefixOutgoingArm.firstEdgeSet hprefix]

/-- Forgetting orientation gives the finite retained edge set named by a
merge state. -/
def LocalizedCommonRunMergeArmState.incidentEdges
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) :
    Finset (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
  state.edgeList.toFinset

/-- Forgetting orientation gives the finite retained edge set named by a
split state. -/
def LocalizedCommonRunSplitArmState.incidentEdges
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) :
    Finset (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
  state.edgeList.toFinset

/-- Every dart named by a merge state is oriented out of the merge. -/
theorem LocalizedCommonRunMergeArmState.outgoingDarts_fst_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice)
    {dart : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart}
    (hdart : dart ∈ state.outgoingDarts) :
    dart.fst = (pair.prefixSharedEdgeDart profile.firstRank).fst := by
  cases state with
  | internal hprefix hsuffix =>
      simp only [LocalizedCommonRunMergeArmState.outgoingDarts,
        List.mem_cons, List.not_mem_nil, or_false] at hdart
      rcases hdart with rfl | rfl | rfl <;> simp
  | prefixPort _ _ hsuffix =>
      simp only [LocalizedCommonRunMergeArmState.outgoingDarts,
        List.mem_cons, List.not_mem_nil, or_false] at hdart
      rcases hdart with rfl | rfl <;> simp
  | suffixPort _ _ hprefix =>
      simp only [LocalizedCommonRunMergeArmState.outgoingDarts,
        List.mem_cons, List.not_mem_nil, or_false] at hdart
      rcases hdart with rfl | rfl <;> simp

/-- Every dart named by a split state is oriented out of the split. -/
theorem LocalizedCommonRunSplitArmState.outgoingDarts_fst_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice)
    {dart : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart}
    (hdart : dart ∈ state.outgoingDarts) :
    dart.fst = (pair.prefixSharedEdgeDart profile.lastRank).snd := by
  cases state with
  | internal hprefix hsuffix =>
      simp only [LocalizedCommonRunSplitArmState.outgoingDarts,
        List.mem_cons, List.not_mem_nil, or_false] at hdart
      rcases hdart with rfl | rfl | rfl <;> simp
  | prefixPort _ _ hsuffix =>
      simp only [LocalizedCommonRunSplitArmState.outgoingDarts,
        List.mem_cons, List.not_mem_nil, or_false] at hdart
      rcases hdart with rfl | rfl <;> simp
  | suffixPort _ _ hprefix =>
      simp only [LocalizedCommonRunSplitArmState.outgoingDarts,
        List.mem_cons, List.not_mem_nil, or_false] at hdart
      rcases hdart with rfl | rfl <;> simp

/-- The edge word named by a clean merge state has no repetitions. -/
theorem LocalizedAlignedCommonRunSplice.merge_edgeList_nodup
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (state : LocalizedCommonRunMergeArmState splice) :
    state.edgeList.Nodup := by
  cases state with
  | internal hprefix hsuffix =>
      have hprefixMem :=
        splice.trunk.prefixIncomingArm.lastEdgeSet_val_mem_edges hprefix
      have hsuffixMem :=
        splice.trunk.suffixIncomingArm.lastEdgeSet_val_mem_edges hsuffix
      have hcommonPrefix :=
        pair.sharedEdgeAt_val_mem_prefixTrail_edges profile.firstRank
      have hcommonSuffix :=
        pair.sharedEdgeAt_val_mem_suffixTrail_edges profile.firstRank
      have hprefixSuffix :=
        SimpleGraph.Walk.edgeSet_ne_of_val_mem_of_val_mem_of_disjoint
          splice.crossArms_pairwise_disjoint.1 hprefixMem hsuffixMem
      have hprefixCommon :=
        SimpleGraph.Walk.edgeSet_ne_of_val_mem_of_val_mem_of_disjoint
          splice.trunk.prefixIncomingArm_disjoint_suffixTrail
          hprefixMem hcommonSuffix
      have hsuffixCommon :=
        SimpleGraph.Walk.edgeSet_ne_of_val_mem_of_val_mem_of_disjoint
          splice.trunk.suffixIncomingArm_disjoint_prefixTrail
          hsuffixMem hcommonPrefix
      simpa [LocalizedCommonRunMergeArmState.edgeList] using
        And.intro (And.intro hprefixSuffix hprefixCommon) hsuffixCommon
  | prefixPort _ _ hsuffix =>
      have hsuffixMem :=
        splice.trunk.suffixIncomingArm.lastEdgeSet_val_mem_edges hsuffix
      have hcommonPrefix :=
        pair.sharedEdgeAt_val_mem_prefixTrail_edges profile.firstRank
      have hsuffixCommon :=
        SimpleGraph.Walk.edgeSet_ne_of_val_mem_of_val_mem_of_disjoint
          splice.trunk.suffixIncomingArm_disjoint_prefixTrail
          hsuffixMem hcommonPrefix
      simpa [LocalizedCommonRunMergeArmState.edgeList] using hsuffixCommon
  | suffixPort _ _ hprefix =>
      have hprefixMem :=
        splice.trunk.prefixIncomingArm.lastEdgeSet_val_mem_edges hprefix
      have hcommonSuffix :=
        pair.sharedEdgeAt_val_mem_suffixTrail_edges profile.firstRank
      have hprefixCommon :=
        SimpleGraph.Walk.edgeSet_ne_of_val_mem_of_val_mem_of_disjoint
          splice.trunk.prefixIncomingArm_disjoint_suffixTrail
          hprefixMem hcommonSuffix
      simpa [LocalizedCommonRunMergeArmState.edgeList] using hprefixCommon

/-- The edge word named by a clean split state has no repetitions. -/
theorem LocalizedAlignedCommonRunSplice.split_edgeList_nodup
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (state : LocalizedCommonRunSplitArmState splice) :
    state.edgeList.Nodup := by
  cases state with
  | internal hprefix hsuffix =>
      have hprefixMem :=
        splice.trunk.prefixOutgoingArm.firstEdgeSet_val_mem_edges hprefix
      have hsuffixMem :=
        splice.trunk.suffixOutgoingArm.firstEdgeSet_val_mem_edges hsuffix
      have hcommonPrefix :=
        pair.sharedEdgeAt_val_mem_prefixTrail_edges profile.lastRank
      have hcommonSuffix :=
        pair.sharedEdgeAt_val_mem_suffixTrail_edges profile.lastRank
      have hprefixSuffix :=
        SimpleGraph.Walk.edgeSet_ne_of_val_mem_of_val_mem_of_disjoint
          splice.crossArms_pairwise_disjoint.2.2.2 hprefixMem hsuffixMem
      have hprefixCommon :=
        SimpleGraph.Walk.edgeSet_ne_of_val_mem_of_val_mem_of_disjoint
          splice.trunk.prefixOutgoingArm_disjoint_suffixTrail
          hprefixMem hcommonSuffix
      have hsuffixCommon :=
        SimpleGraph.Walk.edgeSet_ne_of_val_mem_of_val_mem_of_disjoint
          splice.trunk.suffixOutgoingArm_disjoint_prefixTrail
          hsuffixMem hcommonPrefix
      simpa [LocalizedCommonRunSplitArmState.edgeList] using
        And.intro
          (And.intro hprefixCommon.symm hsuffixCommon.symm)
          hprefixSuffix
  | prefixPort _ _ hsuffix =>
      have hsuffixMem :=
        splice.trunk.suffixOutgoingArm.firstEdgeSet_val_mem_edges hsuffix
      have hcommonPrefix :=
        pair.sharedEdgeAt_val_mem_prefixTrail_edges profile.lastRank
      have hsuffixCommon :=
        SimpleGraph.Walk.edgeSet_ne_of_val_mem_of_val_mem_of_disjoint
          splice.trunk.suffixOutgoingArm_disjoint_prefixTrail
          hsuffixMem hcommonPrefix
      simpa [LocalizedCommonRunSplitArmState.edgeList] using
        hsuffixCommon.symm
  | suffixPort _ _ hprefix =>
      have hprefixMem :=
        splice.trunk.prefixOutgoingArm.firstEdgeSet_val_mem_edges hprefix
      have hcommonSuffix :=
        pair.sharedEdgeAt_val_mem_suffixTrail_edges profile.lastRank
      have hprefixCommon :=
        SimpleGraph.Walk.edgeSet_ne_of_val_mem_of_val_mem_of_disjoint
          splice.trunk.prefixOutgoingArm_disjoint_suffixTrail
          hprefixMem hcommonSuffix
      simpa [LocalizedCommonRunSplitArmState.edgeList] using
        hprefixCommon.symm

/-- Forgetting the orientations of the canonical merge darts gives exactly
the merge edge word. -/
theorem LocalizedCommonRunMergeArmState.outgoingDarts_edges_eq_edgeList
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) :
    state.outgoingDarts.map (fun dart =>
      (⟨dart.edge, dart.edge_mem⟩ :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet)) = state.edgeList := by
  cases state <;>
    simp only [LocalizedCommonRunMergeArmState.outgoingDarts,
      LocalizedCommonRunMergeArmState.edgeList,
      SimpleGraph.Walk.lastEdgeSet, List.map_cons, List.map_nil,
      SimpleGraph.Dart.edge_symm] <;>
    rw [pair.prefixSharedEdgeDart_edgeSet]

/-- Forgetting the orientations of the canonical split darts gives exactly
the split edge word. -/
theorem LocalizedCommonRunSplitArmState.outgoingDarts_edges_eq_edgeList
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) :
    state.outgoingDarts.map (fun dart =>
      (⟨dart.edge, dart.edge_mem⟩ :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet)) = state.edgeList := by
  cases state <;>
    simp only [LocalizedCommonRunSplitArmState.outgoingDarts,
      LocalizedCommonRunSplitArmState.edgeList,
      SimpleGraph.Walk.firstEdgeSet, List.map_cons, List.map_nil,
      SimpleGraph.Dart.edge_symm] <;>
    rw [pair.prefixSharedEdgeDart_edgeSet]

/-- The canonical merge darts are pairwise distinct. -/
theorem LocalizedAlignedCommonRunSplice.merge_outgoingDarts_nodup
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (state : LocalizedCommonRunMergeArmState splice) :
    state.outgoingDarts.Nodup := by
  apply List.Nodup.of_map (fun dart =>
    (⟨dart.edge, dart.edge_mem⟩ :
      (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet))
  rw [state.outgoingDarts_edges_eq_edgeList]
  exact splice.merge_edgeList_nodup state

/-- The canonical split darts are pairwise distinct. -/
theorem LocalizedAlignedCommonRunSplice.split_outgoingDarts_nodup
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (state : LocalizedCommonRunSplitArmState splice) :
    state.outgoingDarts.Nodup := by
  apply List.Nodup.of_map (fun dart =>
    (⟨dart.edge, dart.edge_mem⟩ :
      (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet))
  rw [state.outgoingDarts_edges_eq_edgeList]
  exact splice.split_edgeList_nodup state

/-- The canonical merge dart word has the degree prescribed by its state. -/
@[simp] theorem LocalizedCommonRunMergeArmState.outgoingDarts_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) :
    state.outgoingDarts.length = state.retainedDegree := by
  cases state <;> rfl

/-- The canonical split dart word has the degree prescribed by its state. -/
@[simp] theorem LocalizedCommonRunSplitArmState.outgoingDarts_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) :
    state.outgoingDarts.length = state.retainedDegree := by
  cases state <;> rfl

/-- The canonical merge word has the degree prescribed by its state. -/
@[simp] theorem LocalizedCommonRunMergeArmState.edgeList_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) :
    state.edgeList.length = state.retainedDegree := by
  cases state <;> rfl

/-- The canonical split word has the degree prescribed by its state. -/
@[simp] theorem LocalizedCommonRunSplitArmState.edgeList_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) :
    state.edgeList.length = state.retainedDegree := by
  cases state <;> rfl

/-- The canonical merge edge set has the degree prescribed by its state. -/
@[simp] theorem LocalizedAlignedCommonRunSplice.merge_incidentEdges_card
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (state : LocalizedCommonRunMergeArmState splice) :
    state.incidentEdges.card = state.retainedDegree := by
  rw [LocalizedCommonRunMergeArmState.incidentEdges,
    List.toFinset_card_of_nodup (splice.merge_edgeList_nodup state),
    state.edgeList_length]

/-- The canonical split edge set has the degree prescribed by its state. -/
@[simp] theorem LocalizedAlignedCommonRunSplice.split_incidentEdges_card
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (state : LocalizedCommonRunSplitArmState splice) :
    state.incidentEdges.card = state.retainedDegree := by
  rw [LocalizedCommonRunSplitArmState.incidentEdges,
    List.toFinset_card_of_nodup (splice.split_edgeList_nodup state),
    state.edgeList_length]

/-- Every canonical merge edge is incident to the merge. -/
theorem LocalizedCommonRunMergeArmState.incidentEdges_subset_incidentEdgeFinset
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) :
    state.incidentEdges ⊆
      incidentEdgeFinset
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (pair.prefixSharedEdgeDart profile.firstRank).fst := by
  intro edge hedge
  rw [LocalizedCommonRunMergeArmState.incidentEdges,
    List.mem_toFinset, ← state.outgoingDarts_edges_eq_edgeList] at hedge
  rcases List.mem_map.mp hedge with ⟨dart, hdart, rfl⟩
  exact dart.edgeSet_mem_incidentEdgeFinset_of_fst_eq
    (state.outgoingDarts_fst_eq hdart)

/-- Every canonical split edge is incident to the split. -/
theorem LocalizedCommonRunSplitArmState.incidentEdges_subset_incidentEdgeFinset
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) :
    state.incidentEdges ⊆
      incidentEdgeFinset
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (pair.prefixSharedEdgeDart profile.lastRank).snd := by
  intro edge hedge
  rw [LocalizedCommonRunSplitArmState.incidentEdges,
    List.mem_toFinset, ← state.outgoingDarts_edges_eq_edgeList] at hedge
  rcases List.mem_map.mp hedge with ⟨dart, hdart, rfl⟩
  exact dart.edgeSet_mem_incidentEdgeFinset_of_fst_eq
    (state.outgoingDarts_fst_eq hdart)

/-- In a cubic ambient graph, the canonical merge edges exhaust all retained
edges incident to the merge. -/
theorem LocalizedCommonRunCleanFourArms.merge_incidentEdgeFinset_eq
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
    incidentEdgeFinset
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (pair.prefixSharedEdgeDart profile.firstRank).fst =
      state.incidentEdges := by
  symm
  apply Finset.eq_of_subset_of_card_le
    state.incidentEdges_subset_incidentEdgeFinset
  rw [clean.merge_incidentEdgeFinset_card hcubic state,
    splice.merge_incidentEdges_card state]

/-- In a cubic ambient graph, the canonical split edges exhaust all retained
edges incident to the split. -/
theorem LocalizedCommonRunCleanFourArms.split_incidentEdgeFinset_eq
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
    incidentEdgeFinset
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (pair.prefixSharedEdgeDart profile.lastRank).snd =
      state.incidentEdges := by
  symm
  apply Finset.eq_of_subset_of_card_le
    state.incidentEdges_subset_incidentEdgeFinset
  rw [clean.split_incidentEdgeFinset_card hcubic state,
    splice.split_incidentEdges_card state]

/-- In a cubic ambient graph, the canonical merge darts exhaust the entire
outgoing retained-dart fiber at the merge. -/
theorem LocalizedCommonRunCleanFourArms.merge_outgoingDartFinset_eq
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
    (Finset.univ.filter fun dart :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Dart =>
      dart.fst = (pair.prefixSharedEdgeDart profile.firstRank).fst) =
        state.outgoingDarts.toFinset := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro dart hdart
    rw [List.mem_toFinset] at hdart
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact state.outgoingDarts_fst_eq hdart
  · have hfiberCard :
        (Finset.univ.filter fun dart :
            (DeletedAdjacentPairGraph G data.firstVertex
              data.secondVertex).Dart =>
          dart.fst =
            (pair.prefixSharedEdgeDart profile.firstRank).fst).card =
          state.retainedDegree := by
      letI : Fintype
          ((DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).neighborSet
              (pair.prefixSharedEdgeDart profile.firstRank).fst) :=
        Subtype.fintype _
      calc
        _ = (DeletedAdjacentPairGraph G data.firstVertex
              data.secondVertex).degree
              (pair.prefixSharedEdgeDart profile.firstRank).fst :=
          (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).dart_fst_fiber_card_eq_degree _
        _ = (incidentEdgeFinset
              (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
              (pair.prefixSharedEdgeDart profile.firstRank).fst).card :=
          (GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree _).symm
        _ = state.retainedDegree :=
          clean.merge_incidentEdgeFinset_card hcubic state
    rw [hfiberCard,
      List.toFinset_card_of_nodup
        (splice.merge_outgoingDarts_nodup state),
      state.outgoingDarts_length]

/-- In a cubic ambient graph, the canonical split darts exhaust the entire
outgoing retained-dart fiber at the split. -/
theorem LocalizedCommonRunCleanFourArms.split_outgoingDartFinset_eq
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
    (Finset.univ.filter fun dart :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Dart =>
      dart.fst = (pair.prefixSharedEdgeDart profile.lastRank).snd) =
        state.outgoingDarts.toFinset := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro dart hdart
    rw [List.mem_toFinset] at hdart
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact state.outgoingDarts_fst_eq hdart
  · have hfiberCard :
        (Finset.univ.filter fun dart :
            (DeletedAdjacentPairGraph G data.firstVertex
              data.secondVertex).Dart =>
          dart.fst =
            (pair.prefixSharedEdgeDart profile.lastRank).snd).card =
          state.retainedDegree := by
      letI : Fintype
          ((DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).neighborSet
              (pair.prefixSharedEdgeDart profile.lastRank).snd) :=
        Subtype.fintype _
      calc
        _ = (DeletedAdjacentPairGraph G data.firstVertex
              data.secondVertex).degree
              (pair.prefixSharedEdgeDart profile.lastRank).snd :=
          (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).dart_fst_fiber_card_eq_degree _
        _ = (incidentEdgeFinset
              (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
              (pair.prefixSharedEdgeDart profile.lastRank).snd).card :=
          (GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree _).symm
        _ = state.retainedDegree :=
          clean.split_incidentEdgeFinset_card hcubic state
    rw [hfiberCard,
      List.toFinset_card_of_nodup
        (splice.split_outgoingDarts_nodup state),
      state.outgoingDarts_length]

end GoertzelV24AdjacentPairInsertion.AdjacentPairData
end
end Mettapedia.GraphTheory.FourColor
