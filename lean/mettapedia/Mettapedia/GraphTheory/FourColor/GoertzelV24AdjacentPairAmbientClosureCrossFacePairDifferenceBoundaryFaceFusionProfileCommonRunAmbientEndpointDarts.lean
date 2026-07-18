import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunEndpointDarts

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

/-- The restored boundary port, if the merge coincides with one of its
incoming ports. -/
def LocalizedCommonRunMergeArmState.collapsedPort
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunMergeArmState splice → Option (Fin 4)
  | .internal _ _ => none
  | .prefixPort _ _ _ => some 0
  | .suffixPort _ _ _ => some 1

/-- The restored boundary port, if the split coincides with one of its
outgoing ports. -/
def LocalizedCommonRunSplitArmState.collapsedPort
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunSplitArmState splice → Option (Fin 4)
  | .internal _ _ => none
  | .prefixPort _ _ _ => some 2
  | .suffixPort _ _ _ => some 3

/-- Lift every retained merge dart to the ambient graph and, in a port
state, restore the unique deleted boundary direction. -/
def LocalizedCommonRunMergeArmState.ambientOutgoingDarts
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) : List G.Dart :=
  state.outgoingDarts.map (retainedDartToAmbientDart data) ++
    state.collapsedPort.toList.map (boundaryPortDart data)

/-- Lift every retained split dart to the ambient graph and, in a port
state, restore the unique deleted boundary direction. -/
def LocalizedCommonRunSplitArmState.ambientOutgoingDarts
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) : List G.Dart :=
  state.outgoingDarts.map (retainedDartToAmbientDart data) ++
    state.collapsedPort.toList.map (boundaryPortDart data)

/-- The restored ambient merge word always has cubic length. -/
@[simp] theorem LocalizedCommonRunMergeArmState.ambientOutgoingDarts_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) :
    state.ambientOutgoingDarts.length = 3 := by
  cases state <;> rfl

/-- The restored ambient split word always has cubic length. -/
@[simp] theorem LocalizedCommonRunSplitArmState.ambientOutgoingDarts_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) :
    state.ambientOutgoingDarts.length = 3 := by
  cases state <;> rfl

/-- Every restored ambient merge dart is based at the ambient merge. -/
theorem LocalizedCommonRunMergeArmState.ambientOutgoingDarts_fst_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice)
    {dart : G.Dart} (hdart : dart ∈ state.ambientOutgoingDarts) :
    dart.fst =
      (pair.prefixSharedEdgeDart profile.firstRank).fst.1 := by
  rw [LocalizedCommonRunMergeArmState.ambientOutgoingDarts,
    List.mem_append] at hdart
  rcases hdart with hretained | hboundary
  · obtain ⟨retained, hretainedMem, hdartEq⟩ :=
      List.mem_map.mp hretained
    subst dart
    rw [retainedDartToAmbientDart_fst,
      state.outgoingDarts_fst_eq hretainedMem]
  · cases state with
    | internal _ _ =>
        simp [LocalizedCommonRunMergeArmState.collapsedPort] at hboundary
    | prefixPort _ heq _ =>
        have hdartEq : dart = boundaryPortDart data 0 := by
          simpa [LocalizedCommonRunMergeArmState.collapsedPort] using hboundary
        subst dart
        simpa [retainedPort] using (congrArg Subtype.val heq).symm
    | suffixPort _ heq _ =>
        have hdartEq : dart = boundaryPortDart data 1 := by
          simpa [LocalizedCommonRunMergeArmState.collapsedPort] using hboundary
        subst dart
        simpa [retainedPort] using (congrArg Subtype.val heq).symm

/-- Every restored ambient split dart is based at the ambient split. -/
theorem LocalizedCommonRunSplitArmState.ambientOutgoingDarts_fst_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice)
    {dart : G.Dart} (hdart : dart ∈ state.ambientOutgoingDarts) :
    dart.fst =
      (pair.prefixSharedEdgeDart profile.lastRank).snd.1 := by
  rw [LocalizedCommonRunSplitArmState.ambientOutgoingDarts,
    List.mem_append] at hdart
  rcases hdart with hretained | hboundary
  · obtain ⟨retained, hretainedMem, hdartEq⟩ :=
      List.mem_map.mp hretained
    subst dart
    rw [retainedDartToAmbientDart_fst,
      state.outgoingDarts_fst_eq hretainedMem]
  · cases state with
    | internal _ _ =>
        simp [LocalizedCommonRunSplitArmState.collapsedPort] at hboundary
    | prefixPort _ heq _ =>
        have hdartEq : dart = boundaryPortDart data 2 := by
          simpa [LocalizedCommonRunSplitArmState.collapsedPort] using hboundary
        subst dart
        simpa [retainedPort] using (congrArg Subtype.val heq).symm
    | suffixPort _ heq _ =>
        have hdartEq : dart = boundaryPortDart data 3 := by
          simpa [LocalizedCommonRunSplitArmState.collapsedPort] using hboundary
        subst dart
        simpa [retainedPort] using (congrArg Subtype.val heq).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A restored boundary-port dart cannot be the ambient lift of any retained
dart. -/
theorem boundaryPortDart_not_mem_map_retainedDartToAmbientDart
    (data : AdjacentPairData G)
    (darts : List (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart) (port : Fin 4) :
    boundaryPortDart data port ∉
      darts.map (retainedDartToAmbientDart data) := by
  intro hmem
  obtain ⟨dart, _hdart, heq⟩ := List.mem_map.mp hmem
  apply retainedEdgeToAmbientEdge_ne_boundaryEdge data
    (⟨dart.edge, dart.edge_mem⟩ :
      (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet) port
  apply Subtype.ext
  simpa using congrArg SimpleGraph.Dart.edge heq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Lifting a duplicate-free retained dart word and appending one restored
boundary direction preserves duplicate-freedom. -/
theorem map_retainedDartToAmbientDart_append_boundaryPortDart_nodup
    (data : AdjacentPairData G)
    {darts : List (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart} (hnodup : darts.Nodup) (port : Fin 4) :
    (darts.map (retainedDartToAmbientDart data) ++
      [boundaryPortDart data port]).Nodup := by
  apply (hnodup.map (retainedDartToAmbientDart_injective data)).append
    (by simp)
  rw [List.disjoint_left]
  intro dart hdart hboundary
  have heq : dart = boundaryPortDart data port := by
    simpa using hboundary
  subst dart
  exact boundaryPortDart_not_mem_map_retainedDartToAmbientDart
    data darts port hdart

/-- The restored ambient merge word has no repeated dart. -/
theorem LocalizedAlignedCommonRunSplice.merge_ambientOutgoingDarts_nodup
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (state : LocalizedCommonRunMergeArmState splice) :
    state.ambientOutgoingDarts.Nodup := by
  cases state with
  | internal hprefix hsuffix =>
      simpa [LocalizedCommonRunMergeArmState.ambientOutgoingDarts,
        LocalizedCommonRunMergeArmState.collapsedPort] using
        (splice.merge_outgoingDarts_nodup
          (.internal hprefix hsuffix)).map
            (retainedDartToAmbientDart_injective data)
  | prefixPort hnil heq hsuffix =>
      simpa [LocalizedCommonRunMergeArmState.ambientOutgoingDarts,
        LocalizedCommonRunMergeArmState.collapsedPort] using
        map_retainedDartToAmbientDart_append_boundaryPortDart_nodup data
          (splice.merge_outgoingDarts_nodup
            (.prefixPort hnil heq hsuffix)) 0
  | suffixPort hnil heq hprefix =>
      simpa [LocalizedCommonRunMergeArmState.ambientOutgoingDarts,
        LocalizedCommonRunMergeArmState.collapsedPort] using
        map_retainedDartToAmbientDart_append_boundaryPortDart_nodup data
          (splice.merge_outgoingDarts_nodup
            (.suffixPort hnil heq hprefix)) 1

/-- The restored ambient split word has no repeated dart. -/
theorem LocalizedAlignedCommonRunSplice.split_ambientOutgoingDarts_nodup
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (state : LocalizedCommonRunSplitArmState splice) :
    state.ambientOutgoingDarts.Nodup := by
  cases state with
  | internal hprefix hsuffix =>
      simpa [LocalizedCommonRunSplitArmState.ambientOutgoingDarts,
        LocalizedCommonRunSplitArmState.collapsedPort] using
        (splice.split_outgoingDarts_nodup
          (.internal hprefix hsuffix)).map
            (retainedDartToAmbientDart_injective data)
  | prefixPort hnil heq hsuffix =>
      simpa [LocalizedCommonRunSplitArmState.ambientOutgoingDarts,
        LocalizedCommonRunSplitArmState.collapsedPort] using
        map_retainedDartToAmbientDart_append_boundaryPortDart_nodup data
          (splice.split_outgoingDarts_nodup
            (.prefixPort hnil heq hsuffix)) 2
  | suffixPort hnil heq hprefix =>
      simpa [LocalizedCommonRunSplitArmState.ambientOutgoingDarts,
        LocalizedCommonRunSplitArmState.collapsedPort] using
        map_retainedDartToAmbientDart_append_boundaryPortDart_nodup data
          (splice.split_outgoingDarts_nodup
            (.suffixPort hnil heq hprefix)) 3

/-- Cubicity makes the restored merge word the complete ambient dart fiber
at the merge. -/
theorem LocalizedAlignedCommonRunSplice.merge_dartsAt_eq_ambientOutgoingDarts
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (state : LocalizedCommonRunMergeArmState splice) :
    graphData.toRotationSystem.dartsAt
        (pair.prefixSharedEdgeDart profile.firstRank).fst.1 =
      state.ambientOutgoingDarts.toFinset := by
  change (Finset.univ.filter fun dart : G.Dart =>
      dart.fst =
        (pair.prefixSharedEdgeDart profile.firstRank).fst.1) = _
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro dart hdart
    rw [List.mem_toFinset] at hdart
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact state.ambientOutgoingDarts_fst_eq hdart
  · have hcubicAt :=
      hcubic (pair.prefixSharedEdgeDart profile.firstRank).fst.1
    change (Finset.univ.filter fun dart : G.Dart =>
      dart.fst =
        (pair.prefixSharedEdgeDart profile.firstRank).fst.1).card = 3 at hcubicAt
    rw [hcubicAt,
      List.toFinset_card_of_nodup
        (splice.merge_ambientOutgoingDarts_nodup state),
      state.ambientOutgoingDarts_length]

/-- Cubicity makes the restored split word the complete ambient dart fiber
at the split. -/
theorem LocalizedAlignedCommonRunSplice.split_dartsAt_eq_ambientOutgoingDarts
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (state : LocalizedCommonRunSplitArmState splice) :
    graphData.toRotationSystem.dartsAt
        (pair.prefixSharedEdgeDart profile.lastRank).snd.1 =
      state.ambientOutgoingDarts.toFinset := by
  change (Finset.univ.filter fun dart : G.Dart =>
      dart.fst =
        (pair.prefixSharedEdgeDart profile.lastRank).snd.1) = _
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro dart hdart
    rw [List.mem_toFinset] at hdart
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact state.ambientOutgoingDarts_fst_eq hdart
  · have hcubicAt :=
      hcubic (pair.prefixSharedEdgeDart profile.lastRank).snd.1
    change (Finset.univ.filter fun dart : G.Dart =>
      dart.fst =
        (pair.prefixSharedEdgeDart profile.lastRank).snd.1).card = 3 at hcubicAt
    rw [hcubicAt,
      List.toFinset_card_of_nodup
        (splice.split_ambientOutgoingDarts_nodup state),
      state.ambientOutgoingDarts_length]

end GoertzelV24AdjacentPairInsertion.AdjacentPairData
end
end Mettapedia.GraphTheory.FourColor
