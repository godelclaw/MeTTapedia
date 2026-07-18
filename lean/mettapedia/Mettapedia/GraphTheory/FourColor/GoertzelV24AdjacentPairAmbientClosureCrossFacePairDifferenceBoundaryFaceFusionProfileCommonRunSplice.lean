import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunTrunk

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} {Graph : SimpleGraph Vertex}

/-- Cutting immediately before the first selected edge and immediately
after the second selected edge decomposes a walk into its incoming arm,
closed edge interval, and outgoing arm. -/
theorem edges_eq_take_append_edgeInterval_append_drop
    {left right : Vertex} (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first ≤ second) :
    walk.edges =
      (walk.take first.val).edges ++
        (walk.edgeInterval first second horder).edges ++
          (walk.drop (second.val + 1)).edges := by
  simp only [edges_take, edgeInterval_edges, edges_drop]
  calc
    walk.edges = walk.edges.take first.val ++
        walk.edges.drop first.val :=
      (List.take_append_drop first.val walk.edges).symm
    _ = walk.edges.take first.val ++
        ((walk.edges.drop first.val).take
            (second.val - first.val + 1) ++
          (walk.edges.drop first.val).drop
            (second.val - first.val + 1)) := by
      congr 1
      exact (List.take_append_drop
        (second.val - first.val + 1)
        (walk.edges.drop first.val)).symm
    _ = walk.edges.take first.val ++
        ((walk.edges.drop first.val).take
            (second.val - first.val + 1) ++
          walk.edges.drop (second.val + 1)) := by
      rw [List.drop_drop]
      have horderValue : first.val ≤ second.val := horder
      have hindex : first.val + (second.val - first.val + 1) =
          second.val + 1 := by
        omega
      rw [hindex]
    _ = (walk.edges.take first.val ++
          (walk.edges.drop first.val).take
            (second.val - first.val + 1)) ++
        walk.edges.drop (second.val + 1) := by
      rw [List.append_assoc]

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

/-- The prefix trail before it enters the common trunk. -/
def LocalizedAlignedCommonRunTrunk.prefixIncomingArm
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (_trunk : LocalizedAlignedCommonRunTrunk profile) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 0) (pair.prefixSharedEdgeDart profile.firstRank).fst :=
  (pair.prefixTrail.take
    (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val).copy
      rfl (by
        simp only [RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart,
          SimpleGraph.Walk.dartAtEdgePosition_fst])

/-- The suffix trail before it enters the same oriented common trunk. -/
def LocalizedAlignedCommonRunTrunk.suffixIncomingArm
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (_trunk : LocalizedAlignedCommonRunTrunk profile) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 1) (pair.prefixSharedEdgeDart profile.firstRank).fst :=
  (pair.suffixTrail.take
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv profile.firstRank)).val).copy rfl (by
        calc
          pair.suffixTrail.getVert
                (pair.suffixSharedEdgePositionEmbedding
                  (pair.sharedEdgeOrderEquiv profile.firstRank)).val =
              (pair.suffixSharedEdgeDart profile.firstRank).fst := by
            simp only [
              RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDart,
              SimpleGraph.Walk.dartAtEdgePosition_fst]
          _ = (pair.prefixSharedEdgeDart profile.firstRank).fst :=
            congrArg (fun dart ↦ dart.fst)
              (profile.darts_eq profile.firstRank))

/-- The prefix trail after it leaves the common trunk. -/
def LocalizedAlignedCommonRunTrunk.prefixOutgoingArm
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (_trunk : LocalizedAlignedCommonRunTrunk profile) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (pair.prefixSharedEdgeDart profile.lastRank).snd
      (data.retainedPort 2) :=
  (pair.prefixTrail.drop
    ((pair.prefixSharedEdgePositionEmbedding profile.lastRank).val + 1)).copy
      (by
        simp only [RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart,
          SimpleGraph.Walk.dartAtEdgePosition_snd]) rfl

/-- The suffix trail after it leaves the common trunk. -/
def LocalizedAlignedCommonRunTrunk.suffixOutgoingArm
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (_trunk : LocalizedAlignedCommonRunTrunk profile) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (pair.prefixSharedEdgeDart profile.lastRank).snd
      (data.retainedPort 3) :=
  (pair.suffixTrail.drop
    ((pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv profile.lastRank)).val + 1)).copy (by
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
              (profile.darts_eq profile.lastRank)) rfl

/-- The prefix successor is exactly its incoming arm, common trunk, and
outgoing arm, in that order. -/
theorem LocalizedAlignedCommonRunTrunk.prefixTrail_edges_decomposition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    pair.prefixTrail.edges =
      trunk.prefixIncomingArm.edges ++
        trunk.chain.prefixCommonRun.edges ++
          trunk.prefixOutgoingArm.edges := by
  simpa only [LocalizedAlignedCommonRunTrunk.prefixIncomingArm,
    LocalizedAlignedCommonRunTrunk.prefixOutgoingArm,
    LocalizedAlignedCommonRunChain.prefixCommonRun,
    RetainedIntersectionExactFaceCutPair.prefixSharedEdgeInterval,
    SimpleGraph.Walk.edges_copy] using
      pair.prefixTrail.edges_eq_take_append_edgeInterval_append_drop
        (pair.prefixSharedEdgePositionEmbedding profile.firstRank)
        (pair.prefixSharedEdgePositionEmbedding profile.lastRank)
        ((pair.prefixSharedEdgePositionEmbedding.le_iff_le).2
          profile.firstRank_lt_lastRank.le)

/-- The suffix successor has the same exact three-piece decomposition. -/
theorem LocalizedAlignedCommonRunTrunk.suffixTrail_edges_decomposition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    pair.suffixTrail.edges =
      trunk.suffixIncomingArm.edges ++
        trunk.chain.suffixCommonRun.edges ++
          trunk.suffixOutgoingArm.edges := by
  simpa only [LocalizedAlignedCommonRunTrunk.suffixIncomingArm,
    LocalizedAlignedCommonRunTrunk.suffixOutgoingArm,
    LocalizedAlignedCommonRunChain.suffixCommonRun,
    SimpleGraph.Walk.edges_copy] using
      pair.suffixTrail.edges_eq_take_append_edgeInterval_append_drop
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv profile.firstRank))
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv profile.lastRank))
        ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2
          (profile.sharedEdgeOrderEquiv_lt
            profile.firstRank_lt_lastRank).le)

/-- In the prefix decomposition, the middle piece is literally the
ordered shared-edge word. -/
theorem LocalizedAlignedCommonRunTrunk.prefixTrail_edges_eq_arms_sharedWord
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    pair.prefixTrail.edges =
      trunk.prefixIncomingArm.edges ++ pair.prefixSharedEdgeOrder ++
        trunk.prefixOutgoingArm.edges := by
  rw [trunk.prefixTrail_edges_decomposition, trunk.prefix_edges]

/-- The same literal shared word is the middle piece of the suffix
decomposition. -/
theorem LocalizedAlignedCommonRunTrunk.suffixTrail_edges_eq_arms_sharedWord
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    pair.suffixTrail.edges =
      trunk.suffixIncomingArm.edges ++ pair.prefixSharedEdgeOrder ++
        trunk.suffixOutgoingArm.edges := by
  rw [trunk.suffixTrail_edges_decomposition, trunk.suffix_edges]

/-- Each prefix arm is a path whenever the full prefix successor is a
path. -/
theorem LocalizedAlignedCommonRunTrunk.prefixArms_arePaths
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile)
    (hpath : pair.prefixTrail.IsPath) :
    trunk.prefixIncomingArm.IsPath ∧
      trunk.prefixOutgoingArm.IsPath := by
  constructor
  · rw [LocalizedAlignedCommonRunTrunk.prefixIncomingArm,
      SimpleGraph.Walk.isPath_copy]
    exact hpath.take _
  · rw [LocalizedAlignedCommonRunTrunk.prefixOutgoingArm,
      SimpleGraph.Walk.isPath_copy]
    exact hpath.drop _

/-- Each suffix arm is a path whenever the full suffix successor is a
path. -/
theorem LocalizedAlignedCommonRunTrunk.suffixArms_arePaths
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile)
    (hpath : pair.suffixTrail.IsPath) :
    trunk.suffixIncomingArm.IsPath ∧
      trunk.suffixOutgoingArm.IsPath := by
  constructor
  · rw [LocalizedAlignedCommonRunTrunk.suffixIncomingArm,
      SimpleGraph.Walk.isPath_copy]
    exact hpath.take _
  · rw [LocalizedAlignedCommonRunTrunk.suffixOutgoingArm,
      SimpleGraph.Walk.isPath_copy]
    exact hpath.drop _

/-- The prefix incoming arm is supported on the prefix successor. -/
theorem LocalizedAlignedCommonRunTrunk.prefixIncomingArm_edges_subset
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    trunk.prefixIncomingArm.edges ⊆ pair.prefixTrail.edges := by
  intro edge hedge
  rw [trunk.prefixTrail_edges_eq_arms_sharedWord]
  simp only [List.mem_append]
  exact Or.inl (Or.inl hedge)

/-- The prefix outgoing arm is supported on the prefix successor. -/
theorem LocalizedAlignedCommonRunTrunk.prefixOutgoingArm_edges_subset
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    trunk.prefixOutgoingArm.edges ⊆ pair.prefixTrail.edges := by
  intro edge hedge
  rw [trunk.prefixTrail_edges_eq_arms_sharedWord]
  simp only [List.mem_append]
  exact Or.inr hedge

/-- The suffix incoming arm is supported on the suffix successor. -/
theorem LocalizedAlignedCommonRunTrunk.suffixIncomingArm_edges_subset
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    trunk.suffixIncomingArm.edges ⊆ pair.suffixTrail.edges := by
  intro edge hedge
  rw [trunk.suffixTrail_edges_eq_arms_sharedWord]
  simp only [List.mem_append]
  exact Or.inl (Or.inl hedge)

/-- The suffix outgoing arm is supported on the suffix successor. -/
theorem LocalizedAlignedCommonRunTrunk.suffixOutgoingArm_edges_subset
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    trunk.suffixOutgoingArm.edges ⊆ pair.suffixTrail.edges := by
  intro edge hedge
  rw [trunk.suffixTrail_edges_eq_arms_sharedWord]
  simp only [List.mem_append]
  exact Or.inr hedge

/-- No edge before the prefix trunk occurs anywhere on the suffix
successor. -/
theorem LocalizedAlignedCommonRunTrunk.prefixIncomingArm_disjoint_suffixTrail
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    trunk.prefixIncomingArm.edges.Disjoint pair.suffixTrail.edges := by
  have hnodup :
      (trunk.prefixIncomingArm.edges ++ pair.prefixSharedEdgeOrder ++
        trunk.prefixOutgoingArm.edges).Nodup := by
    rw [← trunk.prefixTrail_edges_eq_arms_sharedWord]
    exact pair.prefixRetained_isTrail.edges_nodup
  have hincomingShared : trunk.prefixIncomingArm.edges.Disjoint
      pair.prefixSharedEdgeOrder :=
    hnodup.of_append_left.disjoint
  rw [List.disjoint_left]
  intro edge hincoming hsuffix
  have hprefix := trunk.prefixIncomingArm_edges_subset hincoming
  have hshared : edge ∈ pair.prefixSharedEdgeOrder :=
    (pair.mem_prefixSharedEdgeOrder_iff edge).2 ⟨hprefix, hsuffix⟩
  exact (List.disjoint_left.mp hincomingShared) hincoming hshared

/-- No edge after the prefix trunk occurs anywhere on the suffix
successor. -/
theorem LocalizedAlignedCommonRunTrunk.prefixOutgoingArm_disjoint_suffixTrail
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    trunk.prefixOutgoingArm.edges.Disjoint pair.suffixTrail.edges := by
  have hnodup :
      (trunk.prefixIncomingArm.edges ++ pair.prefixSharedEdgeOrder ++
        trunk.prefixOutgoingArm.edges).Nodup := by
    rw [← trunk.prefixTrail_edges_eq_arms_sharedWord]
    exact pair.prefixRetained_isTrail.edges_nodup
  have hleftOutgoing :
      (trunk.prefixIncomingArm.edges ++
        pair.prefixSharedEdgeOrder).Disjoint
          trunk.prefixOutgoingArm.edges := hnodup.disjoint
  rw [List.disjoint_left]
  intro edge houtgoing hsuffix
  have hprefix := trunk.prefixOutgoingArm_edges_subset houtgoing
  have hshared : edge ∈ pair.prefixSharedEdgeOrder :=
    (pair.mem_prefixSharedEdgeOrder_iff edge).2 ⟨hprefix, hsuffix⟩
  exact (List.disjoint_left.mp hleftOutgoing)
    (by
      simp only [List.mem_append]
      exact Or.inr hshared)
    houtgoing

/-- No edge before the suffix trunk occurs anywhere on the prefix
successor. -/
theorem LocalizedAlignedCommonRunTrunk.suffixIncomingArm_disjoint_prefixTrail
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    trunk.suffixIncomingArm.edges.Disjoint pair.prefixTrail.edges := by
  have hnodup :
      (trunk.suffixIncomingArm.edges ++ pair.prefixSharedEdgeOrder ++
        trunk.suffixOutgoingArm.edges).Nodup := by
    rw [← trunk.suffixTrail_edges_eq_arms_sharedWord]
    exact pair.suffixRetained_isTrail.edges_nodup
  have hincomingShared : trunk.suffixIncomingArm.edges.Disjoint
      pair.prefixSharedEdgeOrder :=
    hnodup.of_append_left.disjoint
  rw [List.disjoint_left]
  intro edge hincoming hprefix
  have hsuffix := trunk.suffixIncomingArm_edges_subset hincoming
  have hshared : edge ∈ pair.prefixSharedEdgeOrder :=
    (pair.mem_prefixSharedEdgeOrder_iff edge).2 ⟨hprefix, hsuffix⟩
  exact (List.disjoint_left.mp hincomingShared) hincoming hshared

/-- No edge after the suffix trunk occurs anywhere on the prefix
successor. -/
theorem LocalizedAlignedCommonRunTrunk.suffixOutgoingArm_disjoint_prefixTrail
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    trunk.suffixOutgoingArm.edges.Disjoint pair.prefixTrail.edges := by
  have hnodup :
      (trunk.suffixIncomingArm.edges ++ pair.prefixSharedEdgeOrder ++
        trunk.suffixOutgoingArm.edges).Nodup := by
    rw [← trunk.suffixTrail_edges_eq_arms_sharedWord]
    exact pair.suffixRetained_isTrail.edges_nodup
  have hleftOutgoing :
      (trunk.suffixIncomingArm.edges ++
        pair.prefixSharedEdgeOrder).Disjoint
          trunk.suffixOutgoingArm.edges := hnodup.disjoint
  rw [List.disjoint_left]
  intro edge houtgoing hprefix
  have hsuffix := trunk.suffixOutgoingArm_edges_subset houtgoing
  have hshared : edge ∈ pair.prefixSharedEdgeOrder :=
    (pair.mem_prefixSharedEdgeOrder_iff edge).2 ⟨hprefix, hsuffix⟩
  exact (List.disjoint_left.mp hleftOutgoing)
    (by
      simp only [List.mem_append]
      exact Or.inr hshared)
    houtgoing

/-- A common trunk together with the path certificates for its two full
successors. Each canonical arm shares no edge with the opposite successor. -/
structure LocalizedAlignedCommonRunSplice
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face) where
  trunk : LocalizedAlignedCommonRunTrunk profile
  prefix_isPath : pair.prefixTrail.IsPath
  suffix_isPath : pair.suffixTrail.IsPath

/-- The four arms of a merge--split splice are paths. -/
theorem LocalizedAlignedCommonRunSplice.arms_arePaths
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    splice.trunk.prefixIncomingArm.IsPath ∧
      splice.trunk.prefixOutgoingArm.IsPath ∧
      splice.trunk.suffixIncomingArm.IsPath ∧
      splice.trunk.suffixOutgoingArm.IsPath := by
  have hprefix := splice.trunk.prefixArms_arePaths splice.prefix_isPath
  have hsuffix := splice.trunk.suffixArms_arePaths splice.suffix_isPath
  exact ⟨hprefix.1, hprefix.2, hsuffix.1, hsuffix.2⟩

/-- Every prefix arm is edge-disjoint from every suffix arm. -/
theorem LocalizedAlignedCommonRunSplice.crossArms_pairwise_disjoint
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    splice.trunk.prefixIncomingArm.edges.Disjoint
        splice.trunk.suffixIncomingArm.edges ∧
      splice.trunk.prefixIncomingArm.edges.Disjoint
        splice.trunk.suffixOutgoingArm.edges ∧
      splice.trunk.prefixOutgoingArm.edges.Disjoint
        splice.trunk.suffixIncomingArm.edges ∧
      splice.trunk.prefixOutgoingArm.edges.Disjoint
        splice.trunk.suffixOutgoingArm.edges := by
  have hprefixIncoming :=
    splice.trunk.prefixIncomingArm_disjoint_suffixTrail
  have hprefixOutgoing :=
    splice.trunk.prefixOutgoingArm_disjoint_suffixTrail
  constructor
  · rw [List.disjoint_left]
    intro edge hprefix hsuffix
    exact (List.disjoint_left.mp hprefixIncoming) hprefix
      (splice.trunk.suffixIncomingArm_edges_subset hsuffix)
  constructor
  · rw [List.disjoint_left]
    intro edge hprefix hsuffix
    exact (List.disjoint_left.mp hprefixIncoming) hprefix
      (splice.trunk.suffixOutgoingArm_edges_subset hsuffix)
  constructor
  · rw [List.disjoint_left]
    intro edge hprefix hsuffix
    exact (List.disjoint_left.mp hprefixOutgoing) hprefix
      (splice.trunk.suffixIncomingArm_edges_subset hsuffix)
  · rw [List.disjoint_left]
    intro edge hprefix hsuffix
    exact (List.disjoint_left.mp hprefixOutgoing) hprefix
      (splice.trunk.suffixOutgoingArm_edges_subset hsuffix)

/-- Add the two successor path certificates to a common trunk. -/
def LocalizedAlignedCommonRunTrunk.toCommonRunSplice
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile)
    (hprefix : pair.prefixTrail.IsPath)
    (hsuffix : pair.suffixTrail.IsPath) :
    LocalizedAlignedCommonRunSplice profile :=
  ⟨trunk, hprefix, hsuffix⟩

/-- The fusion-chain normal form with its aligned terminal branch exposed
as an exact four-arm merge--split splice. -/
inductive LocalizedFusionChainSpliceResolution
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  | commonRunSplice
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : Nonempty (LocalizedAlignedCommonRunSplice profile))
  | alignedBubbleCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (bubble : Nonempty (LocalizedAlignedBubblePrimalCycle profile))
  | strictlyShorterMixedPortCycles
      (descent : Nonempty
        (LocalizedStrictlyShorterMixedPortCycles pair oldCross face))
  | orderInversionPrimalCycle
      (descent : Nonempty
        (LocalizedOrderInversionPrimalCycle pair oldCross face))

/-- Upgrade the common-trunk normal form to its exact four-arm splice
whenever the two successors are paths. -/
theorem LocalizedFusionChainTrunkResolution.nonempty_spliceResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (resolution : LocalizedFusionChainTrunkResolution pair oldCross face)
    (hprefix : pair.prefixTrail.IsPath)
    (hsuffix : pair.suffixTrail.IsPath) :
    Nonempty (LocalizedFusionChainSpliceResolution pair oldCross face) := by
  cases resolution with
  | commonRunTrunk profile trunk =>
      rcases trunk with ⟨trunk⟩
      exact ⟨LocalizedFusionChainSpliceResolution.commonRunSplice
        profile ⟨trunk.toCommonRunSplice hprefix hsuffix⟩⟩
  | alignedBubbleCycle profile bubble =>
      exact ⟨LocalizedFusionChainSpliceResolution.alignedBubbleCycle
        profile bubble⟩
  | strictlyShorterMixedPortCycles descent =>
      exact ⟨
        LocalizedFusionChainSpliceResolution.strictlyShorterMixedPortCycles
          descent⟩
  | orderInversionPrimalCycle descent =>
      exact ⟨LocalizedFusionChainSpliceResolution.orderInversionPrimalCycle
        descent⟩

/-- A width-at-least-two successor profile reaches the four-arm splice
normal form under its inherited path certificates. -/
theorem LocalizedSuccessorFusionChainProfile.nonempty_spliceResolution
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
    Nonempty (LocalizedFusionChainSpliceResolution successor.pair oldCross
      face) := by
  rcases successor.nonempty_trunkResolution with ⟨resolution⟩
  exact resolution.nonempty_spliceResolution hprefix hsuffix

/-- The successor-pair trichotomy with its width-at-least-two branch
strengthened to the exact four-arm merge--split splice. -/
def LocalizedFusionSuccessorResolution.SpliceOutcome
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
        Nonempty (LocalizedFusionChainSpliceResolution successor.pair cross
          face))

/-- Every resolved successor pair realizes its exact splice outcome. -/
theorem LocalizedFusionSuccessorResolution.finite_splice_outcome
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
    successors.SpliceOutcome := by
  unfold LocalizedFusionSuccessorResolution.SpliceOutcome
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
      successor.nonempty_spliceResolution hprefix hsuffix⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
