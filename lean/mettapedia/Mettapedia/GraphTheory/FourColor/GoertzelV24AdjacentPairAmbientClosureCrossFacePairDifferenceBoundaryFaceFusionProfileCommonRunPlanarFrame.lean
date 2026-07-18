import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunFusionSkeleton
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionAmbientTrailFaceCutTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairRotationPortFaceCut

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
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

/-- Over the two-element field, two values distinct from a fixed value are
equal. -/
theorem f2_eq_of_ne_of_ne (fixed first second : F2)
    (hfirst : fixed ≠ first) (hsecond : fixed ≠ second) :
    first = second := by
  fin_cases fixed <;> fin_cases first <;> fin_cases second <;> simp_all

/-- The actual ambient prefix direction at the common-run merge, including
the restored port direction when the prefix arm is collapsed. -/
def LocalizedCommonRunMergeArmState.ambientPrefixDart
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunMergeArmState splice → G.Dart
  | .internal hprefix _ =>
      retainedDartToAmbientDart data
        (splice.trunk.prefixIncomingArm.lastDart hprefix).symm
  | .prefixPort _ _ _ => boundaryPortDart data 0
  | .suffixPort _ _ hprefix =>
      retainedDartToAmbientDart data
        (splice.trunk.prefixIncomingArm.lastDart hprefix).symm

/-- The actual ambient prefix direction at the common-run split, including
the restored port direction when the prefix arm is collapsed. -/
def LocalizedCommonRunSplitArmState.ambientPrefixDart
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunSplitArmState splice → G.Dart
  | .internal hprefix _ =>
      retainedDartToAmbientDart data
        (splice.trunk.prefixOutgoingArm.firstDart hprefix)
  | .prefixPort _ _ _ => boundaryPortDart data 2
  | .suffixPort _ _ hprefix =>
      retainedDartToAmbientDart data
        (splice.trunk.prefixOutgoingArm.firstDart hprefix)

/-- The actual ambient suffix direction at the common-run merge, including
the restored port direction when the suffix arm is collapsed. -/
def LocalizedCommonRunMergeArmState.ambientSuffixDart
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunMergeArmState splice → G.Dart
  | .internal _ hsuffix =>
      retainedDartToAmbientDart data
        (splice.trunk.suffixIncomingArm.lastDart hsuffix).symm
  | .prefixPort _ _ hsuffix =>
      retainedDartToAmbientDart data
        (splice.trunk.suffixIncomingArm.lastDart hsuffix).symm
  | .suffixPort _ _ _ => boundaryPortDart data 1

/-- The actual ambient suffix direction at the common-run split, including
the restored port direction when the suffix arm is collapsed. -/
def LocalizedCommonRunSplitArmState.ambientSuffixDart
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunSplitArmState splice → G.Dart
  | .internal _ hsuffix =>
      retainedDartToAmbientDart data
        (splice.trunk.suffixOutgoingArm.firstDart hsuffix)
  | .prefixPort _ _ hsuffix =>
      retainedDartToAmbientDart data
        (splice.trunk.suffixOutgoingArm.firstDart hsuffix)
  | .suffixPort _ _ _ => boundaryPortDart data 3

/-- The displayed prefix position is the concrete ambient prefix dart at
the merge. -/
theorem LocalizedCommonRunMergeArmState.ambientRotation_displayedDart_eq_prefix
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) :
    rotation.displayedDart state.ambientPrefixPosition =
      state.ambientPrefixDart := by
  cases state <;>
    have hword := rotation.word_eq <;>
    simp [LocalizedCommonRunMergeArmState.ambientOutgoingDarts,
      LocalizedCommonRunMergeArmState.outgoingDarts,
      LocalizedCommonRunMergeArmState.collapsedPort,
      LocalizedCommonRunMergeArmState.ambientPrefixPosition,
      LocalizedCommonRunMergeArmState.ambientPrefixDart] at hword ⊢
  · exact (List.cons.inj hword).1.symm
  · exact (List.cons.inj (List.cons.inj
      (List.cons.inj hword).2).2).1.symm
  · exact (List.cons.inj hword).1.symm

/-- The displayed prefix position is the concrete ambient prefix dart at
the split. -/
theorem LocalizedCommonRunSplitArmState.ambientRotation_displayedDart_eq_prefix
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) :
    rotation.displayedDart state.ambientPrefixPosition =
      state.ambientPrefixDart := by
  cases state <;>
    have hword := rotation.word_eq <;>
    simp [LocalizedCommonRunSplitArmState.ambientOutgoingDarts,
      LocalizedCommonRunSplitArmState.outgoingDarts,
      LocalizedCommonRunSplitArmState.collapsedPort,
      LocalizedCommonRunSplitArmState.ambientPrefixPosition,
      LocalizedCommonRunSplitArmState.ambientPrefixDart] at hword ⊢
  · exact (List.cons.inj (List.cons.inj hword).2).1.symm
  · exact (List.cons.inj (List.cons.inj
      (List.cons.inj hword).2).2).1.symm
  · exact (List.cons.inj (List.cons.inj hword).2).1.symm

/-- The displayed suffix position is the concrete ambient suffix dart at
the merge. -/
theorem LocalizedCommonRunMergeArmState.ambientRotation_displayedDart_eq_suffix
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) :
    rotation.displayedDart state.ambientSuffixPosition =
      state.ambientSuffixDart := by
  cases state <;>
    have hword := rotation.word_eq <;>
    simp [LocalizedCommonRunMergeArmState.ambientOutgoingDarts,
      LocalizedCommonRunMergeArmState.outgoingDarts,
      LocalizedCommonRunMergeArmState.collapsedPort,
      LocalizedCommonRunMergeArmState.ambientSuffixPosition,
      LocalizedCommonRunMergeArmState.ambientSuffixDart] at hword ⊢
  · exact (List.cons.inj (List.cons.inj hword).2).1.symm
  · exact (List.cons.inj hword).1.symm
  · exact (List.cons.inj (List.cons.inj
      (List.cons.inj hword).2).2).1.symm

/-- The displayed suffix position is the concrete ambient suffix dart at
the split. -/
theorem LocalizedCommonRunSplitArmState.ambientRotation_displayedDart_eq_suffix
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) :
    rotation.displayedDart state.ambientSuffixPosition =
      state.ambientSuffixDart := by
  cases state <;>
    have hword := rotation.word_eq <;>
    simp [LocalizedCommonRunSplitArmState.ambientOutgoingDarts,
      LocalizedCommonRunSplitArmState.outgoingDarts,
      LocalizedCommonRunSplitArmState.collapsedPort,
      LocalizedCommonRunSplitArmState.ambientSuffixPosition,
      LocalizedCommonRunSplitArmState.ambientSuffixDart] at hword ⊢
  · exact (List.cons.inj (List.cons.inj
      (List.cons.inj hword).2).2).1.symm
  · exact (List.cons.inj (List.cons.inj hword).2).1.symm
  · exact (List.cons.inj (List.cons.inj
      (List.cons.inj hword).2).2).1.symm

/-- The edge predicate carried by the closed prefix successor. -/
def oppositePortClosureCut
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (edge : G.edgeSet) : Prop :=
  edge.1 ∈ (data.oppositePortClosure path).edges

/-- Every retained edge on the suffix incoming arm avoids the closed prefix
successor. -/
theorem LocalizedAlignedCommonRunSplice.suffixIncomingArm_not_cut
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    ∀ edge ∈ splice.trunk.suffixIncomingArm.edgeSubtypeSupport,
      ¬oppositePortClosureCut data pair.prefixTrail
        (retainedEdgeToAmbientEdge data edge) := by
  intro edge hedge hcut
  have harm : edge.1 ∈ splice.trunk.suffixIncomingArm.edges := by
    rw [← splice.trunk.suffixIncomingArm.edgeSubtypeSupport_map_val]
    exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
  have hprefix : edge.1 ∈ pair.prefixTrail.edges :=
    (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
      data pair.prefixTrail edge).1 hcut
  exact (List.disjoint_left.mp
    splice.trunk.suffixIncomingArm_disjoint_prefixTrail) harm hprefix

/-- Every retained edge on the suffix outgoing arm avoids the closed prefix
successor. -/
theorem LocalizedAlignedCommonRunSplice.suffixOutgoingArm_not_cut
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile) :
    ∀ edge ∈ splice.trunk.suffixOutgoingArm.edgeSubtypeSupport,
      ¬oppositePortClosureCut data pair.prefixTrail
        (retainedEdgeToAmbientEdge data edge) := by
  intro edge hedge hcut
  have harm : edge.1 ∈ splice.trunk.suffixOutgoingArm.edges := by
    rw [← splice.trunk.suffixOutgoingArm.edgeSubtypeSupport_map_val]
    exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
  have hprefix : edge.1 ∈ pair.prefixTrail.edges :=
    (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
      data pair.prefixTrail edge).1 hcut
  exact (List.disjoint_left.mp
    splice.trunk.suffixOutgoingArm_disjoint_prefixTrail) harm hprefix

/-- Exact-cut labels transport from port `1` to the merge along the clean
suffix incoming arm. -/
theorem LocalizedAlignedCommonRunSplice.suffixIncomingArm_labels_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        oppositePortClosureCut data pair.prefixTrail
          (graphData.toRotationSystem.edgeOf dart))
    (hnil : ¬splice.trunk.suffixIncomingArm.Nil) :
    labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          (splice.trunk.suffixIncomingArm.firstDart hnil))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          (splice.trunk.suffixIncomingArm.lastDart hnil).symm)) := by
  apply retainedTrail_labels_eq_terminalDarts_of_support_not_cut
    graphData hcubic hrotation data labels
      (oppositePortClosureCut data pair.prefixTrail) hexact
      splice.trunk.suffixIncomingArm hnil
      splice.arms_arePaths.2.2.1.isTrail
      splice.trunk.suffixIncomingArm.edgeSubtypeSupport
  · intro edge hedge
    rw [SimpleGraph.Walk.edgeSubtypeSupport_map_val]
    exact hedge
  · exact splice.suffixIncomingArm_not_cut

/-- Exact-cut labels transport from the split to port `3` along the clean
suffix outgoing arm. -/
theorem LocalizedAlignedCommonRunSplice.suffixOutgoingArm_labels_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        oppositePortClosureCut data pair.prefixTrail
          (graphData.toRotationSystem.edgeOf dart))
    (hnil : ¬splice.trunk.suffixOutgoingArm.Nil) :
    labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          (splice.trunk.suffixOutgoingArm.firstDart hnil))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          (splice.trunk.suffixOutgoingArm.lastDart hnil).symm)) := by
  apply retainedTrail_labels_eq_terminalDarts_of_support_not_cut
    graphData hcubic hrotation data labels
      (oppositePortClosureCut data pair.prefixTrail) hexact
      splice.trunk.suffixOutgoingArm hnil
      splice.arms_arePaths.2.2.2.isTrail
      splice.trunk.suffixOutgoingArm.edgeSubtypeSupport
  · intro edge hedge
    rw [SimpleGraph.Walk.edgeSubtypeSupport_map_val]
    exact hedge
  · exact splice.suffixOutgoingArm_not_cut

/-- At the merge, the prefix direction belongs to the closed prefix
successor. -/
theorem LocalizedCommonRunMergeArmState.ambientPrefixDart_cut
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) :
    oppositePortClosureCut data pair.prefixTrail
      (graphData.toRotationSystem.edgeOf state.ambientPrefixDart) := by
  cases state with
  | internal hprefix _ =>
      simp only [LocalizedCommonRunMergeArmState.ambientPrefixDart]
      unfold oppositePortClosureCut
      have hedge : graphData.toRotationSystem.edgeOf
          (retainedDartToAmbientDart data
            (splice.trunk.prefixIncomingArm.lastDart hprefix).symm) =
          retainedEdgeToAmbientEdge data
            (splice.trunk.prefixIncomingArm.lastEdgeSet hprefix) := by
        apply Subtype.ext
        simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
      rw [hedge]
      rw [retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff]
      exact splice.trunk.prefixIncomingArm_edges_subset
        (splice.trunk.prefixIncomingArm.lastEdgeSet_val_mem_edges hprefix)
  | prefixPort _ _ _ =>
      simp only [LocalizedCommonRunMergeArmState.ambientPrefixDart]
      unfold oppositePortClosureCut
      have hedge : graphData.toRotationSystem.edgeOf
          (boundaryPortDart data 0) = boundaryEdge data 0 := by
        apply Subtype.ext
        simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
      rw [hedge]
      change boundaryEdgeValue data 0 ∈
        (data.oppositePortClosure pair.prefixTrail).edges
      rw [data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff]
      exact Or.inl rfl
  | suffixPort _ _ hprefix =>
      simp only [LocalizedCommonRunMergeArmState.ambientPrefixDart]
      unfold oppositePortClosureCut
      have hedge : graphData.toRotationSystem.edgeOf
          (retainedDartToAmbientDart data
            (splice.trunk.prefixIncomingArm.lastDart hprefix).symm) =
          retainedEdgeToAmbientEdge data
            (splice.trunk.prefixIncomingArm.lastEdgeSet hprefix) := by
        apply Subtype.ext
        simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
      rw [hedge]
      rw [retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff]
      exact splice.trunk.prefixIncomingArm_edges_subset
        (splice.trunk.prefixIncomingArm.lastEdgeSet_val_mem_edges hprefix)

/-- At the split, the prefix direction belongs to the closed prefix
successor. -/
theorem LocalizedCommonRunSplitArmState.ambientPrefixDart_cut
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) :
    oppositePortClosureCut data pair.prefixTrail
      (graphData.toRotationSystem.edgeOf state.ambientPrefixDart) := by
  cases state with
  | internal hprefix _ =>
      simp only [LocalizedCommonRunSplitArmState.ambientPrefixDart]
      unfold oppositePortClosureCut
      have hedge : graphData.toRotationSystem.edgeOf
          (retainedDartToAmbientDart data
            (splice.trunk.prefixOutgoingArm.firstDart hprefix)) =
          retainedEdgeToAmbientEdge data
            (splice.trunk.prefixOutgoingArm.firstEdgeSet hprefix) := by
        apply Subtype.ext
        simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
      rw [hedge]
      rw [retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff]
      exact splice.trunk.prefixOutgoingArm_edges_subset
        (splice.trunk.prefixOutgoingArm.firstEdgeSet_val_mem_edges hprefix)
  | prefixPort _ _ _ =>
      simp only [LocalizedCommonRunSplitArmState.ambientPrefixDart]
      unfold oppositePortClosureCut
      have hedge : graphData.toRotationSystem.edgeOf
          (boundaryPortDart data 2) = boundaryEdge data 2 := by
        apply Subtype.ext
        simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
      rw [hedge]
      change boundaryEdgeValue data 2 ∈
        (data.oppositePortClosure pair.prefixTrail).edges
      rw [data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff]
      exact Or.inr rfl
  | suffixPort _ _ hprefix =>
      simp only [LocalizedCommonRunSplitArmState.ambientPrefixDart]
      unfold oppositePortClosureCut
      have hedge : graphData.toRotationSystem.edgeOf
          (retainedDartToAmbientDart data
            (splice.trunk.prefixOutgoingArm.firstDart hprefix)) =
          retainedEdgeToAmbientEdge data
            (splice.trunk.prefixOutgoingArm.firstEdgeSet hprefix) := by
        apply Subtype.ext
        simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
      rw [hedge]
      rw [retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff]
      exact splice.trunk.prefixOutgoingArm_edges_subset
        (splice.trunk.prefixOutgoingArm.firstEdgeSet_val_mem_edges hprefix)

/-- At the merge, the suffix direction avoids the closed prefix
successor. -/
theorem LocalizedCommonRunMergeArmState.ambientSuffixDart_not_cut
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) :
    ¬oppositePortClosureCut data pair.prefixTrail
      (graphData.toRotationSystem.edgeOf state.ambientSuffixDart) := by
  cases state with
  | internal _ hsuffix | prefixPort _ _ hsuffix =>
      simp only [LocalizedCommonRunMergeArmState.ambientSuffixDart]
      intro hcut
      unfold oppositePortClosureCut at hcut
      have hedge : graphData.toRotationSystem.edgeOf
          (retainedDartToAmbientDart data
            (splice.trunk.suffixIncomingArm.lastDart hsuffix).symm) =
          retainedEdgeToAmbientEdge data
            (splice.trunk.suffixIncomingArm.lastEdgeSet hsuffix) := by
        apply Subtype.ext
        simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
      rw [hedge] at hcut
      have hprefix :=
        (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
          data pair.prefixTrail
            (splice.trunk.suffixIncomingArm.lastEdgeSet hsuffix)).1 hcut
      exact (List.disjoint_left.mp
        splice.trunk.suffixIncomingArm_disjoint_prefixTrail)
          (splice.trunk.suffixIncomingArm.lastEdgeSet_val_mem_edges hsuffix)
          hprefix
  | suffixPort _ _ _ =>
      simp only [LocalizedCommonRunMergeArmState.ambientSuffixDart]
      intro hcut
      have hcut' : boundaryEdgeValue data 1 ∈
          (data.oppositePortClosure pair.prefixTrail).edges := by
        simpa [oppositePortClosureCut,
          SimpleGraphDartRotation.Data.toRotationSystem_edgeOf] using hcut
      have := (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff
        pair.prefixTrail 1).1 hcut'
      omega

/-- At the split, the suffix direction avoids the closed prefix
successor. -/
theorem LocalizedCommonRunSplitArmState.ambientSuffixDart_not_cut
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) :
    ¬oppositePortClosureCut data pair.prefixTrail
      (graphData.toRotationSystem.edgeOf state.ambientSuffixDart) := by
  cases state with
  | internal _ hsuffix | prefixPort _ _ hsuffix =>
      simp only [LocalizedCommonRunSplitArmState.ambientSuffixDart]
      intro hcut
      unfold oppositePortClosureCut at hcut
      have hedge : graphData.toRotationSystem.edgeOf
          (retainedDartToAmbientDart data
            (splice.trunk.suffixOutgoingArm.firstDart hsuffix)) =
          retainedEdgeToAmbientEdge data
            (splice.trunk.suffixOutgoingArm.firstEdgeSet hsuffix) := by
        apply Subtype.ext
        simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
      rw [hedge] at hcut
      have hprefix :=
        (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
          data pair.prefixTrail
            (splice.trunk.suffixOutgoingArm.firstEdgeSet hsuffix)).1 hcut
      exact (List.disjoint_left.mp
        splice.trunk.suffixOutgoingArm_disjoint_prefixTrail)
          (splice.trunk.suffixOutgoingArm.firstEdgeSet_val_mem_edges hsuffix)
          hprefix
  | suffixPort _ _ _ =>
      simp only [LocalizedCommonRunSplitArmState.ambientSuffixDart]
      intro hcut
      have hcut' : boundaryEdgeValue data 3 ∈
          (data.oppositePortClosure pair.prefixTrail).edges := by
        simpa [oppositePortClosureCut,
          SimpleGraphDartRotation.Data.toRotationSystem_edgeOf] using hcut
      have := (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff
        pair.prefixTrail 3).1 hcut'
      omega

/-- The displayed common-trunk direction at the merge belongs to the closed
prefix successor. -/
theorem LocalizedCommonRunMergeArmState.ambientTrunkDart_cut
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) :
    oppositePortClosureCut data pair.prefixTrail
      (graphData.toRotationSystem.edgeOf
        (rotation.displayedDart state.ambientTrunkPosition)) := by
  rw [state.ambientRotation_displayedDart_eq_trunk rotation]
  unfold oppositePortClosureCut
  have hedge : graphData.toRotationSystem.edgeOf
      (pair.ambientPrefixSharedEdgeDart profile.firstRank) =
      retainedEdgeToAmbientEdge data
        (pair.sharedEdgeAt profile.firstRank) := by
    apply Subtype.ext
    simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
  rw [hedge]
  rw [retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff]
  exact pair.sharedEdgeAt_val_mem_prefixTrail_edges profile.firstRank

/-- The displayed reversed common-trunk direction at the split belongs to
the closed prefix successor. -/
theorem LocalizedCommonRunSplitArmState.ambientTrunkDart_cut
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) :
    oppositePortClosureCut data pair.prefixTrail
      (graphData.toRotationSystem.edgeOf
        (rotation.displayedDart state.ambientTrunkPosition)) := by
  rw [state.ambientRotation_displayedDart_eq_trunk rotation]
  unfold oppositePortClosureCut
  have hedge : graphData.toRotationSystem.edgeOf
      (pair.ambientPrefixSharedEdgeDart profile.lastRank).symm =
      retainedEdgeToAmbientEdge data
        (pair.sharedEdgeAt profile.lastRank) := by
    apply Subtype.ext
    simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
  rw [hedge]
  rw [retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff]
  exact pair.sharedEdgeAt_val_mem_prefixTrail_edges profile.lastRank

/-- The restored edge at unused port `1` avoids the closed prefix
successor. -/
theorem boundaryPortDart_one_not_cut
    {graphData : Data G} (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)) :
    ¬oppositePortClosureCut data path
      (graphData.toRotationSystem.edgeOf (boundaryPortDart data 1)) := by
  intro hcut
  unfold oppositePortClosureCut at hcut
  have hedge : graphData.toRotationSystem.edgeOf
      (boundaryPortDart data 1) = boundaryEdge data 1 := by
    apply Subtype.ext
    simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
  rw [hedge] at hcut
  change boundaryEdgeValue data 1 ∈
    (data.oppositePortClosure path).edges at hcut
  have := (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff
    path 1).1 hcut
  omega

/-- The restored edge at unused port `3` avoids the closed prefix
successor. -/
theorem boundaryPortDart_three_not_cut
    {graphData : Data G} (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)) :
    ¬oppositePortClosureCut data path
      (graphData.toRotationSystem.edgeOf (boundaryPortDart data 3)) := by
  intro hcut
  unfold oppositePortClosureCut at hcut
  have hedge : graphData.toRotationSystem.edgeOf
      (boundaryPortDart data 3) = boundaryEdge data 3 := by
    apply Subtype.ext
    simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
  rw [hedge] at hcut
  change boundaryEdgeValue data 3 ∈
    (data.oppositePortClosure path).edges at hcut
  have := (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff
    path 3).1 hcut
  omega

/-- The first suffix-incoming dart and restored port `1` dart expose the
same exact-cut label. -/
theorem LocalizedAlignedCommonRunSplice.suffixIncomingFirst_label_eq_port_one
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        oppositePortClosureCut data pair.prefixTrail
          (graphData.toRotationSystem.edgeOf dart))
    (hnil : ¬splice.trunk.suffixIncomingArm.Nil) :
    labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          (splice.trunk.suffixIncomingArm.firstDart hnil))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data 1)) := by
  apply graphData.toRotationSystem
    |>.labels_eq_of_distinct_dartsAt_of_edges_not_cut
      hcubic hrotation labels
        (oppositePortClosureCut data pair.prefixTrail) hexact
  · simp [SimpleGraphDartRotation.Data.toRotationSystem_vertOf,
      retainedDartToAmbientDart_fst, retainedPort]
  · intro heq
    apply boundaryPortDart_not_mem_map_retainedDartToAmbientDart
      data [splice.trunk.suffixIncomingArm.firstDart hnil] 1
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    exact heq.symm
  · have hsupport : splice.trunk.suffixIncomingArm.firstEdgeSet hnil ∈
        splice.trunk.suffixIncomingArm.edgeSubtypeSupport := by
      unfold SimpleGraph.Walk.edgeSubtypeSupport
      exact List.mem_map.mpr
        ⟨splice.trunk.suffixIncomingArm.firstDart hnil,
          splice.trunk.suffixIncomingArm.firstDart_mem_darts hnil, rfl⟩
    have hnot := splice.suffixIncomingArm_not_cut
      (splice.trunk.suffixIncomingArm.firstEdgeSet hnil) hsupport
    have hedge : graphData.toRotationSystem.edgeOf
        (retainedDartToAmbientDart data
          (splice.trunk.suffixIncomingArm.firstDart hnil)) =
        retainedEdgeToAmbientEdge data
          (splice.trunk.suffixIncomingArm.firstEdgeSet hnil) := by
      apply Subtype.ext
      simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
    rwa [hedge]
  · exact boundaryPortDart_one_not_cut data pair.prefixTrail

/-- The reversed last suffix-outgoing dart and restored port `3` dart expose
the same exact-cut label. -/
theorem LocalizedAlignedCommonRunSplice.suffixOutgoingLast_label_eq_port_three
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        oppositePortClosureCut data pair.prefixTrail
          (graphData.toRotationSystem.edgeOf dart))
    (hnil : ¬splice.trunk.suffixOutgoingArm.Nil) :
    labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          (splice.trunk.suffixOutgoingArm.lastDart hnil).symm)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data 3)) := by
  apply graphData.toRotationSystem
    |>.labels_eq_of_distinct_dartsAt_of_edges_not_cut
      hcubic hrotation labels
        (oppositePortClosureCut data pair.prefixTrail) hexact
  · simp [SimpleGraphDartRotation.Data.toRotationSystem_vertOf,
      retainedDartToAmbientDart_fst, retainedPort]
  · intro heq
    apply boundaryPortDart_not_mem_map_retainedDartToAmbientDart
      data [(splice.trunk.suffixOutgoingArm.lastDart hnil).symm] 3
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    exact heq.symm
  · have hsupport : splice.trunk.suffixOutgoingArm.lastEdgeSet hnil ∈
        splice.trunk.suffixOutgoingArm.edgeSubtypeSupport := by
      unfold SimpleGraph.Walk.edgeSubtypeSupport
      exact List.mem_map.mpr
        ⟨splice.trunk.suffixOutgoingArm.lastDart hnil,
          splice.trunk.suffixOutgoingArm.lastDart_mem_darts hnil, rfl⟩
    have hnot := splice.suffixOutgoingArm_not_cut
      (splice.trunk.suffixOutgoingArm.lastEdgeSet hnil) hsupport
    have hedge : graphData.toRotationSystem.edgeOf
        (retainedDartToAmbientDart data
          (splice.trunk.suffixOutgoingArm.lastDart hnil).symm) =
        retainedEdgeToAmbientEdge data
          (splice.trunk.suffixOutgoingArm.lastEdgeSet hnil) := by
      apply Subtype.ext
      simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
    rwa [hedge]
  · exact boundaryPortDart_three_not_cut data pair.prefixTrail

/-- The concrete suffix direction at the merge carries the exact-cut label
of unused boundary port `1`. -/
theorem LocalizedCommonRunMergeArmState.ambientSuffix_label_eq_port_one
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        oppositePortClosureCut data pair.prefixTrail
          (graphData.toRotationSystem.edgeOf dart)) :
    labels (dartOrbitFace graphData.toRotationSystem
        state.ambientSuffixDart) =
      labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data 1)) := by
  cases state with
  | internal _ hsuffix | prefixPort _ _ hsuffix =>
      simp only [LocalizedCommonRunMergeArmState.ambientSuffixDart]
      exact (splice.suffixIncomingArm_labels_eq hcubic hrotation labels
        hexact hsuffix).symm.trans
          (splice.suffixIncomingFirst_label_eq_port_one hcubic hrotation
            labels hexact hsuffix)
  | suffixPort _ _ _ =>
      rfl

/-- The concrete suffix direction at the split carries the exact-cut label
of unused boundary port `3`. -/
theorem LocalizedCommonRunSplitArmState.ambientSuffix_label_eq_port_three
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        oppositePortClosureCut data pair.prefixTrail
          (graphData.toRotationSystem.edgeOf dart)) :
    labels (dartOrbitFace graphData.toRotationSystem
        state.ambientSuffixDart) =
      labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data 3)) := by
  cases state with
  | internal _ hsuffix | prefixPort _ _ hsuffix =>
      simp only [LocalizedCommonRunSplitArmState.ambientSuffixDart]
      exact (splice.suffixOutgoingArm_labels_eq hcubic hrotation labels
        hexact hsuffix).trans
          (splice.suffixOutgoingLast_label_eq_port_three hcubic hrotation
            labels hexact hsuffix)
  | suffixPort _ _ _ =>
      rfl

/-- At a clean merge, the suffix dart has the selected remote-face label
exactly when that face selects the suffix route. -/
theorem LocalizedCommonRunMergeArmState.ambientSuffix_label_eq_face_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts)
    (labels : OrbitFace graphData.toRotationSystem → F2)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        oppositePortClosureCut data pair.prefixTrail
          (graphData.toRotationSystem.edgeOf dart))
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    labels (dartOrbitFace graphData.toRotationSystem
        state.ambientSuffixDart) = labels face ↔
      state.ambientTrunkFaceRoute rotation = true := by
  have hprefix := (hexact state.ambientPrefixDart).2
    state.ambientPrefixDart_cut
  have htrunk :=
    (hexact (rotation.displayedDart state.ambientTrunkPosition)).2
      (state.ambientTrunkDart_cut rotation)
  have hsuffix :
      labels (dartOrbitFace graphData.toRotationSystem
          state.ambientSuffixDart) =
        labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha state.ambientSuffixDart)) := by
    by_contra hne
    exact state.ambientSuffixDart_not_cut ((hexact _).1 hne)
  have hface := state.ambientRotation_faceMateSideFace_eq
    rotation htwoSided
  have hfaceLabels := congrArg labels hface
  rw [← hfaceLabels,
    ← state.ambientRotation_displayedDart_eq_suffix rotation]
  rw [← state.ambientRotation_displayedDart_eq_prefix rotation]
    at hprefix
  rw [← state.ambientRotation_displayedDart_eq_suffix rotation]
    at hsuffix
  have hfirstFace := congrArg labels rotation.dartOrbitFace_alpha_first
  have hsecondFace := congrArg labels rotation.dartOrbitFace_alpha_second
  have hthirdFace := congrArg labels rotation.dartOrbitFace_alpha_third
  clear hexact htwoSided hface hfaceLabels
  cases state <;> cases horientation : rotation.orientation <;>
    cases hside : splice.mergeTrunkFaceSide <;>
    simp [LocalizedCommonRunMergeArmState.ambientPrefixPosition,
      LocalizedCommonRunMergeArmState.ambientSuffixPosition,
      LocalizedCommonRunMergeArmState.ambientTrunkPosition,
      LocalizedCommonRunMergeArmState.ambientTrunkFaceRoute,
      LocalizedCommonRunMergeArmState.ambientTrunkFaceMatePosition,
      RotationSystem.ThreeDartRotation.faceMatePosition,
      RotationSystem.orientedStepPosition,
      RotationSystem.ThreeDartRotation.displayedDart,
      RotationSystem.ThreeDartRotation.displayedSideOrbitFace,
      RotationSystem.dartSideOrbitFace, horientation, hside]
      at hprefix hsuffix htrunk hfirstFace hsecondFace hthirdFace ⊢ <;>
    simp_all

/-- At a clean split, the suffix dart has the selected remote-face label
exactly when that face selects the suffix route. -/
theorem LocalizedCommonRunSplitArmState.ambientSuffix_label_eq_face_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts)
    (labels : OrbitFace graphData.toRotationSystem → F2)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        oppositePortClosureCut data pair.prefixTrail
          (graphData.toRotationSystem.edgeOf dart))
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    labels (dartOrbitFace graphData.toRotationSystem
        state.ambientSuffixDart) = labels face ↔
      state.ambientTrunkFaceRoute rotation = true := by
  have hprefix := (hexact state.ambientPrefixDart).2
    state.ambientPrefixDart_cut
  have htrunk :=
    (hexact (rotation.displayedDart state.ambientTrunkPosition)).2
      (state.ambientTrunkDart_cut rotation)
  have hsuffix :
      labels (dartOrbitFace graphData.toRotationSystem
          state.ambientSuffixDart) =
        labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha state.ambientSuffixDart)) := by
    by_contra hne
    exact state.ambientSuffixDart_not_cut ((hexact _).1 hne)
  have hface := state.ambientRotation_faceMateSideFace_eq
    rotation htwoSided
  have hfaceLabels := congrArg labels hface
  rw [← hfaceLabels,
    ← state.ambientRotation_displayedDart_eq_suffix rotation]
  rw [← state.ambientRotation_displayedDart_eq_prefix rotation]
    at hprefix
  rw [← state.ambientRotation_displayedDart_eq_suffix rotation]
    at hsuffix
  have hfirstFace := congrArg labels rotation.dartOrbitFace_alpha_first
  have hsecondFace := congrArg labels rotation.dartOrbitFace_alpha_second
  have hthirdFace := congrArg labels rotation.dartOrbitFace_alpha_third
  clear hexact htwoSided hface hfaceLabels
  cases state <;> cases horientation : rotation.orientation <;>
    cases hside : splice.splitTrunkFaceSide <;>
    simp [LocalizedCommonRunSplitArmState.ambientPrefixPosition,
      LocalizedCommonRunSplitArmState.ambientSuffixPosition,
      LocalizedCommonRunSplitArmState.ambientTrunkPosition,
      LocalizedCommonRunSplitArmState.ambientTrunkFaceRoute,
      LocalizedCommonRunSplitArmState.ambientTrunkFaceMatePosition,
      RotationSystem.ThreeDartRotation.faceMatePosition,
      RotationSystem.orientedStepPosition,
      RotationSystem.ThreeDartRotation.displayedDart,
      RotationSystem.ThreeDartRotation.displayedSideOrbitFace,
      RotationSystem.dartSideOrbitFace, horientation, hside]
      at hprefix hsuffix htrunk hfirstFace hsecondFace hthirdFace ⊢ <;>
    simp_all

/-- Distinct unused-port labels force the remote face to change route across
a clean common trunk. -/
theorem LocalizedAlignedCommonRunSplice.ambientEndpointRouteFlip_eq_true_of_exactCut
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (mergeState : LocalizedCommonRunMergeArmState splice)
    (splitState : LocalizedCommonRunSplitArmState splice)
    (mergeRotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem mergeState.ambientOutgoingDarts)
    (splitRotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem splitState.ambientOutgoingDarts)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (labels : OrbitFace graphData.toRotationSystem → F2)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        oppositePortClosureCut data pair.prefixTrail
          (graphData.toRotationSystem.edgeOf dart))
    (hports :
      labels (dartOrbitFace graphData.toRotationSystem
          (boundaryPortDart data 1)) ≠
        labels (dartOrbitFace graphData.toRotationSystem
          (boundaryPortDart data 3))) :
    splice.ambientEndpointRouteFlip mergeState splitState
        mergeRotation splitRotation = true := by
  have hmergePort := mergeState.ambientSuffix_label_eq_port_one
    hcubic hrotation labels hexact
  have hsplitPort := splitState.ambientSuffix_label_eq_port_three
    hcubic hrotation labels hexact
  have hsuffixNe :
      labels (dartOrbitFace graphData.toRotationSystem
          mergeState.ambientSuffixDart) ≠
        labels (dartOrbitFace graphData.toRotationSystem
          splitState.ambientSuffixDart) := by
    intro heq
    apply hports
    exact hmergePort.symm.trans (heq.trans hsplitPort)
  have hmergeFace := mergeState.ambientSuffix_label_eq_face_iff
    mergeRotation labels hexact htwoSided
  have hsplitFace := splitState.ambientSuffix_label_eq_face_iff
    splitRotation labels hexact htwoSided
  unfold LocalizedAlignedCommonRunSplice.ambientEndpointRouteFlip
  cases hm : mergeState.ambientTrunkFaceRoute mergeRotation <;>
    cases hs : splitState.ambientTrunkFaceRoute splitRotation
  · have hmne : labels (dartOrbitFace graphData.toRotationSystem
          mergeState.ambientSuffixDart) ≠ labels face := by
      intro heq
      have := hmergeFace.mp heq
      simp [hm] at this
    have hsne : labels (dartOrbitFace graphData.toRotationSystem
          splitState.ambientSuffixDart) ≠ labels face := by
      intro heq
      have := hsplitFace.mp heq
      simp [hs] at this
    exact False.elim (hsuffixNe
      (f2_eq_of_ne_of_ne (labels face)
        (labels (dartOrbitFace graphData.toRotationSystem
          mergeState.ambientSuffixDart))
        (labels (dartOrbitFace graphData.toRotationSystem
          splitState.ambientSuffixDart)) hmne.symm hsne.symm))
  · rfl
  · rfl
  · have hmface := hmergeFace.mpr hm
    have hsface := hsplitFace.mpr hs
    exact False.elim (hsuffixNe (hmface.trans hsface.symm))

/-- In a vertex-minimal spherical counterexample, every clean common-run
certificate has odd endpoint-frame parity. -/
theorem LocalizedCommonRunEndpointChiralCertificate.frameParity_eq_true_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {pair : RetainedIntersectionExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    {oldCross : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    {mergeState : LocalizedCommonRunMergeArmState splice}
    {splitState : LocalizedCommonRunSplitArmState splice}
    (certificate : LocalizedCommonRunEndpointChiralCertificate splice
      mergeState splitState) :
    RotationSystem.threeArmEndpointFrameParity
        mergeState.ambientRouteOrderFlipped
        splitState.ambientRouteOrderFlipped
        certificate.mergeRotation.orientation
        certificate.splitRotation.orientation = true := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rcases baseData.exists_rotationOrdered_oppositePortClosure_exactFaceCut_of_minimal
      graphData minimal minimal.spherical.cubic
        minimal.vertexRotationCyclic pair.prefixTrail splice.prefix_isPath with
    ⟨labels, _, hexact, _, _, hports⟩
  have hexact' : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        oppositePortClosureCut data pair.prefixTrail
          (graphData.toRotationSystem.edgeOf dart) := by
    simpa only [oppositePortClosureCut] using hexact
  have hflip := splice.ambientEndpointRouteFlip_eq_true_of_exactCut
    mergeState splitState certificate.mergeRotation certificate.splitRotation
      minimal.spherical.cubic minimal.vertexRotationCyclic
      minimal.facesTwoSided labels hexact' hports
  exact certificate.routeFlip_eq_frameParity.symm.trans hflip

/-- Consequently, the canonical clean common-run transfer in a minimal
spherical counterexample is the diagonal endpoint-and-route flip. -/
theorem LocalizedCommonRunEndpointChiralCertificate.signedTransfer_eq_diagonal_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {pair : RetainedIntersectionExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    {oldCross : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    {mergeState : LocalizedCommonRunMergeArmState splice}
    {splitState : LocalizedCommonRunSplitArmState splice}
    (certificate : LocalizedCommonRunEndpointChiralCertificate splice
      mergeState splitState) :
    certificate.signedTransfer = signedRoutePermutation true true := by
  rw [certificate.signedTransfer_eq_frameParity,
    certificate.frameParity_eq_true_of_minimal graphData minimal baseData]

/-- A signed fusion-chain resolution is diagonal in its clean branch; all
cycle and descent branches satisfy the predicate vacuously. -/
def LocalizedFusionChainSignedTransferResolution.CleanTransferIsDiagonal
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (resolution : LocalizedFusionChainSignedTransferResolution pair
      oldCross face) : Prop :=
  match resolution with
  | .cleanFourArms _ _ _ _ _ certificate _ =>
      certificate.signedTransfer = signedRoutePermutation true true
  | _ => True

/-- Every chiral fusion-chain resolution in a minimal spherical
counterexample admits a signed resolution whose clean transfer is exactly
diagonal. -/
theorem LocalizedFusionChainChiralResolution.exists_signedTransferResolution_with_diagonal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {pair : RetainedIntersectionExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    {oldCross : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (resolution : LocalizedFusionChainChiralResolution pair oldCross face) :
    ∃ signed : LocalizedFusionChainSignedTransferResolution pair oldCross
        face,
      signed.CleanTransferIsDiagonal := by
  cases resolution with
  | parallelArmCycle profile splice cycle =>
      exact ⟨LocalizedFusionChainSignedTransferResolution.parallelArmCycle
        profile splice cycle, trivial⟩
  | crossedArmCycle profile splice cycle =>
      exact ⟨LocalizedFusionChainSignedTransferResolution.crossedArmCycle
        profile splice cycle, trivial⟩
  | cleanFourArms profile splice clean mergeState splitState certificate =>
      refine ⟨LocalizedFusionChainSignedTransferResolution.cleanFourArms
        profile splice clean mergeState splitState certificate
          certificate.signedTransfer_ne_refl, ?_⟩
      exact certificate.signedTransfer_eq_diagonal_of_minimal
        graphData minimal baseData
  | alignedBubbleCycle profile bubble =>
      exact ⟨LocalizedFusionChainSignedTransferResolution.alignedBubbleCycle
        profile bubble, trivial⟩
  | strictlyShorterMixedPortCycles descent =>
      exact ⟨
        LocalizedFusionChainSignedTransferResolution.strictlyShorterMixedPortCycles
          descent, trivial⟩
  | orderInversionPrimalCycle descent =>
      exact ⟨
        LocalizedFusionChainSignedTransferResolution.orderInversionPrimalCycle
          descent, trivial⟩

/-- A width-at-least-two successor profile in a minimal spherical
counterexample reaches a signed resolution with exact diagonal clean
transfer. -/
theorem LocalizedSuccessorFusionChainProfile.exists_signedTransferResolution_with_diagonal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {oldCross : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {prefixSuccessor : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).Walk
        ((baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic).retainedPort 0)
        ((baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic).retainedPort 2)}
    {suffixSuccessor : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).Walk
        ((baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic).retainedPort 1)
        ((baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic).retainedPort 3)}
    (successor : LocalizedSuccessorFusionChainProfile oldCross face
      prefixSuccessor suffixSuccessor)
    (hprefix : successor.pair.prefixTrail.IsPath)
    (hsuffix : successor.pair.suffixTrail.IsPath) :
    ∃ signed : LocalizedFusionChainSignedTransferResolution successor.pair
        oldCross face,
      signed.CleanTransferIsDiagonal := by
  rcases successor.nonempty_chiralResolution hprefix hsuffix
      minimal.spherical.cubic minimal.vertexRotationCyclic
        minimal.facesTwoSided with ⟨resolution⟩
  exact resolution.exists_signedTransferResolution_with_diagonal
    graphData minimal baseData

/-- The successor trichotomy with every clean fusion-chain branch carrying
the exact diagonal signed transfer. -/
def LocalizedFusionSuccessorResolution.DiagonalTransferOutcome
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
      ∃ signed : LocalizedFusionChainSignedTransferResolution
          successor.pair cross face,
        signed.CleanTransferIsDiagonal)

/-- Every resolved successor pair in a minimal spherical counterexample
realizes the diagonal-transfer-refined outcome. -/
theorem LocalizedFusionSuccessorResolution.finite_diagonalTransfer_outcome
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross}
    {face : OrbitFace graphData.toRotationSystem}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    (successors : LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion) :
    successors.DiagonalTransferOutcome := by
  unfold LocalizedFusionSuccessorResolution.DiagonalTransferOutcome
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
      successor.exists_signedTransferResolution_with_diagonal
        graphData minimal baseData hprefix hsuffix⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
