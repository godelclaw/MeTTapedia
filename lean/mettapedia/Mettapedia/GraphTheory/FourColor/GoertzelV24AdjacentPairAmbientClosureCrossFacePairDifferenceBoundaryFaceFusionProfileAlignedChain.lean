import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileResolution

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} {Graph : SimpleGraph Vertex}

/-- The open subwalk strictly between two selected edge positions. -/
def edgeOpenInterval {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first < second) :
    Graph.Walk (walk.getVert (first.val + 1)) (walk.getVert second.val) :=
  ((walk.drop (first.val + 1)).take
      (second.val - first.val - 1)).copy rfl (by
    rw [drop_getVert]
    congr 1
    omega)

@[simp] theorem edgeOpenInterval_length {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first < second) :
    (walk.edgeOpenInterval first second horder).length =
      second.val - first.val - 1 := by
  simp only [edgeOpenInterval, length_copy, take_length, drop_length]
  apply Nat.min_eq_left
  have hsecond := second.isLt
  have hlength := walk.length_edges
  omega

@[simp] theorem edgeOpenInterval_edges {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first < second) :
    (walk.edgeOpenInterval first second horder).edges =
      (walk.edges.drop (first.val + 1)).take
        (second.val - first.val - 1) := by
  simp [edgeOpenInterval, edges_take, edges_drop]

theorem edgeOpenInterval_isSubwalk {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first < second) :
    (walk.edgeOpenInterval first second horder).IsSubwalk walk := by
  unfold edgeOpenInterval
  exact ((((walk.drop (first.val + 1)).isSubwalk_take
    (second.val - first.val - 1)).trans
      (walk.isSubwalk_drop (first.val + 1))).copy _ _ rfl rfl)

theorem IsTrail.edgeOpenInterval {left right : Vertex}
    {walk : Graph.Walk left right} (htrail : walk.IsTrail)
    (first second : Fin walk.edges.length) (horder : first < second) :
    (walk.edgeOpenInterval first second horder).IsTrail :=
  isTrail_of_isSubwalk
    (walk.edgeOpenInterval_isSubwalk first second horder) htrail

theorem IsPath.edgeOpenInterval {left right : Vertex}
    {walk : Graph.Walk left right} (hpath : walk.IsPath)
    (first second : Fin walk.edges.length) (horder : first < second) :
    (walk.edgeOpenInterval first second horder).IsPath :=
  isPath_of_isSubwalk
    (walk.edgeOpenInterval_isSubwalk first second horder) hpath

/-- Every edge of an open interval has an exact original position strictly
between its two selected boundary positions. -/
theorem exists_edgePosition_between_of_mem_edgeOpenInterval
    {left right : Vertex} (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first < second)
    {edge : Sym2 Vertex}
    (hedge : edge ∈ (walk.edgeOpenInterval first second horder).edges) :
    ∃ position : Fin walk.edges.length,
      first < position ∧ position < second ∧
        walk.edges.get position = edge := by
  rw [walk.edgeOpenInterval_edges, List.mem_iff_getElem] at hedge
  rcases hedge with ⟨index, hindex, hvalue⟩
  simp only [List.length_take, List.length_drop] at hindex
  have hindexInterior : index < second.val - first.val - 1 :=
    lt_of_lt_of_le hindex (Nat.min_le_left _ _)
  have hbetween : first.val + 1 + index < second.val := by
    calc
      first.val + 1 + index <
          first.val + 1 + (second.val - first.val - 1) :=
        Nat.add_lt_add_left hindexInterior (first.val + 1)
      _ = second.val := by omega
  have hfirstBetween : first.val < first.val + 1 + index := by omega
  have hraw :
      walk.edges[first.val + 1 + index]'(by
        have hsecond := second.isLt
        omega) = edge := by
    simpa only [List.getElem_take, List.getElem_drop] using hvalue
  exact ⟨⟨first.val + 1 + index, by
      have hsecond := second.isLt
      exact lt_trans hbetween hsecond⟩, hfirstBetween, hbetween, hraw⟩

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24TwoEdgeCutMinimality
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

/-- Literal rank alignment makes the suffix occurrences of two increasing
profile ranks increase as well. -/
theorem LocalizedAlignedSharedEdgeProfile.sharedEdgeOrderEquiv_lt
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    {first second : Fin pair.prefixSharedEdgeOrder.length}
    (horder : first < second) :
    pair.sharedEdgeOrderEquiv first <
      pair.sharedEdgeOrderEquiv second := by
  change (pair.sharedEdgeOrderEquiv first : Nat) <
    (pair.sharedEdgeOrderEquiv second : Nat)
  rw [profile.order_position_val_eq first,
    profile.order_position_val_eq second]
  exact horder

/-- The prefix segment strictly between two aligned shared edges, with
canonical oriented endpoint vertices. -/
def LocalizedAlignedSharedEdgeProfile.prefixOpenInterval
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (_profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (pair.prefixSharedEdgeDart first).snd
      (pair.prefixSharedEdgeDart second).fst :=
  (pair.prefixTrail.edgeOpenInterval
      (pair.prefixSharedEdgePositionEmbedding first)
      (pair.prefixSharedEdgePositionEmbedding second)
      ((pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2 horder)).copy
    (by
      simp only [RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart,
        SimpleGraph.Walk.dartAtEdgePosition_snd])
    (by
      simp only [RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart,
        SimpleGraph.Walk.dartAtEdgePosition_fst])

/-- The corresponding suffix segment, copied to the same canonical
oriented endpoints by the aligned dart certificate. -/
def LocalizedAlignedSharedEdgeProfile.suffixOpenInterval
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (pair.prefixSharedEdgeDart first).snd
      (pair.prefixSharedEdgeDart second).fst :=
  (pair.suffixTrail.edgeOpenInterval
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv first))
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv second))
      ((pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2
        (profile.sharedEdgeOrderEquiv_lt horder))).copy
    (by
      calc
        pair.suffixTrail.getVert
              ((pair.suffixSharedEdgePositionEmbedding
                (pair.sharedEdgeOrderEquiv first)).val + 1) =
            (pair.suffixSharedEdgeDart first).snd := by
          simp only [RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDart,
            SimpleGraph.Walk.dartAtEdgePosition_snd]
        _ = (pair.prefixSharedEdgeDart first).snd :=
          congrArg (fun dart ↦ dart.snd) (profile.darts_eq first))
    (by
      calc
        pair.suffixTrail.getVert
              (pair.suffixSharedEdgePositionEmbedding
                (pair.sharedEdgeOrderEquiv second)).val =
            (pair.suffixSharedEdgeDart second).fst := by
          simp only [RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDart,
            SimpleGraph.Walk.dartAtEdgePosition_fst]
        _ = (pair.prefixSharedEdgeDart second).fst :=
          congrArg (fun dart ↦ dart.fst) (profile.darts_eq second))

@[simp] theorem LocalizedAlignedSharedEdgeProfile.prefixOpenInterval_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second) :
    (profile.prefixOpenInterval first second horder).length =
      (pair.prefixSharedEdgePositionEmbedding second).val -
        (pair.prefixSharedEdgePositionEmbedding first).val - 1 := by
  simp [LocalizedAlignedSharedEdgeProfile.prefixOpenInterval]

@[simp] theorem LocalizedAlignedSharedEdgeProfile.suffixOpenInterval_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second) :
    (profile.suffixOpenInterval first second horder).length =
      (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv second)).val -
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv first)).val - 1 := by
  simp [LocalizedAlignedSharedEdgeProfile.suffixOpenInterval]

/-- Both open aligned intervals remain paths whenever the two complete
successor trails are paths. -/
theorem LocalizedAlignedSharedEdgeProfile.openIntervals_arePaths
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (hprefixPath : pair.prefixTrail.IsPath)
    (hsuffixPath : pair.suffixTrail.IsPath)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second) :
    (profile.prefixOpenInterval first second horder).IsPath ∧
      (profile.suffixOpenInterval first second horder).IsPath := by
  constructor
  · rw [LocalizedAlignedSharedEdgeProfile.prefixOpenInterval,
      SimpleGraph.Walk.isPath_copy]
    exact hprefixPath.edgeOpenInterval _ _ _
  · rw [LocalizedAlignedSharedEdgeProfile.suffixOpenInterval,
      SimpleGraph.Walk.isPath_copy]
    exact hsuffixPath.edgeOpenInterval _ _ _

/-- Between consecutive aligned profile ranks, the two open primal
segments are edge-disjoint. Any common edge would define a third shared
rank strictly between the consecutive pair. -/
theorem LocalizedAlignedSharedEdgeProfile.openIntervals_edges_disjoint_of_consecutive
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second)
    (hconsecutive : second.val = first.val + 1) :
    (profile.prefixOpenInterval first second horder).edges.Disjoint
      (profile.suffixOpenInterval first second horder).edges := by
  rw [List.disjoint_left]
  intro edge hprefix hsuffix
  have hprefixOpen : edge ∈
      (pair.prefixTrail.edgeOpenInterval
        (pair.prefixSharedEdgePositionEmbedding first)
        (pair.prefixSharedEdgePositionEmbedding second)
        ((pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2 horder)).edges := by
    simpa only [LocalizedAlignedSharedEdgeProfile.prefixOpenInterval,
      SimpleGraph.Walk.edges_copy] using hprefix
  rcases pair.prefixTrail.exists_edgePosition_between_of_mem_edgeOpenInterval
      (pair.prefixSharedEdgePositionEmbedding first)
      (pair.prefixSharedEdgePositionEmbedding second)
      ((pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2 horder)
      hprefixOpen with
    ⟨rawPosition, hfirstRaw, hrawSecond, hrawEdge⟩
  have hprefixSource : edge ∈ pair.prefixTrail.edges := by
    have hmem := List.get_mem pair.prefixTrail.edges rawPosition
    rwa [hrawEdge] at hmem
  have hsuffixOpen : edge ∈
      (pair.suffixTrail.edgeOpenInterval
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv first))
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv second))
        ((pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2
          (profile.sharedEdgeOrderEquiv_lt horder))).edges := by
    simpa only [LocalizedAlignedSharedEdgeProfile.suffixOpenInterval,
      SimpleGraph.Walk.edges_copy] using hsuffix
  have hsuffixSource : edge ∈ pair.suffixTrail.edges :=
    (pair.suffixTrail.edgeOpenInterval_isSubwalk
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv first))
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv second))
      ((pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2
        (profile.sharedEdgeOrderEquiv_lt horder))).edges_subset hsuffixOpen
  have hshared : edge ∈ pair.prefixSharedEdgeOrder :=
    (pair.mem_prefixSharedEdgeOrder_iff edge).2
      ⟨hprefixSource, hsuffixSource⟩
  rcases List.get_of_mem hshared with ⟨rank, hrank⟩
  have hrawRank : rawPosition =
      pair.prefixSharedEdgePositionEmbedding rank := by
    apply pair.prefixRetained_isTrail.edges_nodup.get_inj_iff.mp
    calc
      pair.prefixTrail.edges.get rawPosition = edge := hrawEdge
      _ = pair.prefixSharedEdgeOrder.get rank := hrank.symm
      _ = pair.prefixTrail.edges.get
          (pair.prefixSharedEdgePositionEmbedding rank) :=
        pair.prefixSharedEdgePositionEmbedding_preserves_edge rank
  rw [hrawRank] at hfirstRaw hrawSecond
  have hfirstRank : first < rank :=
    (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).1 hfirstRaw
  have hrankSecond : rank < second :=
    (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).1 hrawSecond
  omega

/-- Close a consecutive aligned gap by following the prefix interior and
returning along the reversed suffix interior. -/
def LocalizedAlignedSharedEdgeProfile.closedBubbleWalk
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (pair.prefixSharedEdgeDart first).snd
      (pair.prefixSharedEdgeDart first).snd :=
  (profile.prefixOpenInterval first second horder).append
    (profile.suffixOpenInterval first second horder).reverse

@[simp] theorem LocalizedAlignedSharedEdgeProfile.closedBubbleWalk_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second) :
    (profile.closedBubbleWalk first second horder).length =
      (profile.prefixOpenInterval first second horder).length +
        (profile.suffixOpenInterval first second horder).length := by
  simp [LocalizedAlignedSharedEdgeProfile.closedBubbleWalk]

/-- A nonempty consecutive aligned gap closes to an edge-simple primal
circuit. -/
theorem LocalizedAlignedSharedEdgeProfile.closedBubbleWalk_isCircuit
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (hprefixPath : pair.prefixTrail.IsPath)
    (hsuffixPath : pair.suffixTrail.IsPath)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second)
    (hconsecutive : second.val = first.val + 1)
    (hpositive : 0 <
      (profile.prefixOpenInterval first second horder).length +
        (profile.suffixOpenInterval first second horder).length) :
    (profile.closedBubbleWalk first second horder).IsCircuit := by
  rw [SimpleGraph.Walk.isCircuit_def]
  constructor
  · rw [LocalizedAlignedSharedEdgeProfile.closedBubbleWalk,
      SimpleGraph.Walk.isTrail_append]
    have hpaths := profile.openIntervals_arePaths hprefixPath hsuffixPath
      first second horder
    exact ⟨hpaths.1.isTrail, hpaths.2.isTrail.reverse, by
      simpa only [SimpleGraph.Walk.edges_reverse,
        List.disjoint_reverse_right] using
          profile.openIntervals_edges_disjoint_of_consecutive
            first second horder hconsecutive⟩
  · intro hnil
    have hlength := congrArg SimpleGraph.Walk.length hnil
    rw [profile.closedBubbleWalk_length] at hlength
    simp only [SimpleGraph.Walk.length_nil] at hlength
    omega

/-- The strict primal-cycle outcome carried by a nontrivial aligned
fusion-chain gap. -/
structure LocalizedAlignedBubblePrimalCycle
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face) where
  first : Fin pair.prefixSharedEdgeOrder.length
  second : Fin pair.prefixSharedEdgeOrder.length
  first_lt_second : first < second
  consecutive : second.val = first.val + 1
  positive : 0 <
    (profile.prefixOpenInterval first second first_lt_second).length +
      (profile.suffixOpenInterval first second first_lt_second).length
  cycle : (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).Walk
      (pair.prefixSharedEdgeDart first).snd
      (pair.prefixSharedEdgeDart first).snd
  cycle_isCycle : cycle.IsCycle
  cycle_edges_subset_openIntervals : cycle.edges ⊆
    (profile.prefixOpenInterval first second first_lt_second).edges ++
      (profile.suffixOpenInterval first second first_lt_second).edges
  cycle_length_le_openIntervals : cycle.length ≤
    (profile.prefixOpenInterval first second first_lt_second).length +
      (profile.suffixOpenInterval first second first_lt_second).length

/-- Bypass repeated vertices in a nonempty aligned-gap circuit to obtain
an actual support-certified primal cycle. -/
theorem LocalizedAlignedSharedEdgeProfile.exists_localizedAlignedBubblePrimalCycle
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (hprefixPath : pair.prefixTrail.IsPath)
    (hsuffixPath : pair.suffixTrail.IsPath)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second)
    (hconsecutive : second.val = first.val + 1)
    (hpositive : 0 <
      (profile.prefixOpenInterval first second horder).length +
        (profile.suffixOpenInterval first second horder).length) :
    Nonempty (LocalizedAlignedBubblePrimalCycle profile) := by
  let closed := profile.closedBubbleWalk first second horder
  have hcircuit : closed.IsCircuit :=
    profile.closedBubbleWalk_isCircuit hprefixPath hsuffixPath
      first second horder hconsecutive hpositive
  exact ⟨{
    first := first
    second := second
    first_lt_second := horder
    consecutive := hconsecutive
    positive := hpositive
    cycle := closed.cycleBypass
    cycle_isCycle := hcircuit.isCycle_cycleBypass
    cycle_edges_subset_openIntervals := by
      intro edge hedge
      have hclosed := closed.edges_cycleBypass_subset_edges hedge
      change edge ∈
        (profile.closedBubbleWalk first second horder).edges at hclosed
      rw [LocalizedAlignedSharedEdgeProfile.closedBubbleWalk,
        SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
        List.mem_append] at hclosed
      rcases hclosed with hprefix | hsuffix
      · exact List.mem_append_left _ hprefix
      · exact List.mem_append_right _ (List.mem_reverse.mp hsuffix)
    cycle_length_le_openIntervals := by
      calc
        closed.cycleBypass.length ≤ closed.length :=
          closed.length_cycleBypass_le_length
        _ = _ := profile.closedBubbleWalk_length first second horder }⟩

/-- A bubble cycle saves both boundary edges from each source trail. -/
theorem LocalizedAlignedBubblePrimalCycle.cycle_length_add_four_le_sourceTrails
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (bubble : LocalizedAlignedBubblePrimalCycle profile) :
    bubble.cycle.length + 4 ≤
      pair.prefixTrail.length + pair.suffixTrail.length := by
  have hprefixOrder :=
    (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2
      bubble.first_lt_second
  have hprefixSecond :=
    (pair.prefixSharedEdgePositionEmbedding bubble.second).isLt
  have hprefixLength := pair.prefixTrail.length_edges
  have hprefixBound :
      (profile.prefixOpenInterval bubble.first bubble.second
        bubble.first_lt_second).length + 2 ≤ pair.prefixTrail.length := by
    rw [profile.prefixOpenInterval_length]
    omega
  have hsuffixOrder :=
    (pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2
      (profile.sharedEdgeOrderEquiv_lt bubble.first_lt_second)
  have hsuffixSecond :=
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv bubble.second)).isLt
  have hsuffixLength := pair.suffixTrail.length_edges
  have hsuffixBound :
      (profile.suffixOpenInterval bubble.first bubble.second
        bubble.first_lt_second).length + 2 ≤ pair.suffixTrail.length := by
    rw [profile.suffixOpenInterval_length]
    omega
  have hcycle := bubble.cycle_length_le_openIntervals
  omega

/-- Every aligned-bubble cycle edge belongs to one of the complete source
trails. -/
theorem LocalizedAlignedBubblePrimalCycle.cycle_edges_subset_sourceTrails
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (bubble : LocalizedAlignedBubblePrimalCycle profile) :
    bubble.cycle.edges ⊆
      pair.prefixTrail.edges ++ pair.suffixTrail.edges := by
  intro edge hedge
  rcases List.mem_append.mp
      (bubble.cycle_edges_subset_openIntervals hedge) with
    hprefix | hsuffix
  · apply List.mem_append_left
    rw [LocalizedAlignedSharedEdgeProfile.prefixOpenInterval,
      SimpleGraph.Walk.edges_copy] at hprefix
    exact (pair.prefixTrail.edgeOpenInterval_isSubwalk _ _ _).edges_subset
      hprefix
  · apply List.mem_append_right
    rw [LocalizedAlignedSharedEdgeProfile.suffixOpenInterval,
      SimpleGraph.Walk.edges_copy] at hsuffix
    exact (pair.suffixTrail.edgeOpenInterval_isSubwalk _ _ _).edges_subset
      hsuffix

/-- A zero aligned gap is a literal common-run link: the two shared edges
are consecutive on both trails with no intervening primal edge. -/
structure LocalizedAlignedCommonRunLink
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face) where
  first : Fin pair.prefixSharedEdgeOrder.length
  second : Fin pair.prefixSharedEdgeOrder.length
  first_lt_second : first < second
  consecutive : second.val = first.val + 1
  prefix_open_nil :
    (profile.prefixOpenInterval first second first_lt_second).Nil
  suffix_open_nil :
    (profile.suffixOpenInterval first second first_lt_second).Nil

/-- Every consecutive aligned link is exactly a common-run link or a
support-certified strict primal bubble cycle. -/
theorem LocalizedAlignedSharedEdgeProfile.exists_commonRunLink_or_bubbleCycle
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (hprefixPath : pair.prefixTrail.IsPath)
    (hsuffixPath : pair.suffixTrail.IsPath)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second)
    (hconsecutive : second.val = first.val + 1) :
    Nonempty (LocalizedAlignedCommonRunLink profile) ∨
      Nonempty (LocalizedAlignedBubblePrimalCycle profile) := by
  by_cases hzero :
      (profile.prefixOpenInterval first second horder).length +
        (profile.suffixOpenInterval first second horder).length = 0
  · left
    have hprefixZero :
        (profile.prefixOpenInterval first second horder).length = 0 := by
      omega
    have hsuffixZero :
        (profile.suffixOpenInterval first second horder).length = 0 := by
      omega
    exact ⟨{
      first := first
      second := second
      first_lt_second := horder
      consecutive := hconsecutive
      prefix_open_nil := SimpleGraph.Walk.length_eq_zero_iff.mp hprefixZero
      suffix_open_nil := SimpleGraph.Walk.length_eq_zero_iff.mp hsuffixZero }⟩
  · right
    exact profile.exists_localizedAlignedBubblePrimalCycle
      hprefixPath hsuffixPath first second horder hconsecutive (by omega)

/-- The lower endpoint of the consecutive shared-rank link indexed by
`rank`. -/
def RetainedIntersectionExactFaceCutPair.alignedLinkFirst
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (rank : Fin (pair.prefixSharedEdgeOrder.length - 1)) :
    Fin pair.prefixSharedEdgeOrder.length :=
  ⟨rank.val, by
    have hrank := rank.isLt
    omega⟩

/-- The upper endpoint of that consecutive shared-rank link. -/
def RetainedIntersectionExactFaceCutPair.alignedLinkSecond
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (rank : Fin (pair.prefixSharedEdgeOrder.length - 1)) :
    Fin pair.prefixSharedEdgeOrder.length :=
  ⟨rank.val + 1, by
    have hrank := rank.isLt
    omega⟩

theorem RetainedIntersectionExactFaceCutPair.alignedLinkFirst_lt_second
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (rank : Fin (pair.prefixSharedEdgeOrder.length - 1)) :
    pair.alignedLinkFirst rank < pair.alignedLinkSecond rank := by
  change rank.val < rank.val + 1
  omega

@[simp] theorem RetainedIntersectionExactFaceCutPair.alignedLinkSecond_val
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (rank : Fin (pair.prefixSharedEdgeOrder.length - 1)) :
    (pair.alignedLinkSecond rank).val =
      (pair.alignedLinkFirst rank).val + 1 :=
  rfl

/-- The fully degenerate aligned outcome: every consecutive pair of
shared edges is a literal common-run link on both trails. -/
structure LocalizedAlignedCommonRunChain
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face) where
  links_nil : ∀ rank : Fin (pair.prefixSharedEdgeOrder.length - 1),
    (profile.prefixOpenInterval
        (pair.alignedLinkFirst rank) (pair.alignedLinkSecond rank)
        (pair.alignedLinkFirst_lt_second rank)).Nil ∧
      (profile.suffixOpenInterval
        (pair.alignedLinkFirst rank) (pair.alignedLinkSecond rank)
        (pair.alignedLinkFirst_lt_second rank)).Nil

/-- In a common-run chain, consecutive shared ranks occur at consecutive
raw edge positions of the prefix trail. -/
theorem LocalizedAlignedCommonRunChain.prefix_positions_consecutive
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile)
    (rank : Fin (pair.prefixSharedEdgeOrder.length - 1)) :
    (pair.prefixSharedEdgePositionEmbedding
        (pair.alignedLinkSecond rank)).val =
      (pair.prefixSharedEdgePositionEmbedding
        (pair.alignedLinkFirst rank)).val + 1 := by
  have hzero := SimpleGraph.Walk.length_eq_zero_iff.mpr
    (chain.links_nil rank).1
  rw [profile.prefixOpenInterval_length] at hzero
  have horder :=
    (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2
      (pair.alignedLinkFirst_lt_second rank)
  omega

/-- The same consecutive-position statement holds in the suffix trail. -/
theorem LocalizedAlignedCommonRunChain.suffix_positions_consecutive
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile)
    (rank : Fin (pair.prefixSharedEdgeOrder.length - 1)) :
    (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv
          (pair.alignedLinkSecond rank))).val =
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv
          (pair.alignedLinkFirst rank))).val + 1 := by
  have hzero := SimpleGraph.Walk.length_eq_zero_iff.mpr
    (chain.links_nil rank).2
  rw [profile.suffixOpenInterval_length] at hzero
  have horder :=
    (pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2
      (profile.sharedEdgeOrderEquiv_lt
        (pair.alignedLinkFirst_lt_second rank))
  omega

/-- Globally, an aligned profile is a contiguous common-run chain or one
of its consecutive gaps yields a support-certified strict primal cycle. -/
theorem LocalizedAlignedSharedEdgeProfile.exists_commonRunChain_or_bubbleCycle
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (hprefixPath : pair.prefixTrail.IsPath)
    (hsuffixPath : pair.suffixTrail.IsPath) :
    Nonempty (LocalizedAlignedCommonRunChain profile) ∨
      Nonempty (LocalizedAlignedBubblePrimalCycle profile) := by
  classical
  by_cases hall : ∀ rank : Fin
      (pair.prefixSharedEdgeOrder.length - 1),
      (profile.prefixOpenInterval
          (pair.alignedLinkFirst rank) (pair.alignedLinkSecond rank)
          (pair.alignedLinkFirst_lt_second rank)).Nil ∧
        (profile.suffixOpenInterval
          (pair.alignedLinkFirst rank) (pair.alignedLinkSecond rank)
          (pair.alignedLinkFirst_lt_second rank)).Nil
  · exact Or.inl ⟨⟨hall⟩⟩
  · right
    push Not at hall
    rcases hall with ⟨rank, hnotNil⟩
    let first := pair.alignedLinkFirst rank
    let second := pair.alignedLinkSecond rank
    have horder : first < second := pair.alignedLinkFirst_lt_second rank
    have hconsecutive : second.val = first.val + 1 :=
      pair.alignedLinkSecond_val rank
    have hpositive : 0 <
        (profile.prefixOpenInterval first second horder).length +
          (profile.suffixOpenInterval first second horder).length := by
      by_contra hnotPositive
      have hsum :
          (profile.prefixOpenInterval first second horder).length +
            (profile.suffixOpenInterval first second horder).length = 0 := by
        omega
      have hprefixZero :
          (profile.prefixOpenInterval first second horder).length = 0 := by
        omega
      have hsuffixZero :
          (profile.suffixOpenInterval first second horder).length = 0 := by
        omega
      apply hnotNil
      · simpa only [first, second] using
          SimpleGraph.Walk.length_eq_zero_iff.mp hprefixZero
      · simpa only [first, second] using
          SimpleGraph.Walk.length_eq_zero_iff.mp hsuffixZero
    exact profile.exists_localizedAlignedBubblePrimalCycle
      hprefixPath hsuffixPath first second horder hconsecutive hpositive

/-- The complete geometric normal form for a localized width-at-least-two
fusion profile. -/
inductive LocalizedFusionChainProfileResolution
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  | commonRunChain
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (chain : Nonempty (LocalizedAlignedCommonRunChain profile))
  | alignedBubbleCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (bubble : Nonempty (LocalizedAlignedBubblePrimalCycle profile))
  | strictlyShorterMixedPortCycles
      (descent : Nonempty
        (LocalizedStrictlyShorterMixedPortCycles pair oldCross face))
  | orderInversionPrimalCycle
      (descent : Nonempty
        (LocalizedOrderInversionPrimalCycle pair oldCross face))

/-- Resolve the aligned signed-profile branch into a contiguous common
run or a strict primal bubble cycle. -/
theorem LocalizedAlignedSharedEdgeProfile.nonempty_localizedFusionChainProfileResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
    (hprefixPath : pair.prefixTrail.IsPath)
    (hsuffixPath : pair.suffixTrail.IsPath) :
    Nonempty (LocalizedFusionChainProfileResolution pair oldCross face) := by
  rcases profile.exists_commonRunChain_or_bubbleCycle
      hprefixPath hsuffixPath with hchain | hbubble
  · exact ⟨LocalizedFusionChainProfileResolution.commonRunChain
      profile hchain⟩
  · exact ⟨LocalizedFusionChainProfileResolution.alignedBubbleCycle
      profile hbubble⟩

/-- Convert the prior three-way geometric normal form into the complete
fusion-chain resolution. -/
theorem RetainedIntersectionExactFaceCutPair.nonempty_localizedFusionChainProfileResolution_of_normalForm
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem)
    (hprefixPath : pair.prefixTrail.IsPath)
    (hsuffixPath : pair.suffixTrail.IsPath)
    (hresolved :
      Nonempty (LocalizedAlignedSharedEdgeProfile pair oldCross face) ∨
        Nonempty (LocalizedStrictlyShorterMixedPortCycles pair
          oldCross face) ∨
        Nonempty (LocalizedOrderInversionPrimalCycle pair
          oldCross face)) :
    Nonempty (LocalizedFusionChainProfileResolution pair oldCross face) := by
  rcases hresolved with haligned | hmixed | hinversion
  · rcases haligned with ⟨profile⟩
    exact profile.nonempty_localizedFusionChainProfileResolution
      hprefixPath hsuffixPath
  · exact ⟨
      LocalizedFusionChainProfileResolution.strictlyShorterMixedPortCycles
        hmixed⟩
  · exact ⟨
      LocalizedFusionChainProfileResolution.orderInversionPrimalCycle
        hinversion⟩

/-- A width-at-least-two successor profile together with its complete
localized fusion-chain resolution. -/
structure LocalizedSuccessorFusionChainProfile
    {graphData : Data G} {data : AdjacentPairData G}
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem)
    (prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3)) where
  pair : RetainedIntersectionExactFaceCutPair graphData data
  prefix_eq : pair.prefixTrail = prefixSuccessor
  suffix_eq : pair.suffixTrail = suffixSuccessor
  localized : ∀ edge ∈ pair.sharedEdges,
    edge ≠ oldCross ∧
      retainedEdgeToAmbientEdge data edge ∈
        orbitFaceBoundary graphData.toRotationSystem face
  width_le_face : pair.sharedEdges.card ≤
    (orbitFaceBoundary graphData.toRotationSystem face).card
  two_le_width : 2 ≤ pair.sharedEdges.card
  resolution : Nonempty
    (LocalizedFusionChainProfileResolution pair oldCross face)

/-- The remote successor profile has the final finite structural
trichotomy: disjoint paths, an exact same-face rebase, or a fully resolved
width-at-least-two fusion chain. -/
theorem CrossCentralExactFaceCutPair.exists_localizedSuccessorFusionChainTrichotomy
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
      Nonempty (LocalizedSuccessorFusionChainProfile cross face
        prefixSuccessor suffixSuccessor) := by
  rcases pair.exists_localizedSuccessorResolvedProfileTrichotomy minimal
      face firstFusion hfirstSupport secondFusion hsecondSupport
      prefixSuccessor hprefixAvoids hprefixCycle hprefixSubset
      suffixSuccessor hsuffixCycle hsuffixSubset with
    hdisjoint | hrebase |
      ⟨successorPair, hprefixEq, hsuffixEq, hlocalized, hwidth,
        htwo, hnormal⟩
  · exact Or.inl hdisjoint
  · exact Or.inr (Or.inl hrebase)
  · have hprefixPath : successorPair.prefixTrail.IsPath := by
      rw [hprefixEq]
      exact data.isPath_of_oppositePortClosure_isCycle prefixSuccessor
        hprefixCycle
    have hsuffixPath : successorPair.suffixTrail.IsPath := by
      rw [hsuffixEq]
      exact data.isPath_of_alternateOppositePortClosure_isCycle
        suffixSuccessor hsuffixCycle
    have hresolution :=
      successorPair.nonempty_localizedFusionChainProfileResolution_of_normalForm
        cross face hprefixPath hsuffixPath hnormal
    exact Or.inr (Or.inr ⟨{
      pair := successorPair
      prefix_eq := hprefixEq
      suffix_eq := hsuffixEq
      localized := hlocalized
      width_le_face := hwidth
      two_le_width := htwo
      resolution := hresolution }⟩)

/-- Both successor paths produced by the remote-face fusion pair, together
with their final finite structural outcome. -/
structure LocalizedFusionSuccessorResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (face : OrbitFace graphData.toRotationSystem)
    {firstRoot secondRoot : V}
    (firstFusion : G.Walk firstRoot firstRoot)
    (secondFusion : G.Walk secondRoot secondRoot) where
  prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)
  suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3)
  prefix_isPath : prefixSuccessor.IsPath
  prefix_avoids_cross : cross.1 ∉ prefixSuccessor.edges
  prefix_closure_isCycle :
    (data.oppositePortClosure prefixSuccessor).IsCycle
  prefix_ambient_edges_subset :
    (data.retainedWalkToAmbient prefixSuccessor).edges ⊆ firstFusion.edges
  suffix_isPath : suffixSuccessor.IsPath
  suffix_avoids_cross : cross.1 ∉ suffixSuccessor.edges
  suffix_closure_isCycle :
    (data.alternateOppositePortClosure suffixSuccessor).IsCycle
  suffix_ambient_edges_subset :
    (data.retainedWalkToAmbient suffixSuccessor).edges ⊆ secondFusion.edges
  finite_outcome :
    prefixSuccessor.edges.Disjoint suffixSuccessor.edges ∨
      (∃ (nextCross : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet)
          (nextPair : CrossCentralExactFaceCutPair graphData data nextCross),
        nextCross ≠ cross ∧
          retainedEdgeToAmbientEdge data nextCross ∈
            orbitFaceBoundary graphData.toRotationSystem face ∧
          nextPair.prefixTrail = prefixSuccessor ∧
          nextPair.suffixTrail = suffixSuccessor) ∨
      Nonempty (LocalizedSuccessorFusionChainProfile cross face
        prefixSuccessor suffixSuccessor)

/-- End-to-end remote-face fusion resolution: one fusion cycle already
lives in the retained graph, or the two retained successor paths carry the
complete disjoint/rebase/fusion-chain normal form. -/
theorem CrossCentralExactFaceCutPair.fusionCyclePair_retainedCycle_or_fusionChainResolution
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
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
    (∃ (hroot : firstRoot ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨firstRoot, hroot⟩ ⟨firstRoot, hroot⟩),
      retainedFusion.IsCycle ∧
        data.retainedWalkToAmbient retainedFusion = firstFusion) ∨
    (∃ (hroot : secondRoot ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨secondRoot, hroot⟩ ⟨secondRoot, hroot⟩),
      retainedFusion.IsCycle ∧
        data.retainedWalkToAmbient retainedFusion = secondFusion) ∨
    Nonempty (LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion) := by
  rcases pair.fusionCyclePair_retainedCycle_or_successorPair face hboundary
      firstFusion hfirstCycle hfirstCross hfirstSupport
      secondFusion hsecondCycle hsecondCross hsecondSupport with
    hfirstRetained | hsecondRetained |
      ⟨prefixSuccessor, suffixSuccessor,
        hprefixPath, hprefixAvoids, hprefixClosure, hprefixSubset,
        hsuffixPath, hsuffixAvoids, hsuffixClosure, hsuffixSubset, _⟩
  · exact Or.inl hfirstRetained
  · exact Or.inr (Or.inl hsecondRetained)
  · have houtcome := pair.exists_localizedSuccessorFusionChainTrichotomy
      minimal face firstFusion hfirstSupport secondFusion hsecondSupport
      prefixSuccessor hprefixAvoids hprefixClosure hprefixSubset
      suffixSuccessor hsuffixClosure hsuffixSubset
    exact Or.inr (Or.inr ⟨{
      prefixSuccessor := prefixSuccessor
      suffixSuccessor := suffixSuccessor
      prefix_isPath := hprefixPath
      prefix_avoids_cross := hprefixAvoids
      prefix_closure_isCycle := hprefixClosure
      prefix_ambient_edges_subset := hprefixSubset
      suffix_isPath := hsuffixPath
      suffix_avoids_cross := hsuffixAvoids
      suffix_closure_isCycle := hsuffixClosure
      suffix_ambient_edges_subset := hsuffixSubset
      finite_outcome := houtcome }⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
