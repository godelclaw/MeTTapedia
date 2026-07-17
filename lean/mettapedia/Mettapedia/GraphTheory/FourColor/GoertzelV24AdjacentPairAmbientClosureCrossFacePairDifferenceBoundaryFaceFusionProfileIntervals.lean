import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileMonodromy

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} {Graph : SimpleGraph Vertex}

/-- The contiguous subwalk containing every edge from `first` through
`second`, inclusive. -/
def edgeInterval {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first ≤ second) :
    Graph.Walk (walk.getVert first.val) (walk.getVert (second.val + 1)) :=
  ((walk.drop first.val).take (second.val - first.val + 1)).copy rfl (by
    rw [drop_getVert]
    congr 1
    omega)

@[simp] theorem edgeInterval_length {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first ≤ second) :
    (walk.edgeInterval first second horder).length =
      second.val - first.val + 1 := by
  simp only [edgeInterval, length_copy, take_length, drop_length]
  apply Nat.min_eq_left
  have hsecond := second.isLt
  have hlength := walk.length_edges
  omega

@[simp] theorem edgeInterval_edges {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first ≤ second) :
    (walk.edgeInterval first second horder).edges =
      (walk.edges.drop first.val).take
        (second.val - first.val + 1) := by
  simp [edgeInterval, edges_take, edges_drop]

theorem edgeInterval_isSubwalk {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first ≤ second) :
    (walk.edgeInterval first second horder).IsSubwalk walk := by
  unfold edgeInterval
  exact ((((walk.drop first.val).isSubwalk_take
    (second.val - first.val + 1)).trans
      (walk.isSubwalk_drop first.val)).copy _ _ rfl rfl)

theorem IsTrail.edgeInterval {left right : Vertex}
    {walk : Graph.Walk left right} (htrail : walk.IsTrail)
    (first second : Fin walk.edges.length) (horder : first ≤ second) :
    (walk.edgeInterval first second horder).IsTrail :=
  isTrail_of_isSubwalk (walk.edgeInterval_isSubwalk first second horder)
    htrail

theorem IsPath.edgeInterval {left right : Vertex}
    {walk : Graph.Walk left right} (hpath : walk.IsPath)
    (first second : Fin walk.edges.length) (horder : first ≤ second) :
    (walk.edgeInterval first second horder).IsPath :=
  isPath_of_isSubwalk (walk.edgeInterval_isSubwalk first second horder)
    hpath

/-- The first edge of an edge interval is the selected first edge of the
original walk. -/
theorem edgeInterval_firstEdge {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first ≤ second) :
    (walk.edgeInterval first second horder).edges[0]'(by
        simpa only [length_edges, edgeInterval_length] using
          Nat.zero_lt_succ (second.val - first.val)) =
      walk.edges[first.val]'first.isLt := by
  simp only [edgeInterval_edges, List.getElem_take, List.getElem_drop,
    Nat.add_zero]

/-- The last edge of an edge interval is the selected second edge of the
original walk. -/
theorem edgeInterval_lastEdge {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first ≤ second) :
    (walk.edgeInterval first second horder).edges[second.val - first.val]'(by
        simpa only [length_edges, edgeInterval_length] using
          Nat.lt_succ_self (second.val - first.val)) =
      walk.edges[second.val]'second.isLt := by
  simp only [edgeInterval_edges, List.getElem_take, List.getElem_drop]
  congr 1
  omega

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
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

/-- Filtering to shared edges preserves their order as a sublist of the
prefix trail's complete edge list. -/
theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgeOrder_sublist
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.prefixSharedEdgeOrder.Sublist pair.prefixTrail.edges := by
  exact List.filter_sublist

/-- The suffix-ordered shared edges are likewise a sublist of the complete
suffix edge list. -/
theorem RetainedIntersectionExactFaceCutPair.suffixSharedEdgeOrder_sublist
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.suffixSharedEdgeOrder.Sublist pair.suffixTrail.edges := by
  exact List.filter_sublist

/-- Canonical order embedding of prefix shared-edge positions into exact
positions of the complete prefix edge list. -/
def RetainedIntersectionExactFaceCutPair.prefixSharedEdgePositionEmbedding
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    Fin pair.prefixSharedEdgeOrder.length ↪o
      Fin pair.prefixTrail.edges.length :=
  Classical.choose
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      pair.prefixSharedEdgeOrder_sublist)

/-- The prefix position embedding selects the same retained edge. -/
theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgePositionEmbedding_preserves_edge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    pair.prefixSharedEdgeOrder.get position =
      pair.prefixTrail.edges.get
        (pair.prefixSharedEdgePositionEmbedding position) :=
  Classical.choose_spec
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      pair.prefixSharedEdgeOrder_sublist) position

/-- Canonical order embedding of suffix shared-edge positions into exact
positions of the complete suffix edge list. -/
def RetainedIntersectionExactFaceCutPair.suffixSharedEdgePositionEmbedding
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    Fin pair.suffixSharedEdgeOrder.length ↪o
      Fin pair.suffixTrail.edges.length :=
  Classical.choose
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      pair.suffixSharedEdgeOrder_sublist)

/-- The suffix position embedding also selects the same retained edge. -/
theorem RetainedIntersectionExactFaceCutPair.suffixSharedEdgePositionEmbedding_preserves_edge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.suffixSharedEdgeOrder.length) :
    pair.suffixSharedEdgeOrder.get position =
      pair.suffixTrail.edges.get
        (pair.suffixSharedEdgePositionEmbedding position) :=
  Classical.choose_spec
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      pair.suffixSharedEdgeOrder_sublist) position

/-- Corresponding route-order positions name the same physical retained
edge at their exact positions in the complete trail edge lists. -/
theorem RetainedIntersectionExactFaceCutPair.trailEdges_get_sharedPositions_eq
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    pair.prefixTrail.edges.get
        (pair.prefixSharedEdgePositionEmbedding position) =
      pair.suffixTrail.edges.get
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv position)) := by
  calc
    pair.prefixTrail.edges.get
          (pair.prefixSharedEdgePositionEmbedding position) =
        pair.prefixSharedEdgeOrder.get position :=
      (pair.prefixSharedEdgePositionEmbedding_preserves_edge position).symm
    _ = pair.suffixSharedEdgeOrder.get
          (pair.sharedEdgeOrderEquiv position) :=
      (pair.sharedEdgeOrderEquiv_preserves_edge position).symm
    _ = pair.suffixTrail.edges.get
          (pair.suffixSharedEdgePositionEmbedding
            (pair.sharedEdgeOrderEquiv position)) :=
      pair.suffixSharedEdgePositionEmbedding_preserves_edge _

/-- A nonidentity profile monodromy yields two exact edge positions that
increase in the prefix trail and decrease in the suffix trail. -/
theorem RetainedIntersectionExactFaceCutPair.exists_trailEdgePositionInversion_of_monodromy_ne_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hmonodromy : pair.sharedEdgeMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length)) :
    ∃ first second : Fin pair.prefixSharedEdgeOrder.length,
      pair.prefixSharedEdgePositionEmbedding first <
          pair.prefixSharedEdgePositionEmbedding second ∧
        pair.suffixSharedEdgePositionEmbedding
            (pair.sharedEdgeOrderEquiv second) <
          pair.suffixSharedEdgePositionEmbedding
            (pair.sharedEdgeOrderEquiv first) ∧
        pair.prefixTrail.edges.get
            (pair.prefixSharedEdgePositionEmbedding first) =
          pair.suffixTrail.edges.get
            (pair.suffixSharedEdgePositionEmbedding
              (pair.sharedEdgeOrderEquiv first)) ∧
        pair.prefixTrail.edges.get
            (pair.prefixSharedEdgePositionEmbedding second) =
          pair.suffixTrail.edges.get
            (pair.suffixSharedEdgePositionEmbedding
              (pair.sharedEdgeOrderEquiv second)) ∧
        pair.prefixTrail.edges.get
            (pair.prefixSharedEdgePositionEmbedding first) ≠
          pair.prefixTrail.edges.get
            (pair.prefixSharedEdgePositionEmbedding second) := by
  rcases pair.exists_physicalSharedEdgeOrderInversion_of_monodromy_ne_refl
      hmonodromy with
    ⟨first, second, hfirstSecond, hreverse,
      _hfirstPhysical, _hsecondPhysical, hedgesNe⟩
  refine ⟨first, second,
    (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2 hfirstSecond,
    (pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2 hreverse,
    pair.trailEdges_get_sharedPositions_eq first,
    pair.trailEdges_get_sharedPositions_eq second, ?_⟩
  intro hedge
  apply hedgesNe
  calc
    pair.prefixSharedEdgeOrder.get first =
        pair.prefixTrail.edges.get
          (pair.prefixSharedEdgePositionEmbedding first) :=
      pair.prefixSharedEdgePositionEmbedding_preserves_edge first
    _ = pair.prefixTrail.edges.get
          (pair.prefixSharedEdgePositionEmbedding second) := hedge
    _ = pair.prefixSharedEdgeOrder.get second :=
      (pair.prefixSharedEdgePositionEmbedding_preserves_edge second).symm

/-- In the identity-monodromy branch, equal ranks in the two filtered
orders select the same physical edge at their exact trail positions. -/
theorem RetainedIntersectionExactFaceCutPair.trailEdges_get_sameRank_eq_of_monodromy_eq_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hmonodromy : pair.sharedEdgeMonodromy =
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length))
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    ∃ suffixPosition : Fin pair.suffixSharedEdgeOrder.length,
      (suffixPosition : Nat) = position ∧
        pair.prefixTrail.edges.get
            (pair.prefixSharedEdgePositionEmbedding position) =
          pair.suffixTrail.edges.get
            (pair.suffixSharedEdgePositionEmbedding suffixPosition) := by
  let suffixPosition := pair.sharedEdgeOrderEquiv position
  have hvalue : (suffixPosition : Nat) = position := by
    have himage : pair.sharedEdgeMonodromy position = position := by
      rw [hmonodromy]
      rfl
    have hmonoValue : (pair.sharedEdgeMonodromy position : Nat) = position := by
      exact congrArg Fin.val himage
    rw [pair.sharedEdgeMonodromy_apply_val position] at hmonoValue
    exact hmonoValue
  exact ⟨suffixPosition, hvalue,
    pair.trailEdges_get_sharedPositions_eq position⟩

/-- The actual prefix-trail interval running from one shared-profile edge
to a later one.  It retains every intervening, possibly nonshared, edge. -/
def RetainedIntersectionExactFaceCutPair.prefixSharedEdgeInterval
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first ≤ second) :=
  pair.prefixTrail.edgeInterval
    (pair.prefixSharedEdgePositionEmbedding first)
    (pair.prefixSharedEdgePositionEmbedding second)
    ((pair.prefixSharedEdgePositionEmbedding.le_iff_le).2 horder)

/-- The suffix-trail interval through the same two physical shared edges,
written in suffix traversal order. -/
def RetainedIntersectionExactFaceCutPair.suffixReversedSharedEdgeInterval
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.sharedEdgeOrderEquiv second ≤
      pair.sharedEdgeOrderEquiv first) :=
  pair.suffixTrail.edgeInterval
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv second))
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv first))
    ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2 hreverse)

@[simp] theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgeInterval_length
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first ≤ second) :
    (pair.prefixSharedEdgeInterval first second horder).length =
      (pair.prefixSharedEdgePositionEmbedding second).val -
        (pair.prefixSharedEdgePositionEmbedding first).val + 1 := by
  simp [RetainedIntersectionExactFaceCutPair.prefixSharedEdgeInterval]

@[simp] theorem RetainedIntersectionExactFaceCutPair.suffixReversedSharedEdgeInterval_length
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.sharedEdgeOrderEquiv second ≤
      pair.sharedEdgeOrderEquiv first) :
    (pair.suffixReversedSharedEdgeInterval first second hreverse).length =
      (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv first)).val -
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv second)).val + 1 := by
  simp [RetainedIntersectionExactFaceCutPair.suffixReversedSharedEdgeInterval]

/-- Every prefix shared-edge interval remains a trail. -/
theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgeInterval_isTrail
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first ≤ second) :
    (pair.prefixSharedEdgeInterval first second horder).IsTrail := by
  exact pair.prefixRetained_isTrail.edgeInterval _ _
    ((pair.prefixSharedEdgePositionEmbedding.le_iff_le).2 horder)

/-- Every reversed suffix shared-edge interval remains a trail. -/
theorem RetainedIntersectionExactFaceCutPair.suffixReversedSharedEdgeInterval_isTrail
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.sharedEdgeOrderEquiv second ≤
      pair.sharedEdgeOrderEquiv first) :
    (pair.suffixReversedSharedEdgeInterval first second hreverse).IsTrail := by
  exact pair.suffixRetained_isTrail.edgeInterval _ _
    ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2 hreverse)

/-- A prefix interval of a path is itself a path. -/
theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgeInterval_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hpath : pair.prefixTrail.IsPath)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first ≤ second) :
    (pair.prefixSharedEdgeInterval first second horder).IsPath := by
  exact hpath.edgeInterval _ _
    ((pair.prefixSharedEdgePositionEmbedding.le_iff_le).2 horder)

/-- A reversed suffix interval of a path is itself a path. -/
theorem RetainedIntersectionExactFaceCutPair.suffixReversedSharedEdgeInterval_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hpath : pair.suffixTrail.IsPath)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.sharedEdgeOrderEquiv second ≤
      pair.sharedEdgeOrderEquiv first) :
    (pair.suffixReversedSharedEdgeInterval first second hreverse).IsPath := by
  exact hpath.edgeInterval _ _
    ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2 hreverse)

/-- Two distinct shared-profile positions determine a prefix interval with
at least two edges. -/
theorem RetainedIntersectionExactFaceCutPair.two_le_prefixSharedEdgeInterval_length
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (horder : first < second) :
    2 ≤ (pair.prefixSharedEdgeInterval first second horder.le).length := by
  rw [pair.prefixSharedEdgeInterval_length]
  have hpositions :=
    (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2 horder
  omega

/-- Oppositely ordered shared-profile positions determine a suffix interval
with at least two edges. -/
theorem RetainedIntersectionExactFaceCutPair.two_le_suffixReversedSharedEdgeInterval_length
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (first second : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.sharedEdgeOrderEquiv second <
      pair.sharedEdgeOrderEquiv first) :
    2 ≤
      (pair.suffixReversedSharedEdgeInterval first second hreverse.le).length := by
  rw [pair.suffixReversedSharedEdgeInterval_length]
  have hpositions :=
    (pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2 hreverse
  omega

/-- Nonidentity profile monodromy produces two genuine trail intervals,
each containing the same two distinct physical boundary edges in opposite
route orders. -/
theorem RetainedIntersectionExactFaceCutPair.exists_oppositelyOrderedSharedEdgeTrailIntervals_of_monodromy_ne_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hmonodromy : pair.sharedEdgeMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length)) :
    ∃ first second : Fin pair.prefixSharedEdgeOrder.length,
      ∃ hfirstSecond : first < second,
        ∃ hreverse : pair.sharedEdgeOrderEquiv second <
            pair.sharedEdgeOrderEquiv first,
          (pair.prefixSharedEdgeInterval first second
              hfirstSecond.le).IsTrail ∧
            (pair.suffixReversedSharedEdgeInterval first second
              hreverse.le).IsTrail ∧
            2 ≤ (pair.prefixSharedEdgeInterval first second
              hfirstSecond.le).length ∧
            2 ≤ (pair.suffixReversedSharedEdgeInterval first second
              hreverse.le).length ∧
            pair.prefixTrail.edges.get
                (pair.prefixSharedEdgePositionEmbedding first) =
              pair.suffixTrail.edges.get
                (pair.suffixSharedEdgePositionEmbedding
                  (pair.sharedEdgeOrderEquiv first)) ∧
            pair.prefixTrail.edges.get
                (pair.prefixSharedEdgePositionEmbedding second) =
              pair.suffixTrail.edges.get
                (pair.suffixSharedEdgePositionEmbedding
                  (pair.sharedEdgeOrderEquiv second)) ∧
            pair.prefixTrail.edges.get
                (pair.prefixSharedEdgePositionEmbedding first) ≠
              pair.prefixTrail.edges.get
                (pair.prefixSharedEdgePositionEmbedding second) := by
  rcases pair.exists_trailEdgePositionInversion_of_monodromy_ne_refl
      hmonodromy with
    ⟨first, second, hprefixPositions, hsuffixPositions,
      hfirstPhysical, hsecondPhysical, hedgesNe⟩
  have hfirstSecond : first < second :=
    (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).1 hprefixPositions
  have hreverse : pair.sharedEdgeOrderEquiv second <
      pair.sharedEdgeOrderEquiv first :=
    (pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).1 hsuffixPositions
  exact ⟨first, second, hfirstSecond, hreverse,
    pair.prefixSharedEdgeInterval_isTrail first second hfirstSecond.le,
    pair.suffixReversedSharedEdgeInterval_isTrail first second hreverse.le,
    pair.two_le_prefixSharedEdgeInterval_length first second hfirstSecond,
    pair.two_le_suffixReversedSharedEdgeInterval_length first second hreverse,
    hfirstPhysical, hsecondPhysical, hedgesNe⟩

/-- If both retained routes are paths, the monodromy witness consists of
two genuine path intervals with reversed boundary-edge order. -/
theorem RetainedIntersectionExactFaceCutPair.exists_oppositelyOrderedSharedEdgePathIntervals_of_monodromy_ne_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hprefixPath : pair.prefixTrail.IsPath)
    (hsuffixPath : pair.suffixTrail.IsPath)
    (hmonodromy : pair.sharedEdgeMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length)) :
    ∃ first second : Fin pair.prefixSharedEdgeOrder.length,
      ∃ hfirstSecond : first < second,
        ∃ hreverse : pair.sharedEdgeOrderEquiv second <
            pair.sharedEdgeOrderEquiv first,
          (pair.prefixSharedEdgeInterval first second
              hfirstSecond.le).IsPath ∧
            (pair.suffixReversedSharedEdgeInterval first second
              hreverse.le).IsPath ∧
            2 ≤ (pair.prefixSharedEdgeInterval first second
              hfirstSecond.le).length ∧
            2 ≤ (pair.suffixReversedSharedEdgeInterval first second
              hreverse.le).length := by
  rcases pair.exists_physicalSharedEdgeOrderInversion_of_monodromy_ne_refl
      hmonodromy with
    ⟨first, second, hfirstSecond, hreverse,
      _hfirstPhysical, _hsecondPhysical, _hedgesNe⟩
  exact ⟨first, second, hfirstSecond, hreverse,
    pair.prefixSharedEdgeInterval_isPath hprefixPath first second
      hfirstSecond.le,
    pair.suffixReversedSharedEdgeInterval_isPath hsuffixPath first second
      hreverse.le,
    pair.two_le_prefixSharedEdgeInterval_length first second hfirstSecond,
    pair.two_le_suffixReversedSharedEdgeInterval_length first second hreverse⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
