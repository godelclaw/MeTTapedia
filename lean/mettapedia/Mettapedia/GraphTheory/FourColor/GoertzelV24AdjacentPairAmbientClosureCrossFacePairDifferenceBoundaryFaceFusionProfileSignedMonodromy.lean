import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileIntervals
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionSignedMonodromy
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureCycleReduction

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} {Graph : SimpleGraph Vertex}

/-- The oriented dart traversed at an exact position of a walk's edge
list. -/
def dartAtEdgePosition {left right : Vertex}
    (walk : Graph.Walk left right)
    (position : Fin walk.edges.length) : Graph.Dart :=
  walk.darts.get (Fin.cast (by simp) position)

/-- Forgetting the orientation of the position dart recovers the edge at
that exact list position. -/
@[simp] theorem dartAtEdgePosition_edge {left right : Vertex}
    (walk : Graph.Walk left right)
    (position : Fin walk.edges.length) :
    (walk.dartAtEdgePosition position).edge =
      walk.edges.get position := by
  simp [dartAtEdgePosition, SimpleGraph.Walk.edges]

/-- Equal selected walk edges have either equal position darts or reversed
position darts. -/
theorem dartAtEdgePosition_eq_or_eq_symm_of_edges_get_eq
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hedge : firstWalk.edges.get firstPosition =
      secondWalk.edges.get secondPosition) :
    firstWalk.dartAtEdgePosition firstPosition =
        secondWalk.dartAtEdgePosition secondPosition ∨
      firstWalk.dartAtEdgePosition firstPosition =
        (secondWalk.dartAtEdgePosition secondPosition).symm := by
  exact (SimpleGraph.dart_edge_eq_iff _ _).1 (by simpa using hedge)

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

/-- The prefix traversal orientation of a shared profile edge. -/
def RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart :=
  pair.prefixTrail.dartAtEdgePosition
    (pair.prefixSharedEdgePositionEmbedding position)

/-- The suffix traversal orientation of the same physical shared edge. -/
def RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDart
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart :=
  pair.suffixTrail.dartAtEdgePosition
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv position))

/-- Interpret a position on the common prefix-length carrier as the
corresponding numeric position in the suffix shared-edge order. -/
def RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDartOnCount
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart :=
  pair.suffixTrail.dartAtEdgePosition
    (pair.suffixSharedEdgePositionEmbedding
      (finCongr pair.sharedEdgeOrders_length_eq position))

/-- Applying order monodromy before interpreting a suffix-order position
selects the suffix occurrence of the original physical prefix edge. -/
theorem RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDartOnCount_sharedEdgeMonodromy
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    pair.suffixSharedEdgeDartOnCount
        (pair.sharedEdgeMonodromy position) =
      pair.suffixSharedEdgeDart position := by
  unfold RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDartOnCount
    RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDart
  congr 2

/-- The prefix-oriented dart lies over the physical edge selected by the
profile position. -/
@[simp] theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart_edge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (pair.prefixSharedEdgeDart position).edge =
      (pair.sharedEdgeAt position).1 := by
  calc
    (pair.prefixSharedEdgeDart position).edge =
        pair.prefixTrail.edges.get
          (pair.prefixSharedEdgePositionEmbedding position) := by
      simp [RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart]
    _ = pair.prefixSharedEdgeOrder.get position :=
      (pair.prefixSharedEdgePositionEmbedding_preserves_edge position).symm
    _ = (pair.sharedEdgeAt position).1 := rfl

/-- The suffix-oriented dart lies over that same physical edge. -/
@[simp] theorem RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDart_edge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (pair.suffixSharedEdgeDart position).edge =
      (pair.sharedEdgeAt position).1 := by
  calc
    (pair.suffixSharedEdgeDart position).edge =
        pair.suffixTrail.edges.get
          (pair.suffixSharedEdgePositionEmbedding
            (pair.sharedEdgeOrderEquiv position)) := by
      simp [RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDart]
    _ = pair.suffixSharedEdgeOrder.get
          (pair.sharedEdgeOrderEquiv position) :=
      (pair.suffixSharedEdgePositionEmbedding_preserves_edge _).symm
    _ = pair.prefixSharedEdgeOrder.get position :=
      pair.sharedEdgeOrderEquiv_preserves_edge position
    _ = (pair.sharedEdgeAt position).1 := rfl

/-- At every shared edge, the two route orientations agree or are exact
reversals. -/
theorem RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDart_eq_or_eq_prefix_symm
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    pair.suffixSharedEdgeDart position =
        pair.prefixSharedEdgeDart position ∨
      pair.suffixSharedEdgeDart position =
        (pair.prefixSharedEdgeDart position).symm := by
  apply (SimpleGraph.dart_edge_eq_iff _ _).1
  rw [pair.suffixSharedEdgeDart_edge, pair.prefixSharedEdgeDart_edge]

/-- The prefix traversal dart embedded back into the ambient graph. -/
def RetainedIntersectionExactFaceCutPair.ambientPrefixSharedEdgeDart
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) : G.Dart :=
  retainedDartToAmbientDart data (pair.prefixSharedEdgeDart position)

/-- The suffix traversal dart embedded back into the ambient graph. -/
def RetainedIntersectionExactFaceCutPair.ambientSuffixSharedEdgeDart
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) : G.Dart :=
  retainedDartToAmbientDart data (pair.suffixSharedEdgeDart position)

/-- The ambient prefix dart lies over the embedded physical profile edge. -/
@[simp] theorem RetainedIntersectionExactFaceCutPair.ambientPrefixSharedEdgeDart_edge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (pair.ambientPrefixSharedEdgeDart position).edge =
      retainedEdgeToAmbientEdge data (pair.sharedEdgeAt position) := by
  rw [RetainedIntersectionExactFaceCutPair.ambientPrefixSharedEdgeDart,
    retainedDartToAmbientDart_edge, retainedEdgeToAmbientEdge_val,
    pair.prefixSharedEdgeDart_edge]

/-- The ambient suffix dart lies over the same embedded profile edge. -/
@[simp] theorem RetainedIntersectionExactFaceCutPair.ambientSuffixSharedEdgeDart_edge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (pair.ambientSuffixSharedEdgeDart position).edge =
      retainedEdgeToAmbientEdge data (pair.sharedEdgeAt position) := by
  rw [RetainedIntersectionExactFaceCutPair.ambientSuffixSharedEdgeDart,
    retainedDartToAmbientDart_edge, retainedEdgeToAmbientEdge_val,
    pair.suffixSharedEdgeDart_edge]

/-- A reversed retained profile traversal remains exactly reversed after
embedding into the ambient graph. -/
theorem RetainedIntersectionExactFaceCutPair.ambientSuffixSharedEdgeDart_eq_ambientPrefix_symm_of_suffixSharedEdgeDart_eq_prefix_symm
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hreverse : pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm) :
    pair.ambientSuffixSharedEdgeDart position =
      (pair.ambientPrefixSharedEdgeDart position).symm := by
  simp only [RetainedIntersectionExactFaceCutPair.ambientSuffixSharedEdgeDart,
    RetainedIntersectionExactFaceCutPair.ambientPrefixSharedEdgeDart,
    hreverse, retainedDartToAmbientDart_symm]

/-- The local sign of a profile edge is positive precisely when the two
trails traverse it in the same direction. -/
def RetainedIntersectionExactFaceCutPair.sharedEdgeChirality
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) : Bool :=
  if pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position then true else false

@[simp] theorem RetainedIntersectionExactFaceCutPair.sharedEdgeChirality_eq_true_iff
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    pair.sharedEdgeChirality position = true ↔
      pair.suffixSharedEdgeDart position =
        pair.prefixSharedEdgeDart position := by
  simp [RetainedIntersectionExactFaceCutPair.sharedEdgeChirality]

@[simp] theorem RetainedIntersectionExactFaceCutPair.sharedEdgeChirality_eq_false_iff
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    pair.sharedEdgeChirality position = false ↔
      pair.suffixSharedEdgeDart position =
        (pair.prefixSharedEdgeDart position).symm := by
  constructor
  · intro hnegative
    have hne : pair.suffixSharedEdgeDart position ≠
        pair.prefixSharedEdgeDart position := by
      intro heq
      have hpositive :=
        (pair.sharedEdgeChirality_eq_true_iff position).2 heq
      rw [hnegative] at hpositive
      contradiction
    rcases pair.suffixSharedEdgeDart_eq_or_eq_prefix_symm position with
      hsame | hreverse
    · exact False.elim (hne hsame)
    · exact hreverse
  · intro hreverse
    have hne : pair.suffixSharedEdgeDart position ≠
        pair.prefixSharedEdgeDart position := by
      intro heq
      exact SimpleGraph.Dart.symm_ne _ (hreverse.symm.trans heq)
    unfold RetainedIntersectionExactFaceCutPair.sharedEdgeChirality
    rw [if_neg hne]

/-- The signed profile monodromy transports both a shared-edge rank and
one of the two oriented endpoints of that physical edge. -/
def RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    Equiv.Perm (Fin pair.prefixSharedEdgeOrder.length × Bool) :=
  signedIndexPermutation pair.sharedEdgeMonodromy
    pair.sharedEdgeChirality

@[simp] theorem RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy_apply_fst
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (state : Fin pair.prefixSharedEdgeOrder.length × Bool) :
    (pair.sharedEdgeSignedMonodromy state).1 =
      pair.sharedEdgeMonodromy state.1 :=
  rfl

@[simp] theorem RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy_apply_snd
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (state : Fin pair.prefixSharedEdgeOrder.length × Bool) :
    (pair.sharedEdgeSignedMonodromy state).2 =
      fusionEndpointTransport (pair.sharedEdgeChirality state.1) state.2 :=
  rfl

/-- Signed profile monodromy is trivial exactly when the route order is
unchanged and every common edge is traversed in the same direction. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy_eq_refl_iff
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.sharedEdgeSignedMonodromy =
        Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) ↔
      pair.sharedEdgeMonodromy =
          Equiv.refl (Fin pair.prefixSharedEdgeOrder.length) ∧
        ∀ position, pair.sharedEdgeChirality position = true :=
  signedIndexPermutation_eq_refl_iff _ _

/-- A nonidentity route-order permutation is already a nonidentity signed
profile permutation. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy_ne_refl_of_sharedEdgeMonodromy_ne_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hmonodromy : pair.sharedEdgeMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length)) :
    pair.sharedEdgeSignedMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) := by
  intro hsigned
  exact hmonodromy
    ((pair.sharedEdgeSignedMonodromy_eq_refl_iff).1 hsigned).1

/-- One oppositely traversed shared edge is already a nonidentity signed
profile witness. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy_ne_refl_of_sharedEdgeChirality_eq_false
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hchirality : pair.sharedEdgeChirality position = false) :
    pair.sharedEdgeSignedMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) := by
  intro hsigned
  have hpositive :=
    ((pair.sharedEdgeSignedMonodromy_eq_refl_iff).1 hsigned).2 position
  rw [hchirality] at hpositive
  contradiction

/-- Every nontrivial signed profile is witnessed either by an inversion
of two shared-edge ranks or by one shared edge traversed in the reverse
direction. -/
theorem RetainedIntersectionExactFaceCutPair.exists_orderInversion_or_reversedSharedEdgeDart_of_sharedEdgeSignedMonodromy_ne_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hsigned : pair.sharedEdgeSignedMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool)) :
    (∃ first second : Fin pair.prefixSharedEdgeOrder.length,
        first < second ∧
          pair.sharedEdgeMonodromy second <
            pair.sharedEdgeMonodromy first) ∨
      ∃ position : Fin pair.prefixSharedEdgeOrder.length,
        pair.suffixSharedEdgeDart position =
          (pair.prefixSharedEdgeDart position).symm := by
  by_cases hmonodromy : pair.sharedEdgeMonodromy =
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length)
  · right
    by_contra hnoReverse
    apply hsigned
    apply pair.sharedEdgeSignedMonodromy_eq_refl_iff.2
    refine ⟨hmonodromy, ?_⟩
    intro position
    cases hchirality : pair.sharedEdgeChirality position with
    | false =>
        exfalso
        apply hnoReverse
        exact ⟨position,
          (pair.sharedEdgeChirality_eq_false_iff position).1 hchirality⟩
    | true => rfl
  · left
    exact pair.exists_sharedEdgeOrderInversion_of_monodromy_ne_refl
      hmonodromy

/-- The preceding obstruction alternative is exact: either kind of
witness forces nontrivial signed profile monodromy. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy_ne_refl_iff_exists_orderInversion_or_reversedSharedEdgeDart
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.sharedEdgeSignedMonodromy ≠
        Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) ↔
      (∃ first second : Fin pair.prefixSharedEdgeOrder.length,
          first < second ∧
            pair.sharedEdgeMonodromy second <
              pair.sharedEdgeMonodromy first) ∨
        ∃ position : Fin pair.prefixSharedEdgeOrder.length,
          pair.suffixSharedEdgeDart position =
            (pair.prefixSharedEdgeDart position).symm := by
  constructor
  · exact pair.exists_orderInversion_or_reversedSharedEdgeDart_of_sharedEdgeSignedMonodromy_ne_refl
  · rintro (horder | horientation)
    · rcases horder with ⟨first, second, hfirstSecond, hreverse⟩
      apply pair.sharedEdgeSignedMonodromy_ne_refl_of_sharedEdgeMonodromy_ne_refl
      intro hmonodromy
      rw [hmonodromy] at hreverse
      exact (not_lt_of_ge hfirstSecond.le) hreverse
    · rcases horientation with ⟨position, hreverse⟩
      apply pair.sharedEdgeSignedMonodromy_ne_refl_of_sharedEdgeChirality_eq_false
        position
      exact (pair.sharedEdgeChirality_eq_false_iff position).2 hreverse

/-- A localized order obstruction consists of two distinct new face edges
and the two actual path intervals that meet them in opposite orders. -/
structure LocalizedSharedEdgePathIntervalInversion
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  first : Fin pair.prefixSharedEdgeOrder.length
  second : Fin pair.prefixSharedEdgeOrder.length
  first_lt_second : first < second
  suffix_order_reversed :
    pair.sharedEdgeOrderEquiv second < pair.sharedEdgeOrderEquiv first
  prefix_interval_isPath :
    (pair.prefixSharedEdgeInterval first second
      first_lt_second.le).IsPath
  suffix_interval_isPath :
    (pair.suffixReversedSharedEdgeInterval first second
      suffix_order_reversed.le).IsPath
  two_le_prefix_interval_length :
    2 ≤ (pair.prefixSharedEdgeInterval first second
      first_lt_second.le).length
  two_le_suffix_interval_length :
    2 ≤ (pair.suffixReversedSharedEdgeInterval first second
      suffix_order_reversed.le).length
  first_edge_ne_second_edge :
    pair.sharedEdgeAt first ≠ pair.sharedEdgeAt second
  first_edge_ne_oldCross : pair.sharedEdgeAt first ≠ oldCross
  second_edge_ne_oldCross : pair.sharedEdgeAt second ≠ oldCross
  first_ambient_edge_mem_face :
    retainedEdgeToAmbientEdge data (pair.sharedEdgeAt first) ∈
      orbitFaceBoundary graphData.toRotationSystem face
  second_ambient_edge_mem_face :
    retainedEdgeToAmbientEdge data (pair.sharedEdgeAt second) ∈
      orbitFaceBoundary graphData.toRotationSystem face

/-- A localized sign obstruction is one new face edge whose two route
occurrences have exactly opposite retained and ambient orientations. -/
structure LocalizedReversedSharedEdgeDart
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  position : Fin pair.prefixSharedEdgeOrder.length
  retained_reversed :
    pair.suffixSharedEdgeDart position =
      (pair.prefixSharedEdgeDart position).symm
  ambient_reversed :
    pair.ambientSuffixSharedEdgeDart position =
      (pair.ambientPrefixSharedEdgeDart position).symm
  edge_ne_oldCross : pair.sharedEdgeAt position ≠ oldCross
  ambient_edge_mem_face :
    retainedEdgeToAmbientEdge data (pair.sharedEdgeAt position) ∈
      orbitFaceBoundary graphData.toRotationSystem face

/-- On a profile localized to one ambient face, nontrivial signed
monodromy produces either oppositely ordered path intervals or one
oppositely oriented shared dart, always away from the old cross. -/
theorem RetainedIntersectionExactFaceCutPair.exists_localizedPathIntervalInversion_or_reversedSharedEdgeDart_of_sharedEdgeSignedMonodromy_ne_refl
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
          orbitFaceBoundary graphData.toRotationSystem face)
    (hsigned : pair.sharedEdgeSignedMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool)) :
    Nonempty (LocalizedSharedEdgePathIntervalInversion pair oldCross face) ∨
      Nonempty (LocalizedReversedSharedEdgeDart pair oldCross face) := by
  rcases pair.exists_orderInversion_or_reversedSharedEdgeDart_of_sharedEdgeSignedMonodromy_ne_refl
      hsigned with horder | horientation
  · rcases horder with ⟨first, second, hfirstSecond, hreverse⟩
    have hreverse' : pair.sharedEdgeOrderEquiv second <
        pair.sharedEdgeOrderEquiv first := by
      change (pair.sharedEdgeMonodromy second : Nat) <
        (pair.sharedEdgeMonodromy first : Nat) at hreverse
      rw [pair.sharedEdgeMonodromy_apply_val second,
        pair.sharedEdgeMonodromy_apply_val first] at hreverse
      exact hreverse
    have hfirstLocalized := hlocalized (pair.sharedEdgeAt first)
      (pair.sharedEdgeAt_mem_sharedEdges first)
    have hsecondLocalized := hlocalized (pair.sharedEdgeAt second)
      (pair.sharedEdgeAt_mem_sharedEdges second)
    left
    exact ⟨{
      first := first
      second := second
      first_lt_second := hfirstSecond
      suffix_order_reversed := hreverse'
      prefix_interval_isPath :=
        pair.prefixSharedEdgeInterval_isPath hprefixPath first second
          hfirstSecond.le
      suffix_interval_isPath :=
        pair.suffixReversedSharedEdgeInterval_isPath hsuffixPath first second
          hreverse'.le
      two_le_prefix_interval_length :=
        pair.two_le_prefixSharedEdgeInterval_length first second hfirstSecond
      two_le_suffix_interval_length :=
        pair.two_le_suffixReversedSharedEdgeInterval_length first second
          hreverse'
      first_edge_ne_second_edge :=
        pair.sharedEdgeAt_injective.ne hfirstSecond.ne
      first_edge_ne_oldCross := hfirstLocalized.1
      second_edge_ne_oldCross := hsecondLocalized.1
      first_ambient_edge_mem_face := hfirstLocalized.2
      second_ambient_edge_mem_face := hsecondLocalized.2 }⟩
  · rcases horientation with ⟨position, hreverse⟩
    have hlocalizedPosition := hlocalized (pair.sharedEdgeAt position)
      (pair.sharedEdgeAt_mem_sharedEdges position)
    right
    exact ⟨{
      position := position
      retained_reversed := hreverse
      ambient_reversed :=
        pair.ambientSuffixSharedEdgeDart_eq_ambientPrefix_symm_of_suffixSharedEdgeDart_eq_prefix_symm
          position hreverse
      edge_ne_oldCross := hlocalizedPosition.1
      ambient_edge_mem_face := hlocalizedPosition.2 }⟩

/-- The localized signed profile has an unconditional three-way normal
form: trivial signed transport, an order-inverting pair of path intervals,
or one reversed shared dart. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy_eq_refl_or_exists_localizedPathIntervalInversion_or_reversedSharedEdgeDart
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
      Nonempty (LocalizedReversedSharedEdgeDart pair oldCross face) := by
  by_cases hsigned : pair.sharedEdgeSignedMonodromy =
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool)
  · exact Or.inl hsigned
  · exact Or.inr
      (pair.exists_localizedPathIntervalInversion_or_reversedSharedEdgeDart_of_sharedEdgeSignedMonodromy_ne_refl
        hprefixPath hsuffixPath oldCross face hlocalized hsigned)

/-- A remote-face fusion therefore yields a finite localized successor
profile together with its complete signed normal form. -/
theorem CrossCentralExactFaceCutPair.exists_localizedSuccessorSignedProfileNormalForm
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
    ∃ successorPair : RetainedIntersectionExactFaceCutPair graphData data,
      successorPair.prefixTrail = prefixSuccessor ∧
        successorPair.suffixTrail = suffixSuccessor ∧
        (∀ edge ∈ successorPair.sharedEdges,
          edge ≠ cross ∧
            retainedEdgeToAmbientEdge data edge ∈
              orbitFaceBoundary graphData.toRotationSystem face) ∧
        successorPair.sharedEdges.card ≤
          (orbitFaceBoundary graphData.toRotationSystem face).card ∧
        (successorPair.sharedEdgeSignedMonodromy =
            Equiv.refl
              (Fin successorPair.prefixSharedEdgeOrder.length × Bool) ∨
          Nonempty (LocalizedSharedEdgePathIntervalInversion successorPair
            cross face) ∨
          Nonempty (LocalizedReversedSharedEdgeDart successorPair
            cross face)) := by
  rcases pair.exists_localizedSuccessorIntersectionProfile minimal face
      firstFusion hfirstSupport secondFusion hsecondSupport prefixSuccessor
      hprefixAvoids hprefixCycle hprefixSubset suffixSuccessor hsuffixCycle
      hsuffixSubset with
    ⟨successorPair, hprefixEq, hsuffixEq, hlocalized, hwidth⟩
  have hprefixPath : successorPair.prefixTrail.IsPath := by
    rw [hprefixEq]
    exact data.isPath_of_oppositePortClosure_isCycle prefixSuccessor
      hprefixCycle
  have hsuffixPath : successorPair.suffixTrail.IsPath := by
    rw [hsuffixEq]
    exact data.isPath_of_alternateOppositePortClosure_isCycle suffixSuccessor
      hsuffixCycle
  exact ⟨successorPair, hprefixEq, hsuffixEq, hlocalized, hwidth,
    successorPair.sharedEdgeSignedMonodromy_eq_refl_or_exists_localizedPathIntervalInversion_or_reversedSharedEdgeDart
      hprefixPath hsuffixPath cross face hlocalized⟩

/-- Endpoint transport converts the suffix traversal at a shared edge
back to the same based dart of the prefix traversal. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy_preserves_endpointDart
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (state : Fin pair.prefixSharedEdgeOrder.length × Bool) :
    fusionEndpointDart
        (pair.suffixSharedEdgeDartOnCount
          (pair.sharedEdgeSignedMonodromy state).1)
        (pair.sharedEdgeSignedMonodromy state).2 =
      fusionEndpointDart (pair.prefixSharedEdgeDart state.1) state.2 := by
  rw [pair.sharedEdgeSignedMonodromy_apply_fst,
    pair.suffixSharedEdgeDartOnCount_sharedEdgeMonodromy]
  cases hchirality : pair.sharedEdgeChirality state.1 with
  | false =>
      rw [pair.sharedEdgeSignedMonodromy_apply_snd,
        hchirality, fusionEndpointTransport_false,
        (pair.sharedEdgeChirality_eq_false_iff state.1).1 hchirality]
      exact fusionEndpointDart_symm_not _ _
  | true =>
      rw [pair.sharedEdgeSignedMonodromy_apply_snd,
        hchirality, fusionEndpointTransport_true,
        (pair.sharedEdgeChirality_eq_true_iff state.1).1 hchirality]

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
