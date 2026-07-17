import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfile

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

/-- Exactness of the closed prefix trail implies that its retained part is
itself a trail. -/
theorem RetainedIntersectionExactFaceCutPair.prefixRetained_isTrail
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.prefixTrail.IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def]
  have hclosure := pair.prefixTrail_isTrail.edges_nodup
  change (((data.retainedWalkToAmbient pair.prefixTrail).append
    data.oppositePortCentralReturn).edges).Nodup at hclosure
  rw [SimpleGraph.Walk.edges_append] at hclosure
  have hambient : (data.retainedWalkToAmbient pair.prefixTrail).edges.Nodup :=
    hclosure.of_append_left
  rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    SimpleGraph.Walk.edges_map] at hambient
  exact List.Nodup.of_map _ hambient

/-- Exactness of the closed suffix trail likewise implies that its retained
part is a trail. -/
theorem RetainedIntersectionExactFaceCutPair.suffixRetained_isTrail
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.suffixTrail.IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def]
  have hclosure := pair.suffixTrail_isTrail.edges_nodup
  change (((data.retainedWalkToAmbient pair.suffixTrail).append
    data.alternateOppositePortCentralReturnRetained).edges).Nodup at hclosure
  rw [SimpleGraph.Walk.edges_append] at hclosure
  have hambient : (data.retainedWalkToAmbient pair.suffixTrail).edges.Nodup :=
    hclosure.of_append_left
  rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    SimpleGraph.Walk.edges_map] at hambient
  exact List.Nodup.of_map _ hambient

/-- Common retained edges in the order in which the prefix trail traverses
them. -/
def RetainedIntersectionExactFaceCutPair.prefixSharedEdgeOrder
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    List (Sym2 (retainedVertexSet data.firstVertex data.secondVertex)) :=
  pair.prefixTrail.edges.filter fun edge =>
    edge ∈ pair.suffixTrail.edges

/-- The same common retained edges in suffix-trail order. -/
def RetainedIntersectionExactFaceCutPair.suffixSharedEdgeOrder
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    List (Sym2 (retainedVertexSet data.firstVertex data.secondVertex)) :=
  pair.suffixTrail.edges.filter fun edge =>
    edge ∈ pair.prefixTrail.edges

@[simp] theorem RetainedIntersectionExactFaceCutPair.mem_prefixSharedEdgeOrder_iff
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (edge : Sym2 (retainedVertexSet data.firstVertex data.secondVertex)) :
    edge ∈ pair.prefixSharedEdgeOrder ↔
      edge ∈ pair.prefixTrail.edges ∧ edge ∈ pair.suffixTrail.edges := by
  rw [RetainedIntersectionExactFaceCutPair.prefixSharedEdgeOrder,
    List.mem_filter]
  simp only [decide_eq_true_eq]

@[simp] theorem RetainedIntersectionExactFaceCutPair.mem_suffixSharedEdgeOrder_iff
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (edge : Sym2 (retainedVertexSet data.firstVertex data.secondVertex)) :
    edge ∈ pair.suffixSharedEdgeOrder ↔
      edge ∈ pair.prefixTrail.edges ∧ edge ∈ pair.suffixTrail.edges := by
  rw [RetainedIntersectionExactFaceCutPair.suffixSharedEdgeOrder,
    List.mem_filter]
  simp only [decide_eq_true_eq, and_comm]

theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgeOrder_nodup
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.prefixSharedEdgeOrder.Nodup := by
  exact pair.prefixRetained_isTrail.edges_nodup.filter _

theorem RetainedIntersectionExactFaceCutPair.suffixSharedEdgeOrder_nodup
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.suffixSharedEdgeOrder.Nodup := by
  exact pair.suffixRetained_isTrail.edges_nodup.filter _

/-- The two route orders enumerate exactly the same physical retained
edges. -/
theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgeOrder_perm_suffix
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.prefixSharedEdgeOrder.Perm pair.suffixSharedEdgeOrder := by
  apply (List.perm_ext_iff_of_nodup pair.prefixSharedEdgeOrder_nodup
    pair.suffixSharedEdgeOrder_nodup).2
  intro edge
  rw [pair.mem_prefixSharedEdgeOrder_iff,
    pair.mem_suffixSharedEdgeOrder_iff]

/-- The two route orders therefore have the same finite width. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeOrders_length_eq
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.prefixSharedEdgeOrder.length = pair.suffixSharedEdgeOrder.length :=
  pair.prefixSharedEdgeOrder_perm_suffix.length_eq

/-- Forgetting edge-membership proofs identifies the canonical profile
finset with the prefix-ordered shared-edge list. -/
theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgeOrder_toFinset_eq_image_sharedEdges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.prefixSharedEdgeOrder.toFinset =
      pair.sharedEdges.image Subtype.val := by
  ext edge
  rw [List.mem_toFinset, pair.mem_prefixSharedEdgeOrder_iff]
  constructor
  · intro hboth
    let shared : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet :=
      ⟨edge, pair.prefixTrail.edges_subset_edgeSet hboth.1⟩
    exact Finset.mem_image.mpr ⟨shared,
      (pair.mem_sharedEdges_iff shared).2 hboth, rfl⟩
  · intro himage
    rcases Finset.mem_image.mp himage with ⟨shared, hshared, hvalue⟩
    rw [← hvalue]
    exact (pair.mem_sharedEdges_iff shared).1 hshared

/-- The ordered-list width is exactly the cardinality of the canonical
finite intersection profile. -/
theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgeOrder_length_eq_sharedEdges_card
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.prefixSharedEdgeOrder.length = pair.sharedEdges.card := by
  calc
    pair.prefixSharedEdgeOrder.length =
        pair.prefixSharedEdgeOrder.toFinset.card :=
      (List.toFinset_card_of_nodup
        pair.prefixSharedEdgeOrder_nodup).symm
    _ = (pair.sharedEdges.image Subtype.val).card := by
      rw [pair.prefixSharedEdgeOrder_toFinset_eq_image_sharedEdges]
    _ = pair.sharedEdges.card :=
      Finset.card_image_of_injective pair.sharedEdges
        Subtype.val_injective

/-- The suffix order has the same canonical profile width. -/
theorem RetainedIntersectionExactFaceCutPair.suffixSharedEdgeOrder_length_eq_sharedEdges_card
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.suffixSharedEdgeOrder.length = pair.sharedEdges.card := by
  rw [← pair.sharedEdgeOrders_length_eq]
  exact pair.prefixSharedEdgeOrder_length_eq_sharedEdges_card

/-- The physical retained edge selected by a prefix-order position. -/
def RetainedIntersectionExactFaceCutPair.sharedEdgeAt
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
  ⟨pair.prefixSharedEdgeOrder.get position,
    pair.prefixTrail.edges_subset_edgeSet
      ((pair.mem_prefixSharedEdgeOrder_iff
        (pair.prefixSharedEdgeOrder.get position)).1
          (List.get_mem pair.prefixSharedEdgeOrder position)).1⟩

@[simp] theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_val
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (pair.sharedEdgeAt position).1 =
      pair.prefixSharedEdgeOrder.get position :=
  rfl

theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_mem_sharedEdges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    pair.sharedEdgeAt position ∈ pair.sharedEdges := by
  apply (pair.mem_sharedEdges_iff (pair.sharedEdgeAt position)).2
  exact (pair.mem_prefixSharedEdgeOrder_iff
    (pair.prefixSharedEdgeOrder.get position)).1
      (List.get_mem pair.prefixSharedEdgeOrder position)

/-- Distinct prefix-order positions select distinct physical retained
edges. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_injective
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    Function.Injective pair.sharedEdgeAt := by
  intro first second hedge
  apply pair.prefixSharedEdgeOrder_nodup.get_inj_iff.mp
  exact congrArg Subtype.val hedge

/-- Identity-on-edges equivalence between the membership types of the two
ordered shared-edge lists. -/
def RetainedIntersectionExactFaceCutPair.sharedEdgeMembershipEquiv
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    {edge // edge ∈ pair.prefixSharedEdgeOrder} ≃
      {edge // edge ∈ pair.suffixSharedEdgeOrder} where
  toFun edge := ⟨edge.1,
    pair.prefixSharedEdgeOrder_perm_suffix.mem_iff.1 edge.2⟩
  invFun edge := ⟨edge.1,
    pair.prefixSharedEdgeOrder_perm_suffix.mem_iff.2 edge.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Match a prefix-order position with the position of the same physical
edge in the suffix order. -/
def RetainedIntersectionExactFaceCutPair.sharedEdgeOrderEquiv
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    Fin pair.prefixSharedEdgeOrder.length ≃
      Fin pair.suffixSharedEdgeOrder.length :=
  (List.Nodup.getEquiv pair.prefixSharedEdgeOrder
    pair.prefixSharedEdgeOrder_nodup).trans
      (pair.sharedEdgeMembershipEquiv.trans
        (List.Nodup.getEquiv pair.suffixSharedEdgeOrder
          pair.suffixSharedEdgeOrder_nodup).symm)

/-- The order equivalence preserves the selected retained edge. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeOrderEquiv_preserves_edge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    pair.suffixSharedEdgeOrder.get (pair.sharedEdgeOrderEquiv position) =
      pair.prefixSharedEdgeOrder.get position := by
  let prefixPosition :=
    (List.Nodup.getEquiv pair.prefixSharedEdgeOrder
      pair.prefixSharedEdgeOrder_nodup) position
  have hroundTrip :=
    (List.Nodup.getEquiv pair.suffixSharedEdgeOrder
      pair.suffixSharedEdgeOrder_nodup).apply_symm_apply
        (pair.sharedEdgeMembershipEquiv prefixPosition)
  change
    ((List.Nodup.getEquiv pair.suffixSharedEdgeOrder
        pair.suffixSharedEdgeOrder_nodup)
      ((List.Nodup.getEquiv pair.suffixSharedEdgeOrder
        pair.suffixSharedEdgeOrder_nodup).symm
          (pair.sharedEdgeMembershipEquiv prefixPosition))).1 =
      (pair.sharedEdgeMembershipEquiv prefixPosition).1
  exact congrArg Subtype.val hroundTrip

/-- Transporting the suffix order back to the prefix carrier makes the
route-order discrepancy a finite permutation. -/
def RetainedIntersectionExactFaceCutPair.sharedEdgeMonodromy
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    Equiv.Perm (Fin pair.prefixSharedEdgeOrder.length) :=
  pair.sharedEdgeOrderEquiv.trans
    (finCongr pair.sharedEdgeOrders_length_eq.symm)

@[simp] theorem RetainedIntersectionExactFaceCutPair.sharedEdgeMonodromy_apply_val
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (pair.sharedEdgeMonodromy position : Nat) =
      (pair.sharedEdgeOrderEquiv position : Nat) :=
  rfl

/-- Width zero or one has no nontrivial route-order monodromy. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeMonodromy_eq_refl_of_length_le_one
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hwidth : pair.prefixSharedEdgeOrder.length ≤ 1) :
    pair.sharedEdgeMonodromy =
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length) := by
  apply Equiv.ext
  intro position
  apply Fin.ext
  have hposition := position.isLt
  have himage := (pair.sharedEdgeMonodromy position).isLt
  omega

/-- Nonidentity route-order monodromy requires at least two common
retained edges. -/
theorem RetainedIntersectionExactFaceCutPair.two_le_length_of_sharedEdgeMonodromy_ne_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hmonodromy : pair.sharedEdgeMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length)) :
    2 ≤ pair.prefixSharedEdgeOrder.length := by
  by_contra hwidth
  apply hmonodromy
  exact pair.sharedEdgeMonodromy_eq_refl_of_length_le_one (by omega)

/-- Equivalently, nonidentity order monodromy forces the canonical finite
profile itself to have width at least two. -/
theorem RetainedIntersectionExactFaceCutPair.two_le_card_of_sharedEdgeMonodromy_ne_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hmonodromy : pair.sharedEdgeMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length)) :
    2 ≤ pair.sharedEdges.card := by
  rw [← pair.prefixSharedEdgeOrder_length_eq_sharedEdges_card]
  exact pair.two_le_length_of_sharedEdgeMonodromy_ne_refl hmonodromy

/-- A nonidentity profile monodromy is witnessed by two actual shared-edge
positions that occur in opposite orders on the two trails. -/
theorem RetainedIntersectionExactFaceCutPair.exists_sharedEdgeOrderInversion_of_monodromy_ne_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hmonodromy : pair.sharedEdgeMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length)) :
    ∃ first second : Fin pair.prefixSharedEdgeOrder.length,
      first < second ∧
        pair.sharedEdgeMonodromy second <
          pair.sharedEdgeMonodromy first :=
  finPermutation_exists_inversion_of_ne_refl
    pair.sharedEdgeMonodromy hmonodromy

/-- The abstract inversion names two distinct physical common edges and
their reversed suffix-order positions. -/
theorem RetainedIntersectionExactFaceCutPair.exists_physicalSharedEdgeOrderInversion_of_monodromy_ne_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hmonodromy : pair.sharedEdgeMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length)) :
    ∃ first second : Fin pair.prefixSharedEdgeOrder.length,
      first < second ∧
        pair.sharedEdgeOrderEquiv second <
          pair.sharedEdgeOrderEquiv first ∧
        pair.prefixSharedEdgeOrder.get first =
          pair.suffixSharedEdgeOrder.get
            (pair.sharedEdgeOrderEquiv first) ∧
        pair.prefixSharedEdgeOrder.get second =
          pair.suffixSharedEdgeOrder.get
            (pair.sharedEdgeOrderEquiv second) ∧
        pair.prefixSharedEdgeOrder.get first ≠
          pair.prefixSharedEdgeOrder.get second := by
  rcases pair.exists_sharedEdgeOrderInversion_of_monodromy_ne_refl
      hmonodromy with ⟨first, second, hfirstSecond, hreverse⟩
  have hreverse' : pair.sharedEdgeOrderEquiv second <
      pair.sharedEdgeOrderEquiv first := by
    change (pair.sharedEdgeMonodromy second : Nat) <
      (pair.sharedEdgeMonodromy first : Nat) at hreverse
    rw [pair.sharedEdgeMonodromy_apply_val second,
      pair.sharedEdgeMonodromy_apply_val first] at hreverse
    exact hreverse
  have hedgesNe : pair.prefixSharedEdgeOrder.get first ≠
      pair.prefixSharedEdgeOrder.get second := by
    intro hedge
    exact hfirstSecond.ne
      (pair.prefixSharedEdgeOrder_nodup.get_inj_iff.mp hedge)
  exact ⟨first, second, hfirstSecond, hreverse',
    (pair.sharedEdgeOrderEquiv_preserves_edge first).symm,
    (pair.sharedEdgeOrderEquiv_preserves_edge second).symm, hedgesNe⟩

/-- If the whole profile is localized on one face, a nonidentity order
monodromy exposes two distinct new physical edges on that face in reversed
route order. -/
theorem RetainedIntersectionExactFaceCutPair.exists_localizedSharedEdgeOrderInversion_of_monodromy_ne_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem)
    (hlocalized : ∀ edge ∈ pair.sharedEdges,
      edge ≠ oldCross ∧
        retainedEdgeToAmbientEdge data edge ∈
          GoertzelV24FaceOrbitIncidence.orbitFaceBoundary
            graphData.toRotationSystem face)
    (hmonodromy : pair.sharedEdgeMonodromy ≠
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length)) :
    ∃ first second : Fin pair.prefixSharedEdgeOrder.length,
      first < second ∧
        pair.sharedEdgeOrderEquiv second <
          pair.sharedEdgeOrderEquiv first ∧
        pair.sharedEdgeAt first ≠ pair.sharedEdgeAt second ∧
        pair.sharedEdgeAt first ≠ oldCross ∧
        pair.sharedEdgeAt second ≠ oldCross ∧
        retainedEdgeToAmbientEdge data (pair.sharedEdgeAt first) ∈
          GoertzelV24FaceOrbitIncidence.orbitFaceBoundary
            graphData.toRotationSystem face ∧
        retainedEdgeToAmbientEdge data (pair.sharedEdgeAt second) ∈
          GoertzelV24FaceOrbitIncidence.orbitFaceBoundary
            graphData.toRotationSystem face := by
  rcases pair.exists_sharedEdgeOrderInversion_of_monodromy_ne_refl
      hmonodromy with ⟨first, second, hfirstSecond, hreverse⟩
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
  exact ⟨first, second, hfirstSecond, hreverse',
    pair.sharedEdgeAt_injective.ne hfirstSecond.ne,
    hfirstLocalized.1, hsecondLocalized.1,
    hfirstLocalized.2, hsecondLocalized.2⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
