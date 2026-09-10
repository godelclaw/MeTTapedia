import Mettapedia.GraphTheory.FourColor.DisagreementComponentExchange

/-!
# Every absolute-minimum disagreement component spans the deletion ports

The two contacts from whole-component exchange are physical port incidences
on the same common disagreement component. Branching is allowed. No bound
on its length, on its interface, or on the number of internal branches is
asserted. The actual ordered-row supplier constructs the minimum and its
nonempty disagreement; no colouring or component is an input to that supplier.
-/

namespace Mettapedia.GraphTheory.FourColor.DeletionDisagreementSpanning

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24AdjacentPairBoundary GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24TwoEdgeCutMinimality GoertzelV24RotationMultigraphAdapter
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open SeparatedPairDeletion SeparatedOrderedMeshSites SeparatedDeletionFusion
open DeletionAbsoluteMinimum DisagreementComponentExchange

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem adj_of_members {U : Type*} {H : SimpleGraph U} (e : H.edgeSet)
    {v w : U} (hv : v ∈ e.val) (hw : w ∈ e.val) (hne : v ≠ w) : H.Adj v w := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [Sym2.mem_iff] at hv hw
      rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
      · exact (hne rfl).elim
      · exact he
      · exact (show H.Adj w v from he).symm
      · exact (hne rfl).elim

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem port_of_adj_deleted (data : AdjacentPairData G) {v w : V}
    (hv1 : v ≠ data.firstVertex) (hv2 : v ≠ data.secondVertex)
    (hvw : G.Adj v w) (hw : w = data.firstVertex ∨ w = data.secondVertex) :
    ∃ p, v = data.portVertex p := by
  rcases hw with rfl | rfl
  · have hm : v ∈ G.neighborSet data.firstVertex := hvw.symm
    rw [data.firstNeighbors] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h
    · exact (hv2 h).elim
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · have hm : v ∈ G.neighborSet data.secondVertex := hvw.symm
    rw [data.secondNeighbors] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h
    · exact (hv1 h).elim
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩

def HitsPort (source target site : AdjacentPairData G)
    (e : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet) : Prop :=
  ∃ p : Fin 4, ∃ v, v ∈ e.val ∧ v.val = site.portVertex p

omit [Fintype V] [DecidableRel G.Adj] in
theorem first_boundary_hits_target (source target : AdjacentPairData G)
    (x : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet)
    (z : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).edgeSet)
    (ha : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).lineGraph.Adj
      ((deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex).mapEdgeSet x) z)
    (hout : ¬ ∃ y, (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).mapEdgeSet y = z) : HitsPort source target target x := by
  obtain ⟨_, v, hvx, hvz⟩ := ha
  obtain ⟨w, hw, hwdel⟩ := exists_endpoint_at_second_pair_of_not_in_firstCommonCore_range source target z hout
  obtain ⟨t, htx, htv⟩ := Sym2.mem_map.mp hvx
  have htv' : t.val = v.val := congrArg Subtype.val htv
  have hne : v ≠ w := by
    intro heq
    have heq' : t.val = w.val := htv'.trans (congrArg Subtype.val heq)
    rcases hwdel with h | h
    · exact t.property.2.2.1 (heq'.trans h)
    · exact t.property.2.2.2 (heq'.trans h)
  have hadj : G.Adj t.val w.val := by
    have h := adj_of_members z hvz hw hne
    change G.Adj v.val w.val at h
    rwa [← htv'] at h
  obtain ⟨p, hp⟩ := port_of_adj_deleted target t.property.2.2.1 t.property.2.2.2 hadj hwdel
  exact ⟨p, t, htx, hp⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem second_boundary_hits_source (source target : AdjacentPairData G)
    (x : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet)
    (z : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).edgeSet)
    (ha : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).lineGraph.Adj
      ((deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex).mapEdgeSet x) z)
    (hout : ¬ ∃ y, (deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).mapEdgeSet y = z) : HitsPort source target source x := by
  obtain ⟨_, v, hvx, hvz⟩ := ha
  obtain ⟨w, hw, hwdel⟩ := endpoint_at_first_pair_of_not_in_second_range source target z hout
  obtain ⟨t, htx, htv⟩ := Sym2.mem_map.mp hvx
  have htv' : t.val = v.val := congrArg Subtype.val htv
  have hne : v ≠ w := by
    intro heq
    have heq' : t.val = w.val := htv'.trans (congrArg Subtype.val heq)
    rcases hwdel with h | h
    · exact t.property.1 (heq'.trans h)
    · exact t.property.2.1 (heq'.trans h)
  have hadj : G.Adj t.val w.val := by
    have h := adj_of_members z hvz hw hne
    change G.Adj v.val w.val at h
    rwa [← htv'] at h
  obtain ⟨p, hp⟩ := port_of_adj_deleted source t.property.1 t.property.2.1 hadj hwdel
  exact ⟨p, t, htx, hp⟩

def AllComponentsSpan (source target : AdjacentPairData G)
    (left : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color)
    (right : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).EdgeColoring Color) : Prop :=
  let c := firstDeletionCommonCoreColoring (third := target.firstVertex) (fourth := target.secondVertex) left
  let d := secondDeletionCommonCoreColoring (first := source.firstVertex) (second := source.secondVertex) right
  ∀ K : (graph c d).ConnectedComponent,
    (∃ x ∈ componentEdges c d K, HitsPort source target source x) ∧
    (∃ y ∈ componentEdges c d K, HitsPort source target target y)

theorem allComponentsSpan_of_absolute (source target : AdjacentPairData G)
    (left : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color)
    (right : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).EdgeColoring Color)
    (h : AbsoluteMinimum
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex target.firstVertex target.secondVertex)
      (deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex source.secondVertex target.firstVertex target.secondVertex)
      left right) : AllComponentsSpan source target left right := by
  intro K
  obtain ⟨⟨x, hx, z, hxz, hz⟩, ⟨y, hy, w, hyw, hw⟩⟩ := absolute_component_touches_both _ _ left right h K
  exact ⟨⟨y, hy, second_boundary_hits_source source target y w hyw hw⟩,
    ⟨x, hx, first_boundary_hits_target source target x z hxz hz⟩⟩

/-- Four source ports can be met by at most four disjoint disagreement
components. This is not a bound on their edge counts or interface sizes. -/
theorem card_components_le_four (source target : AdjacentPairData G)
    (left : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color)
    (right : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).EdgeColoring Color)
    (h : AllComponentsSpan source target left right) :
    Nat.card (graph
      (firstDeletionCommonCoreColoring (third := target.firstVertex) (fourth := target.secondVertex) left)
      (secondDeletionCommonCoreColoring (first := source.firstVertex) (second := source.secondVertex) right)).ConnectedComponent ≤ 4 := by
  classical
  let c := firstDeletionCommonCoreColoring (third := target.firstVertex) (fourth := target.secondVertex) left
  let d := secondDeletionCommonCoreColoring (first := source.firstVertex) (second := source.secondVertex) right
  have hits (K : (graph c d).ConnectedComponent) :
      ∃ p : Fin 4, ∃ e ∈ componentEdges c d K, ∃ v, v ∈ e.val ∧ v.val = source.portVertex p := by
    obtain ⟨e, he, p, v, hv, hp⟩ := (h K).1
    exact ⟨p, e, he, v, hv, hp⟩
  let port : (graph c d).ConnectedComponent → Fin 4 := fun K => (hits K).choose
  have hinj : Function.Injective port := by
    intro K L heq
    obtain ⟨e, he, v, hv, hp⟩ := (hits K).choose_spec
    obtain ⟨f, hf, w, hw, hq⟩ := (hits L).choose_spec
    have hvw : v = w := Subtype.ext (hp.trans ((congrArg source.portVertex heq).trans hq.symm))
    exact component_eq_of_incident c d K L he hf hv (hvw ▸ hw)
  simpa using Nat.card_le_card_of_injective port hinj

/-- The stronger component statement is constructed on the exact row-site
pair, with the same absolute minimizing representatives as the obstruction. -/
theorem exists_rowSite_with_spanning_minimum
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {a n : Nat} (ordered : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a (n + 1))
    (row : Fin a) (source : Fin n) (hlarge : 64 < n) :
    ∃ target : Fin n, source ≠ target ∧
    let S := siteData rotation minimal ordered row source
    let T := siteData rotation minimal ordered row target
    ∃ left right, AbsoluteMinimum
      (deletedTwoPairsToFirstDeletionEmbedding G S.firstVertex S.secondVertex T.firstVertex T.secondVertex)
      (deletedTwoPairsToSecondDeletionEmbedding G S.firstVertex S.secondVertex T.firstVertex T.secondVertex)
      left right ∧
      (∃ seed, firstDeletionCommonCoreColoring (third := T.firstVertex) (fourth := T.secondVertex) left seed ≠
        secondDeletionCommonCoreColoring (first := S.firstVertex) (second := S.secondVertex) right seed) ∧
      AllComponentsSpan S T left right := by
  obtain ⟨target, hne, left, right, hmin, hwrong, _⟩ :=
    exists_rowSite_with_absolute_obstruction rotation minimal ordered row source hlarge
  exact ⟨target, hne, left, right, hmin, hwrong, allComponentsSpan_of_absolute _ _ left right hmin⟩

end
end Mettapedia.GraphTheory.FourColor.DeletionDisagreementSpanning
