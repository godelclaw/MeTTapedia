import Mettapedia.GraphTheory.FiniteEdgeDifference
import Mettapedia.GraphTheory.ComponentAvoidance
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Connectivity through a finite edge patch

Removing a finite set of edges leaves a common exterior graph.  Every
component change caused by restoring some of those edges is visible on the
finite set of their endpoints.  This file packages that observation without
any planarity or colouring assumptions.

For boundary vertices, reachability in the original graph is exactly the
reflexive-transitive closure of two kinds of moves:

* travel inside one component of the graph with the patch deleted;
* travel inside the graph consisting only of original edges in the patch.

The boundary has at most twice as many vertices as the patch has edges.
-/

namespace SimpleGraph

noncomputable section

universe u

variable {V : Type u} [DecidableEq V]

/-- Vertices incident with at least one edge in a finite edge patch. -/
def edgeBoundaryVertices (patch : Finset (Sym2 V)) : Finset V :=
  patch.biUnion Sym2.toFinset

/-- The finite carrier on which a finite edge patch can change components. -/
abbrev EdgeBoundary (patch : Finset (Sym2 V)) :=
  { vertex : V // vertex ∈ edgeBoundaryVertices patch }

@[simp]
theorem mem_edgeBoundaryVertices
    (patch : Finset (Sym2 V)) (vertex : V) :
    vertex ∈ edgeBoundaryVertices patch ↔
      ∃ edge ∈ patch, vertex ∈ edge := by
  simp [edgeBoundaryVertices, Sym2.mem_toFinset]

/-- A finite edge patch has at most two boundary vertices per edge. -/
theorem card_edgeBoundaryVertices_le (patch : Finset (Sym2 V)) :
    (edgeBoundaryVertices patch).card ≤ 2 * patch.card := by
  calc
    (edgeBoundaryVertices patch).card ≤
        ∑ edge ∈ patch, edge.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _edge ∈ patch, 2 := by
      apply Finset.sum_le_sum
      intro edge hedge
      rw [Sym2.card_toFinset]
      split <;> omega
    _ = 2 * patch.card := by simp [Nat.mul_comm]

/-! ## Exact invariance outside the patch boundary -/

/-- If deleting a finite patch makes two graphs equal, their adjacency
relations already agree at every vertex not incident with a patch edge. -/
theorem adj_iff_of_deleteEdges_eq_of_not_mem_edgeBoundaryVertices
    (first second : SimpleGraph V) (patch : Finset (Sym2 V))
    (heq : first.deleteEdges (patch : Set (Sym2 V)) =
      second.deleteEdges (patch : Set (Sym2 V)))
    {left right : V} (hleft : left ∉ edgeBoundaryVertices patch) :
    first.Adj left right ↔ second.Adj left right := by
  have hedge : s(left, right) ∉ patch := by
    intro hedge
    exact hleft ((mem_edgeBoundaryVertices patch left).2
      ⟨s(left, right), hedge, by simp⟩)
  have hdeleted :
      (first.deleteEdges (patch : Set (Sym2 V))).Adj left right ↔
        (second.deleteEdges (patch : Set (Sym2 V))).Adj left right := by
    rw [heq]
  simpa only [deleteEdges_adj, Finset.mem_coe, hedge, not_false_eq_true,
    and_true] using hdeleted

/-- A component disjoint from every endpoint of a finite modification patch
has unchanged reachability after that patch is modified. -/
theorem reachable_iff_of_avoids_edgeBoundaryVertices_of_deleteEdges_eq
    (first second : SimpleGraph V) (patch : Finset (Sym2 V))
    (heq : first.deleteEdges (patch : Set (Sym2 V)) =
      second.deleteEdges (patch : Set (Sym2 V)))
    {root target : V}
    (havoid : ∀ vertex, vertex ∈ edgeBoundaryVertices patch →
      ¬ first.Reachable root vertex) :
    first.Reachable root target ↔ second.Reachable root target := by
  apply Mettapedia.GraphTheory.reachable_iff_of_adj_iff_off_set
    (modified := (edgeBoundaryVertices patch : Set V)) havoid
  intro left right hleft
  exact adj_iff_of_deleteEdges_eq_of_not_mem_edgeBoundaryVertices
    first second patch heq (by simpa using hleft)

/-- The support of a component disjoint from the finite patch boundary is
literally unchanged. -/
theorem connectedComponentMk_supp_eq_of_avoids_edgeBoundaryVertices_of_deleteEdges_eq
    (first second : SimpleGraph V) (patch : Finset (Sym2 V))
    (heq : first.deleteEdges (patch : Set (Sym2 V)) =
      second.deleteEdges (patch : Set (Sym2 V)))
    (root : V)
    (havoid : ∀ vertex, vertex ∈ edgeBoundaryVertices patch →
      ¬ first.Reachable root vertex) :
    (first.connectedComponentMk root).supp =
      (second.connectedComponentMk root).supp := by
  apply Mettapedia.GraphTheory.connectedComponentMk_supp_eq_of_adj_iff_off_set
    (modified := (edgeBoundaryVertices patch : Set V)) root havoid
  intro left right hleft
  exact adj_iff_of_deleteEdges_eq_of_not_mem_edgeBoundaryVertices
    first second patch heq (by simpa using hleft)

/-- Exact metric localization: modifying a finite edge patch cannot change
distances inside a component which is disjoint from every patch endpoint. -/
theorem dist_eq_of_avoids_edgeBoundaryVertices_of_deleteEdges_eq
    (first second : SimpleGraph V) (patch : Finset (Sym2 V))
    (heq : first.deleteEdges (patch : Set (Sym2 V)) =
      second.deleteEdges (patch : Set (Sym2 V)))
    {root target : V}
    (havoid : ∀ vertex, vertex ∈ edgeBoundaryVertices patch →
      ¬ first.Reachable root vertex) :
    first.dist root target = second.dist root target := by
  apply Mettapedia.GraphTheory.dist_eq_of_adj_iff_off_set
    (modified := (edgeBoundaryVertices patch : Set V)) havoid
  intro left right hleft
  exact adj_iff_of_deleteEdges_eq_of_not_mem_edgeBoundaryVertices
    first second patch heq (by simpa using hleft)

/-- The part of `G` supported on a prescribed finite edge patch. -/
def exceptionalEdgeGraph (G : SimpleGraph V) (patch : Finset (Sym2 V)) :
    SimpleGraph V :=
  fromEdgeSet (G.edgeSet ∩ (patch : Set (Sym2 V)))

/-- Deleting the patch and then restoring the original patch edges recovers
the original graph. -/
theorem deleteEdges_sup_exceptionalEdgeGraph
    (G : SimpleGraph V) (patch : Finset (Sym2 V)) :
    G.deleteEdges (patch : Set (Sym2 V)) ⊔ exceptionalEdgeGraph G patch = G := by
  ext left right
  simp only [sup_adj, deleteEdges_adj, exceptionalEdgeGraph, fromEdgeSet_adj,
    Set.mem_inter_iff, Finset.mem_coe, mem_edgeSet]
  constructor
  · rintro (⟨hadj, _⟩ | ⟨⟨hadj, _⟩, _⟩) <;> exact hadj
  · intro hadj
    by_cases hpatch : s(left, right) ∈ patch
    · exact Or.inr ⟨⟨hadj, hpatch⟩, hadj.ne⟩
    · exact Or.inl ⟨hadj, hpatch⟩

/-- A nontrivial path in the exceptional-edge graph starts at a boundary
vertex of the patch. -/
theorem mem_edgeBoundaryVertices_of_exceptionalEdgeGraph_reachable
    (G : SimpleGraph V) (patch : Finset (Sym2 V)) {left right : V}
    (hne : left ≠ right)
    (hreach : (exceptionalEdgeGraph G patch).Reachable left right) :
    left ∈ edgeBoundaryVertices patch := by
  have hsupport : left ∈ (exceptionalEdgeGraph G patch).support :=
    mem_support_of_reachable hne hreach
  rcases (mem_support _).1 hsupport with ⟨neighbor, hadj⟩
  have hpatch : s(left, neighbor) ∈ patch := by
    change (G.Adj left neighbor ∧ s(left, neighbor) ∈ patch) ∧
      left ≠ neighbor at hadj
    exact hadj.1.2
  exact (mem_edgeBoundaryVertices patch left).2
    ⟨s(left, neighbor), hpatch, by simp⟩

private abbrev BoundaryComponentStep
    (first second : SimpleGraph V) (selected : V → Prop)
    (left right : V) : Prop :=
  selected left ∧ selected right ∧
    (first.Reachable left right ∨ second.Reachable left right)

private def BoundarySplitState
    (first second : SimpleGraph V) (selected : V → Prop)
    (start current : V) : Prop :=
  (selected current ∧
      Relation.ReflTransGen
        (BoundaryComponentStep first second selected) start current) ∨
  (∃ last, selected last ∧
      Relation.ReflTransGen
        (BoundaryComponentStep first second selected) start last ∧
      last ≠ current ∧ first.Reachable last current) ∨
  (∃ last, selected last ∧
      Relation.ReflTransGen
        (BoundaryComponentStep first second selected) start last ∧
      last ≠ current ∧ second.Reachable last current)

private theorem boundarySplitState_step
    (first second : SimpleGraph V) (selected : V → Prop)
    (start left right : V)
    (hswitch : ∀ {x middle y}, x ≠ middle → middle ≠ y →
      first.Reachable x middle → second.Reachable middle y →
        selected middle)
    (hleft : BoundarySplitState first second selected start left)
    (hadj : first.Adj left right ∨ second.Adj left right) :
    BoundarySplitState first second selected start right := by
  rcases hadj with hfirst | hsecond
  · rcases hleft with ⟨hselected, hstart⟩ |
        ⟨last, hlastSelected, hstart, hne, hreach⟩ |
        ⟨last, hlastSelected, hstart, hne, hreach⟩
    · exact Or.inr (Or.inl
        ⟨left, hselected, hstart, hfirst.ne, hfirst.reachable⟩)
    · by_cases hlast : last = right
      · subst right
        exact Or.inl ⟨hlastSelected, hstart⟩
      · exact Or.inr (Or.inl
          ⟨last, hlastSelected, hstart, hlast,
            hreach.trans hfirst.reachable⟩)
    · have hselected : selected left :=
        hswitch hfirst.ne.symm hne.symm hfirst.reachable.symm hreach.symm
      exact Or.inr (Or.inl
        ⟨left, hselected,
          hstart.tail ⟨hlastSelected, hselected, Or.inr hreach⟩,
          hfirst.ne, hfirst.reachable⟩)
  · rcases hleft with ⟨hselected, hstart⟩ |
        ⟨last, hlastSelected, hstart, hne, hreach⟩ |
        ⟨last, hlastSelected, hstart, hne, hreach⟩
    · exact Or.inr (Or.inr
        ⟨left, hselected, hstart, hsecond.ne, hsecond.reachable⟩)
    · have hselected : selected left :=
        hswitch hne hsecond.ne hreach hsecond.reachable
      exact Or.inr (Or.inr
        ⟨left, hselected,
          hstart.tail ⟨hlastSelected, hselected, Or.inl hreach⟩,
          hsecond.ne, hsecond.reachable⟩)
    · by_cases hlast : last = right
      · subst right
        exact Or.inl ⟨hlastSelected, hstart⟩
      · exact Or.inr (Or.inr
          ⟨last, hlastSelected, hstart, hlast,
            hreach.trans hsecond.reachable⟩)

private theorem boundarySplitState_of_reflTransGen
    (first second : SimpleGraph V) (selected : V → Prop)
    (start current : V)
    (hswitch : ∀ {x middle y}, x ≠ middle → middle ≠ y →
      first.Reachable x middle → second.Reachable middle y →
        selected middle)
    (hstart : selected start)
    (hpath : Relation.ReflTransGen
      (fun x y => first.Adj x y ∨ second.Adj x y) start current) :
    BoundarySplitState first second selected start current := by
  induction hpath with
  | refl => exact Or.inl ⟨hstart, .refl⟩
  | tail hxy hyz ih =>
      exact boundarySplitState_step first second selected start _ _
        hswitch ih hyz

omit [DecidableEq V] in
private theorem boundaryClosure_to_subtype
    (first second : SimpleGraph V) (selected : V → Prop)
    {left right : V} (hleft : selected left) (hright : selected right)
    (hclosure : Relation.ReflTransGen
      (BoundaryComponentStep first second selected) left right) :
    Relation.ReflTransGen
      (fun x y : Subtype selected =>
        first.Reachable x y ∨ second.Reachable x y)
      ⟨left, hleft⟩ ⟨right, hright⟩ := by
  induction hclosure with
  | refl => exact .refl
  | tail hxy hyz ih => exact (ih hyz.1).tail hyz.2.2

private theorem reachable_sup_iff_boundaryClosure
    (first second : SimpleGraph V) (selected : V → Prop)
    (left right : V) (hleft : selected left) (hright : selected right)
    (hswitch : ∀ {x middle y}, x ≠ middle → middle ≠ y →
      first.Reachable x middle → second.Reachable middle y →
        selected middle) :
    (first ⊔ second).Reachable left right ↔
      Relation.ReflTransGen
        (fun x y : Subtype selected =>
          first.Reachable x y ∨ second.Reachable x y)
        ⟨left, hleft⟩ ⟨right, hright⟩ := by
  constructor
  · intro hreach
    have hpath : Relation.ReflTransGen
        (fun x y => first.Adj x y ∨ second.Adj x y) left right := by
      have h := (reachable_iff_reflTransGen left right).mp hreach
      exact h.mono fun x y hxy => (sup_adj first second x y).mp hxy
    have hstate := boundarySplitState_of_reflTransGen
      first second selected left right hswitch hleft hpath
    have hclosure : Relation.ReflTransGen
        (BoundaryComponentStep first second selected) left right := by
      rcases hstate with ⟨_, h⟩ | ⟨last, hlast, h, _, hreach⟩ |
          ⟨last, hlast, h, _, hreach⟩
      · exact h
      · exact h.tail ⟨hlast, hright, Or.inl hreach⟩
      · exact h.tail ⟨hlast, hright, Or.inr hreach⟩
    exact boundaryClosure_to_subtype first second selected hleft hright hclosure
  · intro hclosure
    have hambient : Relation.ReflTransGen
        (BoundaryComponentStep first second selected) left right :=
      hclosure.lift Subtype.val fun x y hxy => ⟨x.2, y.2, hxy⟩
    exact Relation.ReflTransGen.trans_induction_on
      (motive := fun {x y} _ => (first ⊔ second).Reachable x y)
      hambient
      (fun _ => Reachable.rfl)
      (fun hxy => hxy.2.2.elim
        (Reachable.mono le_sup_left) (Reachable.mono le_sup_right))
      (fun _ _ hxy hyz => hxy.trans hyz)

/-- Complete component factorization through the finite endpoint boundary of
an edge patch.  This is the finite state controlling every component that
meets the patch. -/
theorem reachable_iff_edgeBoundaryClosure
    (G : SimpleGraph V) (patch : Finset (Sym2 V))
    {left right : V}
    (hleft : left ∈ edgeBoundaryVertices patch)
    (hright : right ∈ edgeBoundaryVertices patch) :
    G.Reachable left right ↔
      Relation.ReflTransGen
        (fun x y : EdgeBoundary patch =>
          (G.deleteEdges (patch : Set (Sym2 V))).Reachable x y ∨
            (exceptionalEdgeGraph G patch).Reachable x y)
        ⟨left, hleft⟩ ⟨right, hright⟩ := by
  calc
    G.Reachable left right ↔
        (G.deleteEdges (patch : Set (Sym2 V)) ⊔
          exceptionalEdgeGraph G patch).Reachable left right := by
      rw [deleteEdges_sup_exceptionalEdgeGraph]
    _ ↔ _ := by
      apply reachable_sup_iff_boundaryClosure
      intro x middle y _hxm hmy _hdeleted hexceptional
      exact mem_edgeBoundaryVertices_of_exceptionalEdgeGraph_reachable
        G patch hmy hexceptional

end

end SimpleGraph
