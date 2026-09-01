import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.List.Chain

/-!
# Finite edge disagreement between simple graphs

For two finite simple graphs on the same vertex type,
`edgeDisagreementFinset` records the symmetric difference of their edge sets.
The main localization lemma says that if deleting a finite edge set makes the
graphs equal, every disagreement edge lies in that set.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite set of edge values on which two simple graphs disagree. -/
noncomputable def edgeDisagreementFinset
    (first second : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun edge =>
    (edge ∈ first.edgeSet ∧ edge ∉ second.edgeSet) ∨
      (edge ∈ second.edgeSet ∧ edge ∉ first.edgeSet)

@[simp]
theorem mem_edgeDisagreementFinset
    (first second : SimpleGraph V) (edge : Sym2 V) :
    edge ∈ edgeDisagreementFinset first second ↔
      (edge ∈ first.edgeSet ∧ edge ∉ second.edgeSet) ∨
        (edge ∈ second.edgeSet ∧ edge ∉ first.edgeSet) := by
  classical
  simp [edgeDisagreementFinset]

/-- Edge disagreement is symmetric in the two graphs. -/
theorem edgeDisagreementFinset_comm
    (first second : SimpleGraph V) :
    edgeDisagreementFinset first second =
      edgeDisagreementFinset second first := by
  classical
  ext edge
  simp only [mem_edgeDisagreementFinset]
  tauto

/-- Every disagreement between the first and third graphs occurs in at least
one of the two intermediate disagreements. -/
theorem edgeDisagreementFinset_subset_union
    (first second third : SimpleGraph V) :
    edgeDisagreementFinset first third ⊆
      edgeDisagreementFinset first second ∪
        edgeDisagreementFinset second third := by
  classical
  intro edge hedge
  rw [mem_edgeDisagreementFinset] at hedge
  rw [Finset.mem_union]
  rcases hedge with ⟨hfirst, hthird⟩ | ⟨hthird, hfirst⟩
  · by_cases hsecond : edge ∈ second.edgeSet
    · exact Or.inr ((mem_edgeDisagreementFinset second third edge).2
        (Or.inl ⟨hsecond, hthird⟩))
    · exact Or.inl ((mem_edgeDisagreementFinset first second edge).2
        (Or.inl ⟨hfirst, hsecond⟩))
  · by_cases hsecond : edge ∈ second.edgeSet
    · exact Or.inl ((mem_edgeDisagreementFinset first second edge).2
        (Or.inr ⟨hsecond, hfirst⟩))
    · exact Or.inr ((mem_edgeDisagreementFinset second third edge).2
        (Or.inr ⟨hthird, hsecond⟩))

/-- Cardinal triangle inequality for finite edge disagreement. -/
theorem card_edgeDisagreementFinset_triangle
    (first second third : SimpleGraph V) :
    (edgeDisagreementFinset first third).card ≤
      (edgeDisagreementFinset first second).card +
        (edgeDisagreementFinset second third).card := by
  calc
    (edgeDisagreementFinset first third).card ≤
        (edgeDisagreementFinset first second ∪
          edgeDisagreementFinset second third).card :=
      Finset.card_le_card
        (edgeDisagreementFinset_subset_union first second third)
    _ ≤ (edgeDisagreementFinset first second).card +
        (edgeDisagreementFinset second third).card :=
      Finset.card_union_le _ _

/-- The sum of consecutive edge disagreements along a list of graphs. -/
noncomputable def edgeDisagreementPathCost :
    List (SimpleGraph V) → ℕ
  | first :: second :: rest =>
      (edgeDisagreementFinset first second).card +
        edgeDisagreementPathCost (second :: rest)
  | _ => 0

/-- The endpoint disagreement is at most the sum of the consecutive
disagreements along any finite graph path. -/
theorem card_edgeDisagreementFinset_le_pathCost
    (first last : SimpleGraph V) :
    ∀ middle : List (SimpleGraph V),
      (edgeDisagreementFinset first last).card ≤
        edgeDisagreementPathCost (first :: middle ++ [last])
  | [] => by
      simp [edgeDisagreementPathCost]
  | next :: rest => by
      change (edgeDisagreementFinset first last).card ≤
        (edgeDisagreementFinset first next).card +
          edgeDisagreementPathCost (next :: rest ++ [last])
      exact (card_edgeDisagreementFinset_triangle first next last).trans
        (Nat.add_le_add_left
          (card_edgeDisagreementFinset_le_pathCost next last rest) _)

/-- If every consecutive transition in a finite graph path has disagreement
at most `bound`, its total path cost is at most `bound` times the number of
transitions. -/
theorem edgeDisagreementPathCost_le
    (bound : ℕ) (graphs : List (SimpleGraph V))
    (hchain : graphs.IsChain fun first second =>
      (edgeDisagreementFinset first second).card ≤ bound) :
    edgeDisagreementPathCost graphs ≤ (graphs.length - 1) * bound := by
  induction graphs using List.twoStepInduction with
  | nil => simp [edgeDisagreementPathCost]
  | singleton graph => simp [edgeDisagreementPathCost]
  | cons_cons first second rest _ tailIH =>
      rcases List.isChain_cons_cons.mp hchain with ⟨hfirst, htail⟩
      rw [edgeDisagreementPathCost]
      calc
        (edgeDisagreementFinset first second).card +
            edgeDisagreementPathCost (second :: rest) ≤
          bound + ((second :: rest).length - 1) * bound :=
            Nat.add_le_add hfirst (tailIH second htail)
        _ = ((first :: second :: rest).length - 1) * bound := by
          simp [Nat.add_mul, Nat.add_comm]

/-- A walk in the first graph whose edges avoid the edge disagreement with a
second graph transfers verbatim to the second graph. -/
noncomputable def Walk.transferAvoidingEdgeDisagreement
    {first second : SimpleGraph V} {left right : V}
    (walk : first.Walk left right)
    (havoids : ∀ edge ∈ walk.edges,
      edge ∉ edgeDisagreementFinset first second) :
    second.Walk left right := by
  apply walk.transfer second
  intro edge hedge
  have hfirst : edge ∈ first.edgeSet := walk.edges_subset_edgeSet hedge
  by_contra hsecond
  exact havoids edge hedge
    ((mem_edgeDisagreementFinset first second edge).2
      (Or.inl ⟨hfirst, hsecond⟩))

/-- Reachability form of `Walk.transferAvoidingEdgeDisagreement`. -/
theorem Walk.reachable_of_avoids_edgeDisagreement
    {first second : SimpleGraph V} {left right : V}
    (walk : first.Walk left right)
    (havoids : ∀ edge ∈ walk.edges,
      edge ∉ edgeDisagreementFinset first second) :
    second.Reachable left right :=
  (walk.transferAvoidingEdgeDisagreement havoids).reachable

/-- If a walk in the first graph joins vertices which are disconnected in the
second, some edge of the walk witnesses the finite graph disagreement. -/
theorem Walk.exists_edgeDisagreement_of_not_reachable
    {first second : SimpleGraph V} {left right : V}
    (walk : first.Walk left right)
    (hnot : ¬ second.Reachable left right) :
    ∃ edge ∈ walk.edges, edge ∈ edgeDisagreementFinset first second := by
  by_contra hnone
  apply hnot
  apply walk.reachable_of_avoids_edgeDisagreement
  intro edge hedge hdisagreement
  apply hnone
  exact ⟨edge, hedge, hdisagreement⟩

/-- Component-valued form of
`Walk.reachable_of_avoids_edgeDisagreement`. -/
theorem Walk.connectedComponentMk_eq_of_avoids_edgeDisagreement
    {first second : SimpleGraph V} {left right : V}
    (walk : first.Walk left right)
    (havoids : ∀ edge ∈ walk.edges,
      edge ∉ edgeDisagreementFinset first second) :
    second.connectedComponentMk left = second.connectedComponentMk right :=
  ConnectedComponent.sound
    (walk.reachable_of_avoids_edgeDisagreement havoids)

/-- If deleting `removed` makes two graphs equal, all their edge disagreement
is supported on `removed`. -/
theorem edgeDisagreementFinset_subset_of_deleteEdges_eq
    (first second : SimpleGraph V) (removed : Finset (Sym2 V))
    (heq : first.deleteEdges (removed : Set (Sym2 V)) =
      second.deleteEdges (removed : Set (Sym2 V))) :
    edgeDisagreementFinset first second ⊆ removed := by
  classical
  intro edge hedge
  rw [mem_edgeDisagreementFinset] at hedge
  by_contra houtside
  have hdeleted :
      edge ∈ (first.deleteEdges (removed : Set (Sym2 V))).edgeSet ↔
        edge ∈ (second.deleteEdges (removed : Set (Sym2 V))).edgeSet := by
    rw [heq]
  induction edge using Sym2.inductionOn with
  | _ left right =>
      simp only [mem_edgeSet, deleteEdges_adj, Finset.mem_coe, houtside,
        not_false_eq_true, and_true] at hdeleted
      exact hedge.elim
        (fun h => h.2 (hdeleted.mp h.1))
        (fun h => h.2 (hdeleted.mpr h.1))

/-- Cardinal form of
`edgeDisagreementFinset_subset_of_deleteEdges_eq`. -/
theorem card_edgeDisagreementFinset_le_of_deleteEdges_eq
    (first second : SimpleGraph V) (removed : Finset (Sym2 V))
    (heq : first.deleteEdges (removed : Set (Sym2 V)) =
      second.deleteEdges (removed : Set (Sym2 V))) :
    (edgeDisagreementFinset first second).card ≤ removed.card :=
  Finset.card_le_card
    (edgeDisagreementFinset_subset_of_deleteEdges_eq first second removed heq)

/-- If two graphs become equal after deleting `removed`, vertices whose
reachability differs between the graphs cannot already be joined in the
common deleted graph. -/
theorem not_reachable_deleteEdges_of_reachability_differs
    (first second : SimpleGraph V) (removed : Finset (Sym2 V))
    (heq : first.deleteEdges (removed : Set (Sym2 V)) =
      second.deleteEdges (removed : Set (Sym2 V)))
    {left right : V}
    (hdiffers : ¬ (first.Reachable left right ↔
      second.Reachable left right)) :
    ¬ (first.deleteEdges (removed : Set (Sym2 V))).Reachable left right := by
  intro hcommon
  have hfirst : first.Reachable left right :=
    hcommon.mono (first.deleteEdges_le (removed : Set (Sym2 V)))
  have hsecondDeleted :
      (second.deleteEdges (removed : Set (Sym2 V))).Reachable left right := by
    rw [← heq]
    exact hcommon
  have hsecond : second.Reachable left right :=
    hsecondDeleted.mono (second.deleteEdges_le (removed : Set (Sym2 V)))
  exact hdiffers ⟨fun _ ↦ hsecond, fun _ ↦ hfirst⟩

/-- If deleting `removed` makes two graphs equal but changes reachability,
one of the two graphs has a connecting walk which traverses `removed`. -/
theorem exists_walk_hitting_of_deleteEdges_eq_of_reachability_differs
    (first second : SimpleGraph V) (removed : Finset (Sym2 V))
    (heq : first.deleteEdges (removed : Set (Sym2 V)) =
      second.deleteEdges (removed : Set (Sym2 V)))
    {left right : V}
    (hdiffers : ¬ (first.Reachable left right ↔
      second.Reachable left right)) :
    (∃ walk : first.Walk left right,
        ∃ edge ∈ walk.edges, edge ∈ removed) ∨
      (∃ walk : second.Walk left right,
        ∃ edge ∈ walk.edges, edge ∈ removed) := by
  classical
  by_cases hfirst : first.Reachable left right
  · have hnotSecond : ¬ second.Reachable left right := by
      intro hsecond
      exact hdiffers ⟨fun _ ↦ hsecond, fun _ ↦ hfirst⟩
    rcases hfirst with ⟨walk⟩
    rcases walk.exists_edgeDisagreement_of_not_reachable hnotSecond with
      ⟨edge, hedgeWalk, hedgeDifference⟩
    exact Or.inl ⟨walk, edge, hedgeWalk,
      edgeDisagreementFinset_subset_of_deleteEdges_eq
        first second removed heq hedgeDifference⟩
  · have hsecond : second.Reachable left right := by
      by_contra hnotSecond
      apply hdiffers
      exact ⟨fun h ↦ False.elim (hfirst h),
        fun h ↦ False.elim (hnotSecond h)⟩
    rcases hsecond with ⟨walk⟩
    rcases walk.exists_edgeDisagreement_of_not_reachable hfirst with
      ⟨edge, hedgeWalk, hedgeDifference⟩
    exact Or.inr ⟨walk, edge, hedgeWalk,
      edgeDisagreementFinset_subset_of_deleteEdges_eq
        second first removed heq.symm hedgeDifference⟩

end SimpleGraph
