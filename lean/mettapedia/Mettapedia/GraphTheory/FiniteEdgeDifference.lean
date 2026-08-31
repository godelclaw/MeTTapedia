import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

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

end SimpleGraph
