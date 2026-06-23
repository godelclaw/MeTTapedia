import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.NormNum

namespace Mettapedia.GraphTheory.FourColor.Counterexamples

open SimpleGraph

/-- The path graph with two vertices and one edge. -/
def P2Graph : SimpleGraph Bool where
  Adj a b := a ≠ b
  symm _ _ h := h.symm
  loopless := ⟨fun _ h => h rfl⟩

theorem P2_adj_iff_ne {a b : Bool} : P2Graph.Adj a b ↔ a ≠ b := Iff.rfl

theorem P2_adj_false_true : P2Graph.Adj false true := by
  simp [P2Graph]

theorem P2_adj_true_false : P2Graph.Adj true false := by
  simp [P2Graph]

theorem P2_edge_is_bridge {u v : Bool} (h : P2Graph.Adj u v) :
    P2Graph.IsBridge s(u, v) := by
  rw [SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges]
  refine ⟨h, ?_⟩
  intro p
  have huv : u ≠ v := by
    simpa [P2Graph] using h
  obtain ⟨w, huw, p', rfl⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne (G := P2Graph) huv p
  have hwv : w = v := by
    cases u <;> cases v <;> cases w <;> simp [P2Graph] at h huw ⊢
  subst w
  simp [SimpleGraph.Walk.edges_cons]

theorem P2_acyclic : P2Graph.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro u v h
  exact P2_edge_is_bridge h

/-- A walk in `P2Graph` can bounce across the same edge multiple times. -/
def bounceWalk : P2Graph.Walk false true :=
  Walk.cons P2_adj_false_true
    (Walk.cons P2_adj_true_false
      (Walk.cons P2_adj_false_true Walk.nil))

theorem bounceWalk_length : bounceWalk.length = 3 := by
  simp [bounceWalk]

theorem bounce_between_adjacent_exceeds_one :
    ∃ (G : SimpleGraph Bool) (u v : Bool),
      G.IsAcyclic ∧ G.Adj u v ∧ ∃ w : G.Walk u v, w.length > 1 := by
  refine ⟨P2Graph, false, true, P2_acyclic, by simp [P2Graph], bounceWalk, ?_⟩
  rw [bounceWalk_length]
  norm_num

/-- The complete graph on three vertices. -/
def K3Graph : SimpleGraph (Fin 3) where
  Adj i j := i ≠ j
  symm _ _ h := h.symm
  loopless := ⟨fun _ h => h rfl⟩

theorem K3_edge_01 : K3Graph.Adj 0 1 := by
  simp [K3Graph]

theorem K3_edge_02 : K3Graph.Adj 0 2 := by
  simp [K3Graph]

theorem K3_edge_21 : K3Graph.Adj 2 1 := by
  simp [K3Graph]

theorem K3_walk_01_avoiding_edge_01 :
    ∃ w : K3Graph.Walk 0 1, ∀ e ∈ w.edges, e ≠ s((0 : Fin 3), (1 : Fin 3)) := by
  let w : K3Graph.Walk 0 1 :=
    Walk.cons K3_edge_02
      (Walk.cons K3_edge_21 Walk.nil)
  refine ⟨w, ?_⟩
  intro e he
  have h02 : s((0 : Fin 3), (2 : Fin 3)) ≠ s((0 : Fin 3), (1 : Fin 3)) := by
    decide
  have h21 : s((2 : Fin 3), (1 : Fin 3)) ≠ s((0 : Fin 3), (1 : Fin 3)) := by
    decide
  simp [w, SimpleGraph.Walk.edges_cons] at he
  rcases he with rfl | rfl
  · exact h02
  · exact h21

theorem K3_edge_01_not_bridge :
    ¬ K3Graph.IsBridge s((0 : Fin 3), (1 : Fin 3)) := by
  intro hbridge
  rcases K3_walk_01_avoiding_edge_01 with ⟨w, hw⟩
  exact hw _ ((SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges.mp hbridge).2 w) rfl

theorem triangle_tree_edge_not_bridge :
    ∃ (u v : Fin 3) (e : Sym2 (Fin 3)),
      K3Graph.Adj u v ∧ e = s(u, v) ∧
        ∃ w : K3Graph.Walk u v, ∀ e' ∈ w.edges, e' ≠ e := by
  refine ⟨0, 1, s((0 : Fin 3), (1 : Fin 3)), K3_edge_01, rfl, ?_⟩
  exact K3_walk_01_avoiding_edge_01

end Mettapedia.GraphTheory.FourColor.Counterexamples
