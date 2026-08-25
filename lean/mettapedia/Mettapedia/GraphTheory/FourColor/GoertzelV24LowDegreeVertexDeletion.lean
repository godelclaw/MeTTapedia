import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Deleting leaves preserves preconnectedness

If a finite simple graph is connected, deleting any collection of vertices
whose ambient degrees are at most one leaves a preconnected induced graph.
The result deliberately says `Preconnected`: deleting every vertex of a
one-edge graph leaves an empty graph, which has no inhabitant but still has
the required pairwise reachability property.

The proof is elementary and does not classify the graph.  A simple path
between two retained vertices cannot use a deleted vertex internally, because
an internal path vertex has two distinct neighbours.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24LowDegreeVertexDeletion

open SimpleGraph

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
  {graph : SimpleGraph Vertex} [DecidableRel graph.Adj]

/-- Deleting any finite set of degree-at-most-one vertices from a connected
finite graph leaves a preconnected induced graph. -/
theorem preconnected_induce_compl_of_degree_le_one
    (hconnected : graph.Connected) (removed : Finset Vertex)
    (hdegree : ∀ vertex ∈ removed, graph.degree vertex ≤ 1) :
    (graph.induce (↑removed : Set Vertex)ᶜ).Preconnected := by
  classical
  intro start finish
  obtain ⟨path, hpath⟩ := hconnected.exists_isPath start.1 finish.1
  have hsupport :
      ∀ vertex ∈ path.support, vertex ∈ (↑removed : Set Vertex)ᶜ := by
    intro vertex hvertexSupport
    rw [Set.mem_compl_iff, Finset.mem_coe]
    intro hvertexRemoved
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvertexSupport with
      ⟨index, hindexVertex, hindexBound⟩
    have hindexNotStart : index ≠ 0 := by
      intro hindex
      subst index
      have hvertexEq : vertex = start.1 := by
        simpa using hindexVertex.symm
      exact start.2 (hvertexEq ▸ hvertexRemoved)
    have hindexNotFinish : index ≠ path.length := by
      intro hindex
      have hvertexEq : vertex = finish.1 := by
        calc
          vertex = path.getVert index := hindexVertex.symm
          _ = finish.1 := by simp [hindex]
      exact finish.2 (hvertexEq ▸ hvertexRemoved)
    have hindexLt : index < path.length := by omega
    let previous : Vertex := path.getVert (index - 1)
    let next : Vertex := path.getVert (index + 1)
    have hpreviousAdj : graph.Adj vertex previous := by
      have hpreviousIndex : index - 1 < path.length := by omega
      have hadj := path.adj_getVert_succ hpreviousIndex
      have hsub : index - 1 + 1 = index :=
        Nat.sub_add_cancel (Nat.pos_of_ne_zero hindexNotStart)
      simpa [previous, hindexVertex, hsub] using hadj.symm
    have hnextAdj : graph.Adj vertex next := by
      have hadj := path.adj_getVert_succ hindexLt
      simpa [next, hindexVertex] using hadj
    have hpreviousNeNext : previous ≠ next := by
      intro heq
      have hindices : index - 1 = index + 1 :=
        hpath.getVert_injOn
          (by rw [Set.mem_setOf_eq]; omega)
          (by rw [Set.mem_setOf_eq]; omega)
          (by simpa [previous, next] using heq)
      omega
    let neighbors : Finset Vertex := {previous, next}
    have hneighborsSubset : neighbors ⊆ graph.neighborFinset vertex := by
      intro candidate hcandidate
      simp [neighbors] at hcandidate
      rcases hcandidate with rfl | rfl
      · simpa using hpreviousAdj
      · simpa using hnextAdj
    have hdegreeAtLeastTwo : 2 ≤ graph.degree vertex := by
      rw [← graph.card_neighborFinset_eq_degree]
      calc
        2 = neighbors.card := by simp [neighbors, hpreviousNeNext]
        _ ≤ (graph.neighborFinset vertex).card :=
          Finset.card_le_card hneighborsSubset
    exact (Nat.not_succ_le_self 1)
      (hdegreeAtLeastTwo.trans (hdegree vertex hvertexRemoved))
  exact ⟨path.induce (↑removed : Set Vertex)ᶜ hsupport⟩

end GoertzelV24LowDegreeVertexDeletion

end Mettapedia.GraphTheory.FourColor
