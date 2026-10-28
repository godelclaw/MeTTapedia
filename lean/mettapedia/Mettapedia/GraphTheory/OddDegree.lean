import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Odd-degree vertices within a component

The handshaking lemma applies to each connected component separately: a component, being
a graph in its own right with the same degrees, has an even number of odd-degree vertices.
So every odd-degree vertex shares its component with a different odd-degree vertex
(`exists_ne_odd_degree_reachable`), the componentwise form of Mathlib's
`exists_ne_odd_degree_of_exists_odd_degree`.  This is the parity step that turns a path
leaving an odd vertex into a path ending at another one.

`exists_adj_notMem_of_odd_degree_of_even` is the companion local fact: if the neighbours
of a vertex inside a region are oddly many while all its neighbours are evenly many, some
neighbour lies outside the region.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Componentwise handshaking.**  An odd-degree vertex reaches a different odd-degree
vertex. -/
theorem exists_ne_odd_degree_reachable {v : V} (hv : Odd (G.degree v)) :
    ∃ w, w ≠ v ∧ Odd (G.degree w) ∧ G.Reachable v w := by
  classical
  set K := G.connectedComponentMk v
  have hvK : v ∈ K.supp := ConnectedComponent.connectedComponentMk_mem
  have hdeg : ∀ x : K.supp, (G.induce K.supp).degree x = G.degree x := fun x =>
    degree_induce_of_neighborSet_subset fun _ hy => K.mem_supp_of_adj_mem_supp x.2 hy
  obtain ⟨w, hwv, hw⟩ := (G.induce K.supp).exists_ne_odd_degree_of_exists_odd_degree
    ⟨v, hvK⟩ (by rwa [hdeg])
  rw [hdeg] at hw
  exact ⟨w, fun h => hwv (Subtype.ext h), hw, K.reachable_of_mem_supp hvK w.2⟩

/-- If a vertex has oddly many neighbours inside a region and evenly many in all, one of
its neighbours lies outside the region. -/
theorem exists_adj_notMem_of_odd_degree_of_even (H : SimpleGraph V) [DecidableRel H.Adj]
    (s : Set V) {v : V} (hH : ∀ w, H.Adj v w ↔ G.Adj v w ∧ w ∈ s) (hodd : Odd (H.degree v))
    (heven : Even (G.degree v)) : ∃ w, G.Adj v w ∧ w ∉ s := by
  by_contra hnone
  push Not at hnone
  have hdeg : H.degree v = G.degree v := by
    rw [← H.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
    congr 1
    ext w
    simp only [mem_neighborFinset, hH]
    exact ⟨And.left, fun h => ⟨h, hnone w h⟩⟩
  exact (Nat.not_even_iff_odd.mpr hodd) (hdeg ▸ heven)

end SimpleGraph
