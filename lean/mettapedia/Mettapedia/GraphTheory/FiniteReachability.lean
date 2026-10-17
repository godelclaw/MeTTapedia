import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mettapedia.Logic.Relation.FiniteReachability

/-!
# Computed reachability and connectivity for finite simple graphs

Reachability in a simple graph is the reflexive-transitive closure of adjacency, so the
saturation of `Mettapedia.Logic.Relation.FiniteReachability` computes it exactly.  The
same holds inside an induced subgraph, where reachability is closure of adjacency
restricted to the vertex set.  This gives kernel-evaluable decisions of `Reachable` and
`Connected` for concrete finite graphs, including the subgraphs left after deleting
vertices, which is how vertex connectivity is checked.  Mathlib's own decision procedure
for `Reachable` enumerates walks, which is exponential; saturation is polynomial.

A successor function `next` with `b ∈ next a ↔ G.Adj a b` (for instance adjacency lists)
may replace the generic filter over all vertices.

## Main results

* `reachable_iff_mem_reachSet`, `reachable_iff_mem_reachFrom`.
* `induce_reachable_iff_reflTransGen`: reachability in `G.induce s`.
* `induce_connected_iff_subset_reachSet`: connectivity of the subgraph induced on a finite
  vertex set, decided from one start vertex.
-/

namespace SimpleGraph

open Mettapedia.Logic.Relation

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Reachability is membership in the saturation along any successor function that
lists the neighbours. -/
theorem reachable_iff_mem_reachSet {next : V → Finset V}
    (hnext : ∀ a b, b ∈ next a ↔ G.Adj a b) (u v : V) :
    G.Reachable u v ↔ v ∈ reachSet next {u} := by
  rw [reachable_iff_reflTransGen, mem_reachSet_iff]
  simp only [Finset.mem_singleton, exists_eq_left, hnext]

theorem reachable_iff_mem_reachFrom [DecidableRel G.Adj] (u v : V) :
    G.Reachable u v ↔ v ∈ reachFrom G.Adj u := by
  rw [reachable_iff_reflTransGen, mem_reachFrom_iff]

/-- A graph is connected exactly when the saturation from one vertex is everything. -/
theorem connected_iff_reachSet_eq_univ {next : V → Finset V}
    (hnext : ∀ a b, b ∈ next a ↔ G.Adj a b) (u : V) :
    G.Connected ↔ reachSet next {u} = Finset.univ := by
  constructor
  · intro h
    exact Finset.eq_univ_of_forall fun v => (G.reachable_iff_mem_reachSet hnext u v).mp (h u v)
  · intro h
    exact (connected_iff_exists_forall_reachable G).mpr
      ⟨u, fun v => (G.reachable_iff_mem_reachSet hnext u v).mpr (h ▸ Finset.mem_univ v)⟩

omit [Fintype V] [DecidableEq V] in
/-- Reachability inside an induced subgraph is the reflexive-transitive closure of
adjacency into the vertex set. -/
theorem induce_reachable_iff_reflTransGen {s : Set V} {u v : V} (hu : u ∈ s) (hv : v ∈ s) :
    (G.induce s).Reachable ⟨u, hu⟩ ⟨v, hv⟩ ↔
      Relation.ReflTransGen (fun a b => G.Adj a b ∧ b ∈ s) u v := by
  constructor
  · intro h
    have h' := (reachable_iff_reflTransGen _ _).mp h
    exact Relation.ReflTransGen.lift (fun x : s => (x : V)) (fun x y hxy => ⟨hxy, y.2⟩) _ _ h'
  · intro h
    suffices key : ∀ w, Relation.ReflTransGen (fun a b => G.Adj a b ∧ b ∈ s) u w →
        ∃ hw : w ∈ s, (G.induce s).Reachable ⟨u, hu⟩ ⟨w, hw⟩ from (key v h).2
    intro w hw
    induction hw with
    | refl => exact ⟨hu, .refl _⟩
    | tail _ hbc ih =>
        obtain ⟨hb, hreach⟩ := ih
        exact ⟨hbc.2, hreach.trans (Adj.reachable (G := G.induce s) (u := ⟨_, hb⟩)
          (v := ⟨_, hbc.2⟩) hbc.1)⟩

/-- Reachability inside the subgraph induced on a finite vertex set, computed by
saturation along neighbours inside the set. -/
theorem induce_reachable_iff_mem_reachSet {t : Finset V} {next : V → Finset V}
    (hnext : ∀ a b, b ∈ next a ↔ G.Adj a b ∧ b ∈ t) {u v : V} (hu : u ∈ t) (hv : v ∈ t) :
    (G.induce (t : Set V)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ ↔ v ∈ reachSet next {u} := by
  rw [G.induce_reachable_iff_reflTransGen, mem_reachSet_iff]
  simp only [Finset.mem_singleton, exists_eq_left, hnext, Finset.mem_coe]

/-- **Connectivity of an induced subgraph from one start vertex.**  The subgraph induced
on a finite vertex set containing `w` is connected exactly when saturation from `w` along
neighbours inside the set reaches the whole set. -/
theorem induce_connected_iff_subset_reachSet {t : Finset V} {next : V → Finset V}
    (hnext : ∀ a b, b ∈ next a ↔ G.Adj a b ∧ b ∈ t) {w : V} (hw : w ∈ t) :
    (G.induce (t : Set V)).Connected ↔ t ⊆ reachSet next {w} := by
  constructor
  · intro h v hv
    exact (G.induce_reachable_iff_mem_reachSet hnext hw hv).mp (h ⟨w, hw⟩ ⟨v, hv⟩)
  · intro h
    exact (connected_iff_exists_forall_reachable _).mpr
      ⟨⟨w, hw⟩, fun v => (G.induce_reachable_iff_mem_reachSet hnext hw v.2).mpr (h v.2)⟩

end SimpleGraph
