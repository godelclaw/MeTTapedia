import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# From vertex separators to complete connected edge cuts

Start with two disjoint connected terminal sets. Flood from the first
through the complement of a vertex separator, restore its terminal
vertices, then fill every complementary component except the component
containing the other terminal. Both resulting shores are connected and
every crossing edge has an endpoint in the original separator.

No planar embedding is used in this construction. In maximum degree d
the complete edge boundary has at most d times the separator size. The
terminal sets may intersect the separator. The intended terminals are
the complete primal contours, not chosen local portions of them.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexSeparatorBond

variable {V : Type*} (G : SimpleGraph V)

/-- Reach the seeds using only vertices in the allowed set. -/
def flood (allowed seeds : Set V) : Set V :=
  {v | ∃ a ∈ seeds, ∃ p : G.Walk a v, ∀ x ∈ p.support, x ∈ allowed}

theorem flood_subset (U A : Set V) : flood G U A ⊆ U := by
  rintro v ⟨a, ha, p, hp⟩
  exact hp v p.end_mem_support

theorem mem_flood (U A : Set V) {v : V} (hU : v ∈ U) (hA : v ∈ A) :
    v ∈ flood G U A := ⟨v, hA, .nil, by simpa using hU⟩

theorem flood_adj {U A : Set V} {v w : V} (hv : v ∈ flood G U A)
    (hvw : G.Adj v w) (hw : w ∈ U) : w ∈ flood G U A := by
  obtain ⟨a, ha, p, hp⟩ := hv
  refine ⟨a, ha, p.concat hvw, ?_⟩
  intro x hx
  simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hp x hx
  · exact hw

theorem support_subset_flood {U A : Set V} {a v : V} (ha : a ∈ A)
    (p : G.Walk a v) (hp : ∀ x ∈ p.support, x ∈ U) :
    ∀ x ∈ p.support, x ∈ flood G U A := by
  classical
  intro x hx
  exact ⟨a, ha, p.takeUntil x hx,
    fun y hy => hp y (p.support_takeUntil_subset_support hx hy)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Lift an induced walk without losing its support restriction. -/
theorem exists_walk_in {S : Set V} (hS : (G.induce S).Connected)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
    ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∈ S := by
  obtain ⟨p⟩ := hS ⟨u, hu⟩ ⟨v, hv⟩
  refine ⟨p.map (SimpleGraph.Embedding.induce S).toHom, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact y.property

theorem connected_of_walks {S : Set V} {a : V} (ha : a ∈ S)
    (hwalk : ∀ v ∈ S, ∃ p : G.Walk a v, ∀ x ∈ p.support, x ∈ S) :
    (G.induce S).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨a, ha⟩, ?_⟩
  intro v
  obtain ⟨p, hp⟩ := hwalk v v.property
  exact ⟨p.induce S hp⟩

theorem flood_singleton_connected {U : Set V} {b : V} (hb : b ∈ U) :
    (G.induce (flood G U {b})).Connected := by
  apply connected_of_walks G (mem_flood G U {b} hb (by simp))
  rintro v ⟨a, ha, p, hp⟩
  obtain rfl : a = b := ha
  exact ⟨p, support_subset_flood G (by simp) p hp⟩

/-- Restoring the connected seed set connects all its flooded components. -/
theorem basin_connected (U A : Set V) (hA : (G.induce A).Connected) :
    (G.induce (A ∪ flood G U A)).Connected := by
  obtain ⟨a⟩ := hA.nonempty
  apply connected_of_walks G (Set.mem_union_left _ a.property)
  intro v hv
  rcases hv with hv | ⟨b, hb, p, hp⟩
  · obtain ⟨q, hq⟩ := exists_walk_in G hA a.property hv
    exact ⟨q, fun x hx => Or.inl (hq x hx)⟩
  · obtain ⟨q, hq⟩ := exists_walk_in G hA a.property hb
    refine ⟨q.append p, ?_⟩
    intro x hx
    simp only [SimpleGraph.Walk.support_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inl (hq x hx)
    · exact Or.inr (support_subset_flood G hb p hp x (List.mem_of_mem_tail hx))

/-- Outside a complementary component, a walk to S first reaches S
without entering that component. -/
theorem exists_first_hit_avoiding {S : Set V} {b u v : V}
    (p : G.Walk u v) (hv : v ∈ S) (hu : u ∉ flood G Sᶜ {b}) :
    ∃ z ∈ S, ∃ q : G.Walk u z, ∀ x ∈ q.support, x ∉ flood G Sᶜ {b} := by
  classical
  induction p with
  | nil => exact ⟨_, hv, .nil, by simpa using hu⟩
  | @cons u w v hadj p ih =>
    by_cases huS : u ∈ S
    · exact ⟨u, huS, .nil, by simpa using hu⟩
    have hw : w ∉ flood G Sᶜ {b} := by
      intro h
      exact hu (flood_adj G h hadj.symm huS)
    obtain ⟨z, hz, q, hq⟩ := ih hv hw
    refine ⟨z, hz, q.cons hadj, ?_⟩
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · exact hq x hx

/-- Filling all but one complementary component preserves connectedness. -/
theorem filled_connected (hG : G.Connected) {S : Set V}
    (hS : (G.induce S).Connected) (b : V) :
    (G.induce (flood G Sᶜ {b})ᶜ).Connected := by
  obtain ⟨a⟩ := hS.nonempty
  have hsub : S ⊆ (flood G Sᶜ {b})ᶜ := by
    intro v hv hf
    exact flood_subset G Sᶜ {b} hf hv
  apply connected_of_walks G (hsub a.property)
  intro v hv
  obtain ⟨p⟩ := hG v a
  obtain ⟨z, hz, q, hq⟩ := exists_first_hit_avoiding G p a.property hv
  obtain ⟨r, hr⟩ := exists_walk_in G hS hz a.property
  refine ⟨(q.append r).reverse, ?_⟩
  intro x hx
  simp only [SimpleGraph.Walk.support_reverse, List.mem_reverse,
    SimpleGraph.Walk.support_append, List.mem_append] at hx
  rcases hx with hx | hx
  · exact hq x hx
  · exact hsub (hr x (List.mem_of_mem_tail hx))

/-- Every terminal-to-terminal walk meets X, also at its endpoints. -/
def Separates (A B X : Set V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ x ∈ p.support, x ∈ X

/-- A separator constructs both connected shores, retaining ALL terminals
and all ambient crossing edges. No shore or connectivity witness is supplied. -/
theorem exists_bond_of_separator (hG : G.Connected) {A B X : Set V}
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    (hAB : Disjoint A B) (hX : Separates G A B X) :
    ∃ S : Set V, A ⊆ S ∧ B ⊆ Sᶜ ∧
      (G.induce S).Connected ∧ (G.induce Sᶜ).Connected ∧
      ∀ u v, G.Adj u v → u ∈ S → v ∉ S → u ∈ X ∨ v ∈ X := by
  classical
  let C := A ∪ flood G Xᶜ A
  have hBC : B ⊆ Cᶜ := by
    intro b hb hc
    rcases hc with ha | ⟨a, ha, p, hp⟩
    · exact Set.disjoint_left.mp hAB ha hb
    · obtain ⟨x, hx, hxx⟩ := hX a ha b hb p
      exact hp x hx hxx
  obtain ⟨b⟩ := hB.nonempty
  let R := flood G Cᶜ {b.val}
  have hBR : B ⊆ R := by
    intro v hv
    obtain ⟨p, hp⟩ := exists_walk_in G hB b.property hv
    exact ⟨b, by simp, p, fun x hx => hBC (hp x hx)⟩
  have hCR : C ⊆ Rᶜ := by
    intro v hv hr
    exact flood_subset G Cᶜ {b.val} hr hv
  refine ⟨Rᶜ, fun v hv => hCR (Or.inl hv), ?_,
    filled_connected G hG (basin_connected G Xᶜ A hA) b.val, ?_, ?_⟩
  · simpa using hBR
  · rw [compl_compl]
    exact flood_singleton_connected G (hBC b.property)
  · intro u v huv hu hv
    have hvR : v ∈ R := by simpa using hv
    have huC : u ∈ C := by
      by_contra hn
      exact hu (flood_adj G hvR huv.symm hn)
    by_cases huX : u ∈ X
    · exact Or.inl huX
    right
    by_contra hvX
    have huF : u ∈ flood G Xᶜ A := by
      rcases huC with huA | huF
      · exact mem_flood G Xᶜ A huX huA
      · exact huF
    exact hCR (Or.inr (flood_adj G huF huv hvX)) hvR

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The entire undirected edge boundary on the original graph carrier. -/
noncomputable def edgeBoundary (S : Set V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e => ∃ u ∈ e, u ∈ S ∧ ∃ v ∈ e, v ∉ S

theorem edgeBoundary_card_le {S : Set V} (X : Finset V) (d : ℕ)
    (hdegree : ∀ v ∈ X, G.degree v ≤ d)
    (hcross : ∀ u v, G.Adj u v → u ∈ S → v ∉ S → u ∈ X ∨ v ∈ X) :
    (edgeBoundary G S).card ≤ d * X.card := by
  classical
  have hsub : edgeBoundary G S ⊆ X.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    obtain ⟨he, u, hue, hu, v, hve, hv⟩ := Finset.mem_filter.mp he
    have heG := G.mem_edgeFinset.mp he
    have huI : e ∈ G.incidenceSet u :=
      (G.edge_mem_incidenceSet_iff (e := ⟨e, heG⟩)).mpr hue
    have hvI : e ∈ G.incidenceSet v :=
      (G.edge_mem_incidenceSet_iff (e := ⟨e, heG⟩)).mpr hve
    have hne : u ≠ v := by rintro rfl; exact hv hu
    rcases hcross u v (G.adj_of_mem_incidenceSet hne huI hvI) hu hv with h | h
    · exact Finset.mem_biUnion.mpr ⟨u, h, (G.mem_incidenceFinset u e).mpr huI⟩
    · exact Finset.mem_biUnion.mpr ⟨v, h, (G.mem_incidenceFinset v e).mpr hvI⟩
  calc
    (edgeBoundary G S).card ≤ (X.biUnion (fun v => G.incidenceFinset v)).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ X, (G.incidenceFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ X, G.degree v := by simp
    _ ≤ ∑ _v ∈ X, d := Finset.sum_le_sum hdegree
    _ = d * X.card := by simp [Nat.mul_comm]

/-- The full bounded bond is constructed from a vertex separator. -/
theorem exists_bounded_bond (hG : G.Connected) {A B : Set V}
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    (hAB : Disjoint A B) (X : Finset V) (hX : Separates G A B X)
    (d : ℕ) (hdegree : ∀ v ∈ X, G.degree v ≤ d) :
    ∃ S : Set V, A ⊆ S ∧ B ⊆ Sᶜ ∧
      (G.induce S).Connected ∧ (G.induce Sᶜ).Connected ∧
      (edgeBoundary G S).card ≤ d * X.card := by
  obtain ⟨S, hAS, hBS, hS, hSc, hcross⟩ :=
    exists_bond_of_separator G hG hA hB hAB hX
  exact ⟨S, hAS, hBS, hS, hSc, edgeBoundary_card_le G X d hdegree hcross⟩

end Finite

end Mettapedia.GraphTheory.FourColor.VertexSeparatorBond
