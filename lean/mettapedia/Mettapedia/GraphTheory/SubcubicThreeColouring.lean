import Mettapedia.GraphTheory.SubcubicCycleExtension
import Mettapedia.GraphTheory.FiniteDegree
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Brooks' theorem for finite subcubic graphs

Low-degree insertion, coupled full-path closing, and an exterior-preserving
selected-region extension share one three-colour mechanism. The maximal
path and closing region are selected from actual graph adjacency. No
table of colour words or vertex-connectivity assumption is used.

The proof specializes M. Zając, *A short proof of Brooks' theorem* (2018),
arXiv:1805.11176, Theorem 1, to maximum degree three.
-/

namespace Mettapedia.GraphTheory.SubcubicThreeColouring

open SimpleGraph Finset SubcubicPathSelection SubcubicCycleExtension
noncomputable section

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Induction preserves the actual simple-degree bound. -/
theorem degree_induce_le (s : Set V) [DecidablePred (· ∈ s)] (v : s) :
    (G.induce s).degree v ≤ G.degree v := by
  classical
  have h := Finset.card_le_card (Finset.inter_subset_left
    (s₁ := G.neighborFinset v) (s₂ := s.toFinset))
  rw [← G.map_neighborFinset_induce v, Finset.card_map] at h
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using h

theorem cliqueFree_induce (hfree : G.CliqueFree 4) (s : Set V) :
    (G.induce s).CliqueFree 4 := by
  classical
  intro t ht
  exact hfree _ ((G.isNClique_induce_iff s t 4).mp ht)

theorem nonadjacent_neighbours {r : V} (hdeg : G.degree r = 3)
    (hfree : G.CliqueFree 4) :
    ∃ a b, a ≠ b ∧ ¬G.Adj a b ∧ G.Adj r a ∧ G.Adj r b := by
  classical
  by_contra hn
  have hcl : G.IsNClique 3 (G.neighborFinset r) := by
    refine ⟨?_, by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg⟩
    intro a ha b hb hab
    by_contra hnadj
    exact hn ⟨a, b, hab, hnadj, by simpa using ha, by simpa using hb⟩
  exact hfree _ (hcl.insert (fun w hw => by simpa using hw))

theorem third_neighbour {a b r : V} (hdeg : G.degree r = 3) (hab : a ≠ b) :
    ∃ u, G.Adj r u ∧ u ≠ a ∧ u ≠ b := by
  classical
  by_contra hn
  have hsub : G.neighborFinset r ⊆ {a, b} := by
    intro w hw
    by_cases hwa : w = a
    · simp [hwa]
    · by_cases hwb : w = b
      · simp [hwb]
      · exact (hn ⟨w, by simpa using hw, hwa, hwb⟩).elim
  have hc := Finset.card_le_card hsub
  simp only [SimpleGraph.card_neighborFinset_eq_degree, hdeg, Finset.card_pair hab] at hc
  omega

/-- Colourings on a partition combine when there are no crossing edges. -/
def combine (s : Finset V)
    (inside : (G.induce {v | v ∈ s}).Coloring (Fin 3))
    (outside : (G.induce {v | v ∉ s}).Coloring (Fin 3))
    (hcross : ∀ x y, x ∈ s → y ∉ s → ¬G.Adj x y) : G.Coloring (Fin 3) := by
  classical
  let c : V → Fin 3 := fun v => if hv : v ∈ s then inside ⟨v, hv⟩ else outside ⟨v, hv⟩
  apply Coloring.mk c
  intro x y hxy
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
  · simpa [c, hx, hy] using inside.valid
      (show (G.induce {v | v ∈ s}).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
  · exact (hcross x y hx hy hxy).elim
  · exact (hcross y x hy hx hxy.symm).elim
  · simpa [c, hx, hy] using outside.valid
      (show (G.induce {v | v ∉ s}).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)

/-- Every finite simple graph with degree at most three and no four-clique
admits three vertex colours. Connectivity is not an extra hypothesis. -/
theorem colourable (hdeg : ∀ v, G.degree v ≤ 3) (hfree : G.CliqueFree 4) :
    G.Colorable 3 := by
  classical
  have main : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Fintype.card W = n →
      (∀ v, H.degree v ≤ 3) → H.CliqueFree 4 → H.Colorable 3 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H _ hn hd hf
      by_cases hsmall : n ≤ 3
      · exact Colorable.mono (hn ▸ hsmall) H.colorable_of_fintype
      by_cases hlow : ∃ v, H.degree v < 3
      · obtain ⟨v, hv⟩ := hlow
        let s : Set W := {w | w ≠ v}
        have hcard : Fintype.card s < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := v) (by simp [s])
        obtain ⟨outside⟩ := ih (Fintype.card s) hcard s (H.induce s) rfl
          (fun w => (degree_induce_le H s w).trans (hd w)) (cliqueFree_induce H hf s)
        obtain ⟨c, _⟩ := OrderedBoundaryColouring.low_degree_extension H hv outside
        exact ⟨c⟩
      have hreg : ∀ v, H.degree v = 3 := by
        intro v
        have hv := hd v
        have hl : ¬H.degree v < 3 := fun h => hlow ⟨v, h⟩
        omega
      have hpos : 0 < Fintype.card W := by omega
      obtain ⟨r⟩ := Fintype.card_pos_iff.mp hpos
      obtain ⟨a, b, hab, hnadj, har, hbr⟩ := nonadjacent_neighbours H (hreg r) hf
      obtain ⟨m, p, hclosed⟩ := exists_maximal H hab har hbr
      by_cases hcover : ∀ w, w ∈ p.vertices
      · obtain ⟨u, hru, hua, hub⟩ := third_neighbour H (hreg r) hab
        obtain ⟨j, hjm, hju⟩ := (p.mem_vertices u).mp (hcover u)
        have hj : 3 ≤ j := by
          have hj0 : j ≠ 0 := by intro h; apply hua; simpa [h, p.first] using hju.symm
          have hj1 : j ≠ 1 := by intro h; exact hru.ne (by simpa [h, p.second] using hju)
          have hj2 : j ≠ 2 := by intro h; apply hub; simpa [h, p.third] using hju.symm
          omega
        have hrj : H.Adj r (p.vertex j) := hju ▸ hru
        obtain ⟨c, _⟩ := CoupledThreeColouring.colouring_of_coupledOrder H
          (fullPathOrder H p hcover hj hjm hrj) hd hnadj har hbr
        exact ⟨c⟩
      · obtain ⟨w, hw⟩ : ∃ w, w ∉ p.vertices := by simpa using hcover
        let Q : ℕ → Prop := fun k => k < m ∧ H.Adj (p.vertex (m - 1)) (p.vertex k)
        have hm := p.three_le
        have hQ : ∃ k, Q k := by
          refine ⟨m - 2, by omega, ?_⟩
          have he : m - 2 + 1 = m - 1 := by omega
          simpa only [he] using (p.step (m - 2) (by omega)).symm
        let j := Nat.find hQ
        have hjm : j < m := (Nat.find_spec hQ).1
        have hclose : H.Adj (p.vertex (m - 1)) (p.vertex j) := (Nat.find_spec hQ).2
        have hjlast : j ≠ m - 1 := by
          intro he
          exact H.irrefl (he ▸ hclose)
        have hjn : j + 1 < m := by omega
        let s := SubcubicCycleExtension.StartedPath.tailVertices p j
        have hjmem : p.vertex j ∈ s :=
          (SubcubicCycleExtension.StartedPath.mem_tailVertices p j _).mpr ⟨j, le_rfl, hjm, rfl⟩
        have hwout : w ∉ s := fun h => hw (SubcubicCycleExtension.StartedPath.tailVertices_subset p j h)
        have hend : ∀ u, H.Adj (p.vertex (m - 1)) u → u ∈ s := by
          intro u hu
          obtain ⟨k, hkm, hku⟩ := (p.mem_vertices u).mp (hclosed u hu)
          have hq : Q k := ⟨hkm, by simpa only [hku] using hu⟩
          exact (SubcubicCycleExtension.StartedPath.mem_tailVertices p j _).mpr
            ⟨k, Nat.find_min' hQ hq, hkm, hku⟩
        have hcOut : Fintype.card {v : W // v ∉ s} < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := p.vertex j) (fun h => h hjmem)
        obtain ⟨outside⟩ := ih _ hcOut {v : W // v ∉ s}
          (H.induce {v | v ∉ s}) rfl
          (fun v => (degree_induce_le H {v | v ∉ s} v).trans (hd v))
          (cliqueFree_induce H hf {v | v ∉ s})
        let P : ℕ → Prop := fun k => j ≤ k ∧ k < m ∧ ∃ u, u ∉ s ∧ H.Adj (p.vertex k) u
        by_cases hex : ∃ k, P k
        · obtain ⟨k, hk⟩ := hex
          let l := Nat.findGreatest P (m - 1)
          have hl : P l := Nat.findGreatest_spec (by have := hk.2.1; omega) hk
          obtain ⟨hjl, hlm, u, hu, hlu⟩ := hl
          have hlast : l ≠ m - 1 := by
            intro he
            exact hu (hend u (by simpa only [he] using hlu))
          have hln : l + 1 < m := by omega
          have hseed : ∀ x, H.Adj (p.vertex (l + 1)) x → x ∈ s := by
            intro x hx
            by_contra hxo
            have hp : P (l + 1) := ⟨by omega, hln, x, hxo, hx⟩
            have hbad : l + 1 ≤ l := Nat.le_findGreatest (by omega) hp
            omega
          obtain ⟨c, _⟩ := selected_tail_extension H p hjl hln hclose hu hlu hseed hd outside
          exact ⟨c⟩
        · have hcIn : Fintype.card {v : W // v ∈ s} < n := by
            rw [← hn]
            exact Fintype.card_subtype_lt hwout
          obtain ⟨inside⟩ := ih _ hcIn {v : W // v ∈ s}
            (H.induce {v | v ∈ s}) rfl
            (by
              intro v
              exact (SimpleGraph.degree_instance_independent
                (G := H.induce {v | v ∈ s}) v _ _).trans_le
                ((degree_induce_le H {v | v ∈ s} v).trans (hd v)))
            (cliqueFree_induce H hf {v | v ∈ s})
          refine ⟨combine H s inside outside ?_⟩
          intro x y hx hy hxy
          obtain ⟨k, hjk, hkm, hke⟩ :=
            (SubcubicCycleExtension.StartedPath.mem_tailVertices p j x).mp hx
          exact hex ⟨k, hjk, hkm, y, hy, hke ▸ hxy⟩
  exact main (Fintype.card V) V G rfl hdeg hfree

end
end Mettapedia.GraphTheory.SubcubicThreeColouring
