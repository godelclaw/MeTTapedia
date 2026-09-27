import Mettapedia.GraphTheory.Kempe.PairDecomposition
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Lifting three-colour Kempe histories across low-degree vertices

The low-degree argument of Las Vergnas and Meyniel, in a relative form:
the graph left after a deletion may be arbitrary. A smaller Kempe step
can be reproduced after restoring a vertex of degree at most two, with
an optional preliminary recolouring of that vertex.

See the proof of Lemma 1.1 in *Kempe changes in degenerate graphs*,
https://arxiv.org/abs/2112.02313. The finite palette calculation below
selects the preliminary and final colours; actual Kempe reachability
comes from the component decomposition theorem.
-/

namespace SimpleGraph.Coloring

private theorem bridge_colours : ∀ a b c p q p' q' : Fin 3,
    c ≠ p → c ≠ q →
    (p' = p ∨ p' = Equiv.swap a b p) →
    (q' = q ∨ q' = Equiv.swap a b q) →
    ∃ z z' : Fin 3, z ≠ p ∧ z ≠ q ∧ z' ≠ p' ∧ z' ≠ q' ∧
      (z' = z ∨ z' = Equiv.swap a b z) := by
  decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj]

private theorem two_neighbours {v : V} (hdeg : G.degree v ≤ 2)
    (hne : (G.neighborFinset v).Nonempty) :
    ∃ u w, G.Adj v u ∧ G.Adj v w ∧ ∀ x, G.Adj v x → x = u ∨ x = w := by
  obtain ⟨u, hu⟩ := hne
  by_cases hempty : (G.neighborFinset v).erase u = ∅
  · refine ⟨u, u, (G.mem_neighborFinset v _).mp hu, (G.mem_neighborFinset v _).mp hu, ?_⟩
    intro x hx
    left
    by_contra hxu
    have := Finset.mem_erase.mpr ⟨hxu, (G.mem_neighborFinset v _).mpr hx⟩
    simp [hempty] at this
  · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard : ((G.neighborFinset v).erase u).card ≤ 1 := by
      rw [Finset.card_erase_of_mem hu]
      change G.degree v - 1 ≤ 1
      omega
    refine ⟨u, w, (G.mem_neighborFinset v _).mp hu,
      (G.mem_neighborFinset v _).mp (Finset.mem_erase.mp hw).2, ?_⟩
    intro x hx
    by_cases hxu : x = u
    · exact Or.inl hxu
    · exact Or.inr (Finset.card_le_one.mp hcard x
        (Finset.mem_erase.mpr ⟨hxu, (G.mem_neighborFinset v _).mpr hx⟩) w hw)

/-- A proper partial transposition away from a low-degree vertex lifts to
old reachability. No connectedness assumption on either graph is used. -/
theorem partial_swap_lifts_vertex (v : V) (hdeg : G.degree v ≤ 2)
    (haway : ∀ x y, x ≠ v → y ≠ v → G.Adj x y → H.Adj x y)
    (old : G.Coloring (Fin 3)) (next : H.Coloring (Fin 3)) (a b : Fin 3)
    (hpair : ∀ x, x ≠ v → next x = old x ∨ next x = Equiv.swap a b (old x)) :
    ∃ final : G.Coloring (Fin 3), final ∈ G.KempeClosure old ∧
      ∀ x, x ≠ v → final x = next x := by
  classical
  have choose : ∃ z z' : Fin 3,
      (∀ x, G.Adj v x → z ≠ old x) ∧
      (∀ x, G.Adj v x → z' ≠ next x) ∧
      (z' = z ∨ z' = Equiv.swap a b z) := by
    by_cases hne : (G.neighborFinset v).Nonempty
    · obtain ⟨u, w, hu, hw, cover⟩ := two_neighbours hdeg hne
      obtain ⟨z, z', hzu, hzw, hz'u, hz'w, hzz'⟩ :=
        bridge_colours a b (old v) (old u) (old w) (next u) (next w)
          (old.valid hu) (old.valid hw) (hpair u hu.ne.symm) (hpair w hw.ne.symm)
      exact ⟨z, z', fun x hx => (cover x hx).elim (fun h => h ▸ hzu) (fun h => h ▸ hzw),
        fun x hx => (cover x hx).elim (fun h => h ▸ hz'u) (fun h => h ▸ hz'w), hzz'⟩
    · exact ⟨old v, old v, fun x hx => (hne ⟨x, (G.mem_neighborFinset v _).mpr hx⟩).elim,
        fun x hx => (hne ⟨x, (G.mem_neighborFinset v _).mpr hx⟩).elim, Or.inl rfl⟩
  obtain ⟨z, z', hz, hz', hzz'⟩ := choose
  let prepared : G.Coloring (Fin 3) := .mk (fun x => if x = v then z else old x) (by
    intro x y hxy
    by_cases hx : x = v <;> by_cases hy : y = v
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · simpa [hx, hy] using hz y (hx ▸ hxy)
    · simpa [hx, hy] using (hz x (hy ▸ hxy.symm)).symm
    · simpa [hx, hy] using old.valid hxy)
  let final : G.Coloring (Fin 3) := .mk (fun x => if x = v then z' else next x) (by
    intro x y hxy
    by_cases hx : x = v <;> by_cases hy : y = v
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · simpa [hx, hy] using hz' y (hx ▸ hxy)
    · simpa [hx, hy] using (hz' x (hy ▸ hxy.symm)).symm
    · simpa [hx, hy] using next.valid (haway x y hx hy hxy))
  have prepared_apply (x : V) : prepared x = (if x = v then z else old x) := rfl
  have final_apply (x : V) : final x = (if x = v then z' else next x) := rfl
  have hprep : prepared ∈ G.KempeClosure old := by
    apply old.mem_kempeClosure_of_pointwise_swap prepared (old v) z
    intro x
    by_cases hx : x = v
    · right
      simp [prepared_apply, hx]
    · left
      simp [prepared_apply, hx]
  have hfinal : final ∈ G.KempeClosure prepared := by
    apply prepared.mem_kempeClosure_of_pointwise_swap final a b
    intro x
    by_cases hx : x = v
    · simpa [prepared_apply, final_apply, hx] using hzz'
    · simpa [prepared_apply, final_apply, hx] using hpair x hx
  exact ⟨final, hprep.trans hfinal, fun x hx => by simp [final_apply, hx]⟩

/-- Restoring a vertex of degree at most two preserves every smaller
three-colour Kempe history, allowing several old switches per step. -/
theorem kempeClosure_lifts_vertex (v : V) (hdeg : G.degree v ≤ 2)
    (haway : ∀ x y, x ≠ v → y ≠ v → G.Adj x y → H.Adj x y)
    {C D : H.Coloring (Fin 3)} (history : D ∈ H.KempeClosure C)
    (old : G.Coloring (Fin 3)) (hold : ∀ x, x ≠ v → old x = C x) :
    ∃ final : G.Coloring (Fin 3), final ∈ G.KempeClosure old ∧
      ∀ x, x ≠ v → final x = D x := by
  induction history with
  | refl => exact ⟨old, .refl, hold⟩
  | @tail D next hpath step ih =>
    obtain ⟨middle, hmiddle, hagree⟩ := ih
    obtain ⟨a, b, K, rfl⟩ := step
    obtain ⟨final, hfinal, hlast⟩ := partial_swap_lifts_vertex v hdeg haway middle
      (D.swapOnKempeComponent a b K) a b (fun x hx => by
        rw [hagree x hx]
        by_cases hK : x ∈ D.kempeComponentSet a b K
        · exact Or.inr (D.swapOnKempeComponent_apply_of_mem hK)
        · exact Or.inl (D.swapOnKempeComponent_apply_of_not_mem hK))
    exact ⟨final, hmiddle.trans hfinal, hlast⟩

end SimpleGraph.Coloring
