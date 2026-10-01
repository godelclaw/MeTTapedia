import Mettapedia.GraphTheory.SubcubicPathSelection

/-!
# A selected closed path extends a coloured exterior

The region may have chords. One seed has no exterior neighbours; its
colour is copied from an exterior neighbour of the closing vertex.
An explicit order traverses the rest of the closed path and preserves
every supplied exterior colour. This formalizes the relative branch in
M. Zając, *A short proof of Brooks' theorem* (2018), arXiv:1805.11176.
-/

namespace Mettapedia.GraphTheory.SubcubicCycleExtension

open SimpleGraph Finset SubcubicPathSelection OrderedBoundaryColouring
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

namespace StartedPath

variable {G} {a r b : V} {n : ℕ}

def tailVertices (p : SubcubicPathSelection.StartedPath G a r b n) (j : ℕ) : Finset V :=
  ((Finset.range n).filter (fun i => j ≤ i)).image p.vertex

theorem mem_tailVertices (p : SubcubicPathSelection.StartedPath G a r b n) (j : ℕ) (v : V) :
    v ∈ tailVertices p j ↔ ∃ i, j ≤ i ∧ i < n ∧ p.vertex i = v := by
  simp only [tailVertices, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  aesop

theorem tailVertices_subset (p : SubcubicPathSelection.StartedPath G a r b n) (j : ℕ) :
    tailVertices p j ⊆ p.vertices := by
  intro v hv
  obtain ⟨i, _, hi, he⟩ := (mem_tailVertices p j v).mp hv
  exact (p.mem_vertices v).mpr ⟨i, hi, he⟩

/-- A closed path supplies the relative insertion order even with chords.
The seed at `l+1` is excluded; the order traverses the two retained arcs. -/
def tailOrder (p : SubcubicPathSelection.StartedPath G a r b n) {j l : ℕ}
    (hjl : j ≤ l) (hln : l + 1 < n)
    (hclose : G.Adj (p.vertex (n - 1)) (p.vertex j)) :
    CoupledRegionOrder G (tailVertices p j) (p.vertex (l + 1)) (p.vertex l) := by
  classical
  let s := tailVertices p j
  have hmem (i : ℕ) (hji : j ≤ i) (hin : i < n) : p.vertex i ∈ s :=
    (mem_tailVertices p j _).mpr ⟨i, hji, hin, rfl⟩
  let idx : V → ℕ := fun v => if h : v ∈ s then
    Classical.choose ((mem_tailVertices p j v).mp h) else 0
  have spec : ∀ v, v ∈ s → j ≤ idx v ∧ idx v < n ∧ p.vertex (idx v) = v := by
    intro v hv
    simpa only [idx, dite_eq_left hv] using
      Classical.choose_spec ((mem_tailVertices p j v).mp hv)
  have index : ∀ i, j ≤ i → i < n → idx (p.vertex i) = i := by
    intro i hji hin
    obtain ⟨_, hk, he⟩ := spec _ (hmem i hji hin)
    exact p.injective _ _ hk hin he
  let f : ℕ → ℕ := fun i =>
    if i ≤ l then (n - l - 2) + (i - j) else i - l - 2
  refine ⟨fun v => f (idx v), ?_, ?_⟩
  · intro x y hx hy hxb hyb he
    obtain ⟨hxj, hxn, hxe⟩ := spec x hx
    obtain ⟨hyj, hyn, hye⟩ := spec y hy
    have hxs : idx x ≠ l + 1 := by intro h; apply hxb; simpa [h] using hxe.symm
    have hys : idx y ≠ l + 1 := by intro h; apply hyb; simpa [h] using hye.symm
    have hidx : idx x = idx y := by
      simp only [f] at he
      split_ifs at he <;> omega
    exact hxe.symm.trans (hidx ▸ hye)
  · intro v hv hvb hvr
    obtain ⟨hij, hin, hev⟩ := spec v hv
    let i := idx v
    change j ≤ i at hij
    change i < n at hin
    change p.vertex i = v at hev
    have his : i ≠ l + 1 := by intro h; apply hvb; simpa [← h] using hev.symm
    have hir : i ≠ l := by intro h; apply hvr; simpa [← h] using hev.symm
    have hne : ∀ k, k < n → k ≠ l + 1 → p.vertex k ≠ p.vertex (l + 1) := by
      intro k hk hks he
      exact hks (p.injective k (l + 1) hk hln he)
    by_cases hil : i < l
    · refine ⟨p.vertex (i + 1), hmem _ (by omega) (by omega),
        hne _ (by omega) (by omega), ?_, ?_⟩
      · simpa [show p.vertex i = v from hev] using p.step i (by omega)
      · rw [index (i + 1) (by omega) (by omega)]
        change f i < f (i + 1)
        clear_value i
        simp only [f]; split_ifs <;> omega
    · by_cases hend : i + 1 = n
      · refine ⟨p.vertex j, hmem _ le_rfl (by omega),
          hne _ (by omega) (by omega), ?_, ?_⟩
        · have hi : i = n - 1 := by omega
          have he : p.vertex (n - 1) = v := by simpa only [hi] using hev
          exact he ▸ hclose
        · rw [index j le_rfl (by omega)]
          change f i < f j
          clear_value i
          simp only [f]; split_ifs <;> omega
      · refine ⟨p.vertex (i + 1), hmem _ (by omega) (by omega),
          hne _ (by omega) (by omega), ?_, ?_⟩
        · simpa [show p.vertex i = v from hev] using p.step i (by omega)
        · rw [index (i + 1) (by omega) (by omega)]
          change f i < f (i + 1)
          clear_value i
          simp only [f]; split_ifs <;> omega

end StartedPath

/-- All exterior colourings extend across the selected region with the
one coupled seed choice retained. -/
theorem selected_tail_extension {a r b u : V} {n j l : ℕ}
    (p : SubcubicPathSelection.StartedPath G a r b n)
    (hjl : j ≤ l) (hln : l + 1 < n)
    (hclose : G.Adj (p.vertex (n - 1)) (p.vertex j))
    (hu : u ∉ StartedPath.tailVertices p j)
    (hroot : G.Adj (p.vertex l) u)
    (hseed : ∀ w, G.Adj (p.vertex (l + 1)) w → w ∈ StartedPath.tailVertices p j)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (outside : (G.induce {v | v ∉ StartedPath.tailVertices p j}).Coloring (Fin 3)) :
    ∃ c : G.Coloring (Fin 3), c (p.vertex (l + 1)) = outside ⟨u, hu⟩ ∧
      ∀ w (hw : w ∉ StartedPath.tailVertices p j), c w = outside ⟨w, hw⟩ := by
  apply coupled_region_extension G (StartedPath.tailVertices p j)
    ((StartedPath.mem_tailVertices p j _).mpr ⟨l + 1, by omega, hln, rfl⟩)
    hu hseed hroot (p.step l hln) (StartedPath.tailOrder p hjl hln hclose) hdeg outside

end
end Mettapedia.GraphTheory.SubcubicCycleExtension
