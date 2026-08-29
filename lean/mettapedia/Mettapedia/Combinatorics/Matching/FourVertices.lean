import Mettapedia.Combinatorics.Matching.Sum

/-!
# Perfect matchings on four vertices

A perfect matching on four distinct vertices is one of the three pairings.
The classification applies both to `pairingsOn` and to a global fixed-point-free
involution that preserves the four-vertex set. The final lemmas turn the
classification into reusable zero-edge criteria.
-/

namespace MatchingFourVertices

open Amplitude MatchingSum

variable {V : Type*} [DecidableEq V]

/-- Four distinct vertices preserved by a fixed-point-free involution are
paired in one of the three possible ways. -/
theorem pairing_four_cases {a b x y : V}
    (hab : a ≠ b) (hax : a ≠ x) (_hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (_hxy : x ≠ y)
    {σ : Equiv.Perm V} (hinv : ∀ z, σ (σ z) = z)
    (hne : ∀ z ∈ ({a, b, x, y} : Finset V), σ z ≠ z)
    (hmap : ∀ z ∈ ({a, b, x, y} : Finset V), σ z ∈ ({a, b, x, y} : Finset V)) :
    (σ a = b ∧ σ x = y) ∨ (σ a = x ∧ σ b = y) ∨ (σ a = y ∧ σ b = x) := by
  classical
  have hmem : ∀ z : V, z ∈ ({a, b, x, y} : Finset V) ↔ z = a ∨ z = b ∨ z = x ∨ z = y := by
    intro z
    simp
  have ha : a ∈ ({a, b, x, y} : Finset V) := by simp
  have hb : b ∈ ({a, b, x, y} : Finset V) := by simp
  have hx : x ∈ ({a, b, x, y} : Finset V) := by simp
  rcases (hmem (σ a)).mp (hmap a ha) with h | h | h | h
  · exact absurd h (hne a ha)
  · left
    refine ⟨h, ?_⟩
    have hsb : σ b = a := by rw [← h, hinv]
    rcases (hmem (σ x)).mp (hmap x hx) with h' | h' | h' | h'
    · exact absurd (by rw [← h', hinv] : σ a = x) (by rw [h]; exact hbx)
    · exact absurd (by rw [← h', hinv] : σ b = x) (by rw [hsb]; exact hax)
    · exact absurd h' (hne x hx)
    · exact h'
  · right
    left
    refine ⟨h, ?_⟩
    have hsx : σ x = a := by rw [← h, hinv]
    rcases (hmem (σ b)).mp (hmap b hb) with h' | h' | h' | h'
    · exact absurd (by rw [← h', hinv] : σ a = b) (by rw [h]; exact Ne.symm hbx)
    · exact absurd h' (hne b hb)
    · exact absurd (by rw [← h', hinv] : σ x = b) (by rw [hsx]; exact hab)
    · exact h'
  · right
    right
    refine ⟨h, ?_⟩
    have hsy : σ y = a := by rw [← h, hinv]
    rcases (hmem (σ b)).mp (hmap b hb) with h' | h' | h' | h'
    · exact absurd (by rw [← h', hinv] : σ a = b) (by rw [h]; exact Ne.symm hby)
    · exact absurd h' (hne b hb)
    · exact h'
    · exact absurd (by rw [← h', hinv] : σ y = b) (by rw [hsy]; exact hab)

/-- A member of `pairingsOn` for four distinct vertices is one of the three
possible pairings. -/
theorem pairingOn_four_cases [Fintype V] {a b x y : V}
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    {σ : Equiv.Perm V} (hσ : σ ∈ pairingsOn ({a, b, x, y} : Finset V)) :
    (σ a = b ∧ σ x = y) ∨ (σ a = x ∧ σ b = y) ∨ (σ a = y ∧ σ b = x) := by
  obtain ⟨hinv, hne, -⟩ := mem_pairingsOn.mp hσ
  exact pairing_four_cases hab hax hay hbx hby hxy hinv hne
    (fun z hz => pairingsOn_closed hσ z hz)

/-- If both alternatives to a distinguished four-vertex pairing contain a
zero-weight edge, every different pairing contains a zero-weight edge. -/
theorem zero_edge_of_pairingOn_four_ne [Fintype V] {C R : Type*} [Zero R]
    (W : Sym2 (V × C) → R) (k : C)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (h1 : W s((a, k), (x, k)) = 0 ∨ W s((b, k), (y, k)) = 0)
    (h2 : W s((a, k), (y, k)) = 0 ∨ W s((b, k), (x, k)) = 0)
    {σ : Equiv.Perm V} (hσ : σ ∈ pairingsOn ({a, b, x, y} : Finset V))
    (hne : ¬ (σ a = b ∧ σ x = y)) :
    ∃ z ∈ ({a, b, x, y} : Finset V), W s((z, k), (σ z, k)) = 0 := by
  classical
  rcases pairingOn_four_cases hab hax hay hbx hby hxy hσ with
    h | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact absurd h hne
  · rcases h1 with h | h
    · exact ⟨a, by simp, by rw [hA]; exact h⟩
    · exact ⟨b, by simp, by rw [hB]; exact h⟩
  · rcases h2 with h | h
    · exact ⟨a, by simp, by rw [hA]; exact h⟩
    · exact ⟨b, by simp, by rw [hB]; exact h⟩

/-- The global-involution form of `zero_edge_of_pairingOn_four_ne`. -/
theorem zero_edge_of_pairing_four_ne {C R : Type*} [Zero R]
    (W : Sym2 (V × C) → R) (k : C)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (h1 : W s((a, k), (x, k)) = 0 ∨ W s((b, k), (y, k)) = 0)
    (h2 : W s((a, k), (y, k)) = 0 ∨ W s((b, k), (x, k)) = 0)
    {σ : Equiv.Perm V} (hinv : ∀ z, σ (σ z) = z) (hne : ∀ z, σ z ≠ z)
    (hmap : ∀ z ∈ ({a, b, x, y} : Finset V), σ z ∈ ({a, b, x, y} : Finset V))
    (hdiff : σ a ≠ b) :
    ∃ z ∈ ({a, b, x, y} : Finset V), W s((z, k), (σ z, k)) = 0 := by
  classical
  rcases pairing_four_cases hab hax hay hbx hby hxy hinv (fun z _ => hne z) hmap with
    ⟨hA, -⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact absurd hA hdiff
  · rcases h1 with h | h
    · exact ⟨a, by simp, by rw [hA]; exact h⟩
    · exact ⟨b, by simp, by rw [hB]; exact h⟩
  · rcases h2 with h | h
    · exact ⟨a, by simp, by rw [hA]; exact h⟩
    · exact ⟨b, by simp, by rw [hB]; exact h⟩

end MatchingFourVertices
