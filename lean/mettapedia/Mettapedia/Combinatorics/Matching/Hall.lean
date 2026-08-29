import Mettapedia.Combinatorics.Matching.Sum

/-!
# Hall bounds for weighted perfect-matching sums

If a subset has no live internal edge, every nonzero matching term must send
that subset injectively into live neighbours outside it. This is Hall's
cardinality condition derived directly from a contributing perfect matching.
-/

namespace MatchingHall

open Amplitude MatchingSum

variable {V C R : Type*} [DecidableEq V] [CommSemiring R]

open Classical in
/-- The live partners outside `A`, relative to the matching problem on `S`. -/
noncomputable def liveOut (W : Sym2 (V × C) → R) (c : V → C)
    (S A : Finset V) : Finset V :=
  (S \ A).filter (fun y => ∃ x ∈ A, W (Sym2.map (paint c) s(x, y)) ≠ 0)

theorem mem_liveOut {W : Sym2 (V × C) → R} {c : V → C}
    {S A : Finset V} {y : V} :
    y ∈ liveOut W c S A ↔
      y ∈ S \ A ∧ ∃ x ∈ A, W (Sym2.map (paint c) s(x, y)) ≠ 0 := by
  classical
  simp [liveOut, Finset.mem_filter]

theorem liveOut_subset (W : Sym2 (V × C) → R) (c : V → C)
    (S A : Finset V) : liveOut W c S A ⊆ S \ A :=
  fun _ hy => (mem_liveOut.mp hy).1

variable [Fintype V] [NoZeroDivisors R] [Nontrivial R]

/-- If every pair inside `A` is dead, a nonzero matching term injects `A`
into its live neighbourhood outside. -/
theorem card_le_card_liveOut (W : Sym2 (V × C) → R) (c : V → C)
    {S A : Finset V} (hAS : A ⊆ S)
    (hdead : ∀ x ∈ A, ∀ y ∈ A, y ≠ x →
      W (Sym2.map (paint c) s(x, y)) = 0)
    (hne : pmSum W c S ≠ 0) :
    A.card ≤ (liveOut W c S A).card := by
  classical
  rw [pmSum] at hne
  obtain ⟨σ, hσ, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hfac := Finset.prod_ne_zero_iff.mp hprod
  have hlive : ∀ x ∈ A, W (Sym2.map (paint c) s(x, σ x)) ≠ 0 := fun x hx =>
    hfac _ (Finset.mem_image.mpr ⟨x, hAS hx, rfl⟩)
  have hmap : ∀ x ∈ A, σ x ∈ liveOut W c S A := by
    intro x hx
    have hout : σ x ∉ A := by
      intro hin
      exact hlive x hx (hdead x hx (σ x) hin ((mem_pairingsOn.mp hσ).2.1 x (hAS hx)))
    refine mem_liveOut.mpr ⟨Finset.mem_sdiff.mpr
      ⟨pairingsOn_closed hσ x (hAS hx), hout⟩, ?_⟩
    exact ⟨x, hx, hlive x hx⟩
  exact Finset.card_le_card_of_injOn (fun x => σ x) hmap
    (fun a _ b _ h => σ.injective h)

/-- An internally dead set occupies at most half of the matching domain. -/
theorem card_le_card_compl_of_internal_dead (W : Sym2 (V × C) → R)
    (c : V → C) {S A : Finset V} (hAS : A ⊆ S)
    (hdead : ∀ x ∈ A, ∀ y ∈ A, y ≠ x →
      W (Sym2.map (paint c) s(x, y)) = 0)
    (hne : pmSum W c S ≠ 0) :
    A.card ≤ (S \ A).card :=
  (card_le_card_liveOut W c hAS hdead hne).trans
    (Finset.card_le_card (liveOut_subset W c S A))

/-- If an internally dead set has too few outside vertices, the matching sum vanishes. -/
theorem pmSum_eq_zero_of_internal_dead (W : Sym2 (V × C) → R)
    (c : V → C) {S A : Finset V} (hAS : A ⊆ S)
    (hdead : ∀ x ∈ A, ∀ y ∈ A, y ≠ x →
      W (Sym2.map (paint c) s(x, y)) = 0)
    (hroom : (S \ A).card < A.card) :
    pmSum W c S = 0 := by
  by_contra hne
  exact absurd (card_le_card_compl_of_internal_dead W c hAS hdead hne) (by omega)

end MatchingHall
