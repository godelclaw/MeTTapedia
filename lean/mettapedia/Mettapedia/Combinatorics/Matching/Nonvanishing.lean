import Mettapedia.Combinatorics.Matching.Sum

/-!
# Structural nonvanishing criteria for weighted matching sums

A weighted perfect-matching sum cannot cancel when exactly one live matching
contributes. This module provides a local forced-partner criterion and the more
general criterion stated directly as uniqueness of the live matching.
-/

namespace MatchingNonvanishing

open Amplitude MatchingSum

variable {V C R : Type*} [Fintype V] [DecidableEq V]
  [CommSemiring R]

/-- If the live edges inside `F` form one prescribed perfect matching, its
matching sum is nonzero. -/
theorem pmSum_ne_zero_of_forced [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R) (c : V → C)
    {F : Finset V} (p : V → V) (hp : ∀ x ∈ F, p x ∈ F)
    (hinv : ∀ x ∈ F, p (p x) = x) (hpne : ∀ x ∈ F, p x ≠ x)
    (hlive : ∀ x ∈ F, W (Sym2.map (paint c) s(x, p x)) ≠ 0)
    (hunique : ∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ≠ p x →
      W (Sym2.map (paint c) s(x, y)) = 0) :
    pmSum W c F ≠ 0 := by
  classical
  set f : V → V := fun x => if x ∈ F then p x else x with hf
  have hinvol : Function.Involutive f := by
    intro x
    by_cases hx : x ∈ F
    · simp only [hf, if_pos hx, if_pos (hp x hx)]
      exact hinv x hx
    · simp only [hf, if_neg hx]
  set σ : Equiv.Perm V := hinvol.toPerm f with hσdef
  have hcoe : ∀ x, σ x = f x := fun x => rfl
  have hmem : σ ∈ pairingsOn F := by
    refine mem_pairingsOn.mpr ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hcoe, hcoe]
      exact hinvol x
    · rw [hcoe]
      simp only [hf, if_pos hx]
      exact hpne x hx
    · rw [hcoe]
      simp only [hf, if_neg hx]
  rw [pmSum, Finset.sum_eq_single_of_mem σ hmem]
  · refine Finset.prod_ne_zero_iff.mpr (fun e he => ?_)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    rw [hcoe]
    simp only [hf, if_pos hx]
    exact hlive x hx
  · intro τ hτ hne
    obtain ⟨x, hx⟩ : ∃ x, τ x ≠ σ x := by
      by_contra hall
      push Not at hall
      exact hne (Equiv.ext hall)
    have hxF : x ∈ F := by
      by_contra hout
      rw [(mem_pairingsOn.mp hτ).2.2 x hout, hcoe] at hx
      exact hx (by simp only [hf, if_neg hout])
    refine Finset.prod_eq_zero (i := s(x, τ x))
      (Finset.mem_image.mpr ⟨x, hxF, rfl⟩) ?_
    refine hunique x hxF (τ x) (pairingsOn_closed hτ x hxF)
      ((mem_pairingsOn.mp hτ).2.1 x hxF) ?_
    intro heq
    exact hx (by rw [heq, hcoe]; simp only [hf, if_pos hxF])

/-- A matching sum is nonzero when exactly one matching has all of its selected
edge weights nonzero. -/
theorem pmSum_ne_zero_of_unique_matching [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R)
    (c : V → C) {S : Finset V} {σ₀ : Equiv.Perm V}
    (hmem : σ₀ ∈ pairingsOn S)
    (hlive : ∀ z ∈ S, W (Sym2.map (paint c) s(z, σ₀ z)) ≠ 0)
    (huniq : ∀ τ ∈ pairingsOn S, τ ≠ σ₀ →
      ∃ z ∈ S, W (Sym2.map (paint c) s(z, τ z)) = 0) :
    pmSum W c S ≠ 0 := by
  classical
  rw [pmSum, Finset.sum_eq_single_of_mem σ₀ hmem]
  · refine Finset.prod_ne_zero_iff.mpr (fun e he => ?_)
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    exact hlive z hz
  · intro τ hτ hne
    obtain ⟨z, hz, hz0⟩ := huniq τ hτ hne
    exact Finset.prod_eq_zero (Finset.mem_image.mpr ⟨z, hz, rfl⟩) hz0

/-! ### A bounded number of contributing matchings -/

/-- A matching sum with only two live matchings is exactly the sum of their
two edge products. -/
theorem pmSum_eq_two_terms (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    {σ₀ σ₁ : Equiv.Perm V} (h₀ : σ₀ ∈ pairingsOn S) (h₁ : σ₁ ∈ pairingsOn S)
    (hne : σ₁ ≠ σ₀)
    (hrest : ∀ τ ∈ pairingsOn S, τ ≠ σ₀ → τ ≠ σ₁ →
      ∃ z ∈ S, W (Sym2.map (paint c) s(z, τ z)) = 0) :
    pmSum W c S
      = (∏ e ∈ S.image (fun x => s(x, σ₀ x)), W (Sym2.map (paint c) e))
        + ∏ e ∈ S.image (fun x => s(x, σ₁ x)), W (Sym2.map (paint c) e) := by
  classical
  rw [pmSum, ← Finset.add_sum_erase _ _ h₀,
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne, h₁⟩)]
  congr 1
  have hall : ∀ τ ∈ ((pairingsOn S).erase σ₀).erase σ₁,
      (∏ e ∈ S.image (fun x => s(x, τ x)), W (Sym2.map (paint c) e)) = 0 := by
    intro τ hτ
    have hτ₁ : τ ≠ σ₁ := Finset.ne_of_mem_erase hτ
    have hτ' := Finset.mem_of_mem_erase hτ
    have hτ₀ : τ ≠ σ₀ := Finset.ne_of_mem_erase hτ'
    obtain ⟨z, hz, hz0⟩ := hrest τ (Finset.mem_of_mem_erase hτ') hτ₀ hτ₁
    exact Finset.prod_eq_zero (Finset.mem_image.mpr ⟨z, hz, rfl⟩) hz0
  rw [Finset.sum_eq_zero hall, add_zero]

/-- Two live matchings whose edge products do not cancel force the whole
matching sum to be nonzero. -/
theorem pmSum_ne_zero_of_two_matchings (W : Sym2 (V × C) → R) (c : V → C)
    {S : Finset V} {σ₀ σ₁ : Equiv.Perm V}
    (h₀ : σ₀ ∈ pairingsOn S) (h₁ : σ₁ ∈ pairingsOn S) (hne : σ₁ ≠ σ₀)
    (hrest : ∀ τ ∈ pairingsOn S, τ ≠ σ₀ → τ ≠ σ₁ →
      ∃ z ∈ S, W (Sym2.map (paint c) s(z, τ z)) = 0)
    (hnocancel :
      (∏ e ∈ S.image (fun x => s(x, σ₀ x)), W (Sym2.map (paint c) e))
        + (∏ e ∈ S.image (fun x => s(x, σ₁ x)), W (Sym2.map (paint c) e)) ≠ 0) :
    pmSum W c S ≠ 0 := by
  rw [pmSum_eq_two_terms W c h₀ h₁ hne hrest]
  exact hnocancel

/-! ### Certified deletion -/

/-- If a nonzero matching sum has a pivot with one possible live partner, deleting
that forced pair leaves a nonzero matching sum. -/
theorem certified_forced_pair (W : Sym2 (V × C) → R) (c : V → C)
    {S : Finset V} {u z : V} (hu : u ∈ S) (hS : pmSum W c S ≠ 0)
    (huniq : ∀ y ∈ S.erase u, W (Sym2.map (paint c) s(u, y)) ≠ 0 → y = z) :
    pmSum W c ((S.erase u).erase z) ≠ 0 := by
  obtain ⟨y, hy, hlive, hrest⟩ := exists_partner_ne_zero W c hu hS
  rwa [huniq y hy hlive] at hrest

end MatchingNonvanishing
