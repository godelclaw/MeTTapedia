import Mettapedia.Combinatorics.Matching.Sum

/-!
# Restricting perfect matchings to invariant subsets

A perfect matching carried by a permutation restricts to any invariant vertex
subset and to its complement. The restriction preserves its matching edges and
therefore preserves nonzero edge products. The same viewpoint also bounds how
many vertices of a subset any perfect matching must pair internally.
-/

namespace MatchingRestriction

open Amplitude MatchingSum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An involution cut down to an invariant set: it acts as `σ` inside and fixes the outside. -/
def restrictFun (σ : Equiv.Perm V) (A : Finset V) (x : V) : V :=
  if x ∈ A then σ x else x

omit [Fintype V] in
theorem restrictFun_involutive {σ : Equiv.Perm V} {A : Finset V}
    (hinv : ∀ x, σ (σ x) = x) (hcl : ∀ x ∈ A, σ x ∈ A) :
    Function.Involutive (restrictFun σ A) := by
  intro x
  by_cases hx : x ∈ A
  · simp only [restrictFun, if_pos hx, if_pos (hcl x hx), hinv]
  · simp only [restrictFun, if_neg hx]

/-- The restriction of a matching to an invariant set, as a permutation. -/
def restrictPerm (σ : Equiv.Perm V) (A : Finset V)
    (hinv : ∀ x, σ (σ x) = x) (hcl : ∀ x ∈ A, σ x ∈ A) : Equiv.Perm V :=
  (restrictFun_involutive hinv hcl).toPerm _

omit [Fintype V] in
theorem restrictPerm_apply {σ : Equiv.Perm V} {A : Finset V}
    (hinv : ∀ x, σ (σ x) = x) (hcl : ∀ x ∈ A, σ x ∈ A) (x : V) :
    restrictPerm σ A hinv hcl x = if x ∈ A then σ x else x := rfl

/-- The complement of an invariant set is invariant: an involution cannot leave one side
without arriving on the other. -/
theorem sdiff_closed {σ : Equiv.Perm V} {S A : Finset V} (hσ : σ ∈ pairingsOn S)
    (hcl : ∀ x ∈ A, σ x ∈ A) : ∀ x ∈ S \ A, σ x ∈ S \ A := by
  obtain ⟨hinv, -, -⟩ := mem_pairingsOn.mp hσ
  intro x hx
  rw [Finset.mem_sdiff] at hx ⊢
  refine ⟨pairingsOn_closed hσ x hx.1, ?_⟩
  intro hmem
  have h := hcl _ hmem
  rw [hinv] at h
  exact hx.2 h

/-- A matching restricted to an invariant subset is a matching of that subset. -/
theorem restrictPerm_mem {σ : Equiv.Perm V} {S A : Finset V} (hσ : σ ∈ pairingsOn S)
    (hAS : A ⊆ S) (hcl : ∀ x ∈ A, σ x ∈ A) :
    restrictPerm σ A (mem_pairingsOn.mp hσ).1 hcl ∈ pairingsOn A := by
  obtain ⟨hinv, hne, -⟩ := mem_pairingsOn.mp hσ
  refine mem_pairingsOn.mpr ⟨restrictFun_involutive hinv hcl, ?_, ?_⟩
  · intro x hx
    rw [restrictPerm_apply, if_pos hx]
    exact hne x (hAS hx)
  · intro x hx
    rw [restrictPerm_apply, if_neg hx]

omit [Fintype V] in
/-- The restriction uses only edges of the matching it came from. -/
theorem restrictPerm_image_subset {σ : Equiv.Perm V} {S A : Finset V}
    (hinv : ∀ x, σ (σ x) = x) (hcl : ∀ x ∈ A, σ x ∈ A) (hAS : A ⊆ S) :
    A.image (fun x => s(x, restrictPerm σ A hinv hcl x)) ⊆ S.image (fun x => s(x, σ x)) := by
  intro e he
  simp only [Finset.mem_image] at he ⊢
  obtain ⟨x, hx, rfl⟩ := he
  exact ⟨x, hAS hx, by rw [restrictPerm_apply, if_pos hx]⟩

/-- **A set invariant under two matchings splits both of them.**  The set carries a matching
inherited from the first, its complement one inherited from the second.  Nothing here is about
colour or weight: it is the bare combinatorics of two involutions sharing an invariant set. -/
theorem matchable_split_of_invariant {σ τ : Equiv.Perm V} {S A : Finset V}
    (hσ : σ ∈ pairingsOn S) (hτ : τ ∈ pairingsOn S) (hAS : A ⊆ S)
    (hσA : ∀ x ∈ A, σ x ∈ A) (hτA : ∀ x ∈ A, τ x ∈ A) :
    (pairingsOn A).Nonempty ∧ (pairingsOn (S \ A)).Nonempty :=
  ⟨⟨_, restrictPerm_mem hσ hAS hσA⟩,
   ⟨_, restrictPerm_mem hτ Finset.sdiff_subset (sdiff_closed hτ hτA)⟩⟩

omit [Fintype V] in
/-- The restricted matching contributes a non-vanishing term: every edge it uses was already
live in the matching it was cut from. -/
theorem prod_restrict_ne_zero {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    {D : Type*}
    [DecidableEq D] {W : Sym2 (V × D) → R} {c : V → D} {σ : Equiv.Perm V} {S A : Finset V}
    (hinv : ∀ x, σ (σ x) = x) (hcl : ∀ x ∈ A, σ x ∈ A) (hAS : A ⊆ S)
    (hlive : ∀ x ∈ S, W (Sym2.map (paint c) s(x, σ x)) ≠ 0) :
    ∏ e ∈ A.image (fun x => s(x, restrictPerm σ A hinv hcl x)),
      W (Sym2.map (paint c) e) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro e he
  simp only [Finset.mem_image] at he
  obtain ⟨x, hx, rfl⟩ := he
  rw [restrictPerm_apply, if_pos hx]
  exact hlive x (hAS hx)

/-- All but at most the complement's cardinality are matched inside a chosen
subset. The returned matching also has a nonzero weight on every selected edge. -/
theorem card_matched_inside {C R : Type*}
    [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R) (c : V → C) {S A : Finset V}
    (hAS : A ⊆ S) (hne : pmSum W c S ≠ 0) :
    ∃ σ ∈ pairingsOn S, (∀ z ∈ S, W (Sym2.map (paint c) s(z, σ z)) ≠ 0) ∧
      A.card ≤ (S \ A).card + (A.filter (fun x => σ x ∈ A)).card := by
  classical
  rw [pmSum] at hne
  obtain ⟨σ, hσ, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hfac := Finset.prod_ne_zero_iff.mp hprod
  have hlive : ∀ z ∈ S, W (Sym2.map (paint c) s(z, σ z)) ≠ 0 := fun z hz =>
    hfac _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  refine ⟨σ, hσ, hlive, ?_⟩
  have hout : (A.filter (fun x => σ x ∉ A)).card ≤ (S \ A).card := by
    refine Finset.card_le_card_of_injOn (fun x => σ x) (fun x hx => ?_)
      (fun a _ b _ h => σ.injective h)
    rcases Finset.mem_filter.mp hx with ⟨hxA, hxout⟩
    exact Finset.mem_sdiff.mpr ⟨pairingsOn_closed hσ x (hAS hxA), hxout⟩
  have hsplit : (A.filter (fun x => σ x ∈ A)).card +
      (A.filter (fun x => σ x ∉ A)).card = A.card :=
    Finset.card_filter_add_card_filter_not (p := fun x => σ x ∈ A) (s := A)
  omega

/-- At least the cardinality difference between a subset and its complement is
matched internally. -/
theorem card_internal_ge {C R : Type*}
    [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R) (c : V → C) {S A : Finset V}
    (hAS : A ⊆ S) (hne : pmSum W c S ≠ 0) :
    ∃ σ ∈ pairingsOn S, (∀ z ∈ S, W (Sym2.map (paint c) s(z, σ z)) ≠ 0) ∧
      A.card - (S \ A).card ≤ (A.filter (fun x => σ x ∈ A)).card := by
  obtain ⟨σ, hσ, hlive, hcard⟩ := card_matched_inside W c hAS hne
  exact ⟨σ, hσ, hlive, by omega⟩

end MatchingRestriction
