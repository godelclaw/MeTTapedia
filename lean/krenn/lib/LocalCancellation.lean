import Mathlib
import MatchingParity
import Amplitude
import MatchingBridge
import MatchingSum

/-!
# Local cancellation in the amplitude

Fix a vertex set `A` and two perfect matchings of it.  The perfect matchings of
the whole vertex set that agree with one or the other on `A` come in natural
pairs: regraft the inside, leave the outside alone.  Their amplitude terms differ
only in the factors indexed by `A`, so if the two weight products over `A` are
negatives, every pair cancels and the whole family drops out of the amplitude.

This is the payoff of the exchange machinery.  The hypothesis is a single scalar
equation about `A` alone — it never mentions the matchings being cancelled, and it
is uniform in the vertex set, so it applies at every count the conjecture ranges
over.

The regrafting is not an ad hoc construction: on the nose it is right
multiplication by `α β`, where `α` and `β` are the two matchings of `A` extended
by the identity.  That makes it a permutation for free, and makes the two
directions inverse for free.
-/

namespace LocalCancellation

open MatchingParity Amplitude MatchingBridge

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} {R : Type*} [CommSemiring R]

/-- A perfect matching of the vertex set `A`, extended by the identity outside it. -/
structure LocalSwap (V : Type*) [DecidableEq V] (A : Finset V) where
  /-- The underlying permutation. -/
  perm : Equiv.Perm V
  /-- It is an involution. -/
  involutive : ∀ x, perm (perm x) = x
  /-- It is the identity outside `A`. -/
  fixes_outside : ∀ x, x ∉ A → perm x = x
  /-- It moves every vertex of `A`. -/
  moves_inside : ∀ x ∈ A, perm x ≠ x

namespace LocalSwap

variable {A : Finset V}

omit [Fintype V] in
/-- A local swap keeps `A` inside itself. -/
theorem closed (α : LocalSwap V A) : ∀ x ∈ A, α.perm x ∈ A := by
  intro x hx
  by_contra h
  have hfix := α.fixes_outside _ h
  rw [α.involutive] at hfix
  exact α.moves_inside x hx hfix.symm

end LocalSwap

/-- The product of the weights of a permutation's matching edges met by a vertex
set. -/
def permEdgeProd (W : Sym2 (V × C) → R) (c : V → C) (σ : Equiv.Perm V) (A : Finset V) : R :=
  ∏ e ∈ A.image (fun x => s(x, σ x)), W (Sym2.map (paint c) e)

omit [Fintype V] in
/-- Two permutations agreeing on `A` have the same edge product over `A`. -/
theorem permEdgeProd_congr (W : Sym2 (V × C) → R) (c : V → C) {σ ρ : Equiv.Perm V}
    {A : Finset V} (h : ∀ x ∈ A, σ x = ρ x) :
    permEdgeProd W c σ A = permEdgeProd W c ρ A := by
  unfold permEdgeProd
  congr 1
  exact Finset.image_congr (fun x hx => by rw [h x hx])

/-- Along a set closed under an involution, the edges inside and the edges outside
are disjoint. -/
theorem disjoint_perm_edges {σ : Equiv.Perm V}
    {A : Finset V} (hA : ∀ x ∈ A, σ x ∈ A) :
    Disjoint (A.image (fun x => s(x, σ x))) (Aᶜ.image (fun x => s(x, σ x))) := by
  rw [Finset.disjoint_left]
  rintro e he he'
  simp only [Finset.mem_image] at he he'
  obtain ⟨x, hx, rfl⟩ := he
  obtain ⟨y, hy, hxy⟩ := he'
  rw [Finset.mem_compl] at hy
  rw [Sym2.eq_iff] at hxy
  rcases hxy with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hy hx
  · exact hy (hA x hx)

/-- The amplitude term of a matching factors across a closed set. -/
theorem prod_edges_split_perm (W : Sym2 (V × C) → R) (c : V → C) {σ : Equiv.Perm V}
    {A : Finset V} (hA : ∀ x ∈ A, σ x ∈ A) :
    (∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      = permEdgeProd W c σ A * permEdgeProd W c σ Aᶜ := by
  unfold edges permEdgeProd
  rw [← Finset.union_compl A, Finset.image_union,
    Finset.prod_union (disjoint_perm_edges hA)]

/-- **Regrafting.**  Replace the part of `σ` lying inside `A` by `β`, keeping the
rest.  On the nose this is right multiplication by `α β`. -/
def graft {A : Finset V} (α β : LocalSwap V A) (σ : Equiv.Perm V) : Equiv.Perm V :=
  σ * (α.perm * β.perm)

variable {A : Finset V}

omit [Fintype V] in
/-- Inside `A` a regraft follows the second local swap. -/
theorem graft_of_mem (α β : LocalSwap V A) {σ : Equiv.Perm V}
    (hσ : ∀ x ∈ A, σ x = α.perm x) {x : V} (hx : x ∈ A) :
    graft α β σ x = β.perm x := by
  simp only [graft, Equiv.Perm.mul_apply]
  rw [hσ _ (α.closed _ (β.closed x hx)), α.involutive]

omit [Fintype V] in
/-- Outside `A` a regraft is unchanged. -/
theorem graft_of_notMem (α β : LocalSwap V A) (σ : Equiv.Perm V) {x : V} (hx : x ∉ A) :
    graft α β σ x = σ x := by
  simp only [graft, Equiv.Perm.mul_apply]
  rw [β.fixes_outside x hx, α.fixes_outside x hx]

omit [Fintype V] in
/-- A matching agreeing with a local swap on `A` keeps `A` closed. -/
theorem closed_of_agrees {σ : Equiv.Perm V} (α : LocalSwap V A)
    (hσ : ∀ x ∈ A, σ x = α.perm x) : ∀ x ∈ A, σ x ∈ A := by
  intro x hx
  rw [hσ x hx]
  exact α.closed x hx

omit [Fintype V] in
/-- Such a matching keeps the complement closed too. -/
theorem closed_compl_of_agrees {σ : Equiv.Perm V} (hinv : ∀ x, σ (σ x) = x)
    (α : LocalSwap V A) (hσ : ∀ x ∈ A, σ x = α.perm x) : ∀ x ∉ A, σ x ∉ A := by
  intro x hx hmem
  exact hx (by simpa [hinv] using closed_of_agrees α hσ _ hmem)

/-- A regraft is again a perfect matching. -/
theorem graft_mem_pairings (α β : LocalSwap V A) {σ : Equiv.Perm V}
    (hmem : σ ∈ pairings V) (hσ : ∀ x ∈ A, σ x = α.perm x) :
    graft α β σ ∈ pairings V := by
  obtain ⟨hinv, hne⟩ := (Finset.mem_filter.mp hmem).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ A
    · rw [graft_of_mem α β hσ hx, graft_of_mem α β hσ (β.closed x hx), β.involutive]
    · rw [graft_of_notMem α β σ hx,
        graft_of_notMem α β σ (closed_compl_of_agrees hinv α hσ x hx), hinv]
  · intro x
    by_cases hx : x ∈ A
    · rw [graft_of_mem α β hσ hx]; exact β.moves_inside x hx
    · rw [graft_of_notMem α β σ hx]; exact hne x

omit [Fintype V] in
/-- A regraft agrees with the second local swap on `A`. -/
theorem graft_agrees (α β : LocalSwap V A) {σ : Equiv.Perm V}
    (hσ : ∀ x ∈ A, σ x = α.perm x) : ∀ x ∈ A, graft α β σ x = β.perm x :=
  fun _ hx => graft_of_mem α β hσ hx

omit [Fintype V] in
/-- Regrafting back returns the original matching. -/
theorem graft_graft (α β : LocalSwap V A) {σ : Equiv.Perm V}
    (hσ : ∀ x ∈ A, σ x = α.perm x) : graft β α (graft α β σ) = σ := by
  ext x
  by_cases hx : x ∈ A
  · rw [graft_of_mem β α (graft_agrees α β hσ) hx, hσ x hx]
  · rw [graft_of_notMem β α _ hx, graft_of_notMem α β σ hx]

/-! ### The cancellation -/

/-- The perfect matchings agreeing with a given local swap on `A`. -/
def config (α : LocalSwap V A) : Finset (Equiv.Perm V) :=
  (pairings V).filter (fun σ => ∀ x ∈ A, σ x = α.perm x)

theorem mem_config {α : LocalSwap V A} {σ : Equiv.Perm V} :
    σ ∈ config α ↔ σ ∈ pairings V ∧ ∀ x ∈ A, σ x = α.perm x := by
  simp [config]

theorem config_subset (α : LocalSwap V A) : config α ⊆ pairings V :=
  Finset.filter_subset _ _

/-- Local swaps differing anywhere on `A` have disjoint configuration families. -/
theorem disjoint_config {α β : LocalSwap V A} {a : V} (ha : a ∈ A)
    (hab : α.perm a ≠ β.perm a) : Disjoint (config α) (config β) := by
  rw [Finset.disjoint_left]
  intro σ hσ hσ'
  rw [mem_config] at hσ hσ'
  exact hab (by rw [← hσ.2 a ha, hσ'.2 a ha])

/-- Regrafting carries one configuration family onto the other. -/
theorem config_eq_image (α β : LocalSwap V A) :
    config β = (config α).image (graft α β) := by
  ext σ'
  constructor
  · intro hσ'
    rw [mem_config] at hσ'
    refine Finset.mem_image.mpr ⟨graft β α σ', ?_, graft_graft β α hσ'.2⟩
    exact mem_config.mpr ⟨graft_mem_pairings β α hσ'.1 hσ'.2, graft_agrees β α hσ'.2⟩
  · intro h
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp h
    rw [mem_config] at hσ
    exact mem_config.mpr ⟨graft_mem_pairings α β hσ.1 hσ.2, graft_agrees α β hσ.2⟩

theorem graft_injOn (α β : LocalSwap V A) :
    ∀ x ∈ config α, ∀ y ∈ config α, graft α β x = graft α β y → x = y := by
  intro x hx y hy h
  rw [mem_config] at hx hy
  rw [← graft_graft α β hx.2, ← graft_graft α β hy.2, h]

/-! ### Which matchings have a configuration

A configuration family is only useful once one knows what falls into it.  A
perfect matching agrees on `A` with some local swap exactly when it closes `A`,
and then the swap is unique: it is the matching's own restriction.  So the
configuration families partition the matchings that close `A`, and miss precisely
those that do not.
-/

omit [Fintype V] in
/-- Local swaps are determined by their permutation. -/
theorem LocalSwap.ext' {α β : LocalSwap V A} (h : α.perm = β.perm) : α = β := by
  revert h
  obtain ⟨p, hp1, hp2, hp3⟩ := α
  obtain ⟨q, hq1, hq2, hq3⟩ := β
  intro h
  simp only at h
  subst h
  rfl

omit [Fintype V] in
/-- Cutting a matching down to a set it closes gives an involution. -/
theorem restrict_involutive {σ : Equiv.Perm V} (hinv : ∀ x, σ (σ x) = x)
    {A : Finset V} (hA : ∀ x ∈ A, σ x ∈ A) :
    Function.Involutive (fun x => if x ∈ A then σ x else x) := by
  intro x
  simp only
  by_cases hx : x ∈ A
  · rw [if_pos hx, if_pos (hA x hx), hinv]
  · rw [if_neg hx, if_neg hx]

/-- **The restriction of a matching to a set it closes**: a matching of `A`,
extended by the identity outside. -/
def restrict {σ : Equiv.Perm V} (hinv : ∀ x, σ (σ x) = x) (hne : ∀ x, σ x ≠ x)
    {A : Finset V} (hA : ∀ x ∈ A, σ x ∈ A) : LocalSwap V A where
  perm := Function.Involutive.toPerm _ (restrict_involutive hinv hA)
  involutive := restrict_involutive hinv hA
  fixes_outside := fun _ hx => if_neg hx
  moves_inside := fun x hx => by
    show (if x ∈ A then σ x else x) ≠ x
    rw [if_pos hx]
    exact hne x

omit [Fintype V] in
@[simp] theorem restrict_perm_apply {σ : Equiv.Perm V} (hinv : ∀ x, σ (σ x) = x)
    (hne : ∀ x, σ x ≠ x) {A : Finset V} (hA : ∀ x ∈ A, σ x ∈ A) (x : V) :
    (restrict hinv hne hA).perm x = if x ∈ A then σ x else x := rfl

/-- A matching lies in the configuration family of its own restriction. -/
theorem mem_config_restrict {σ : Equiv.Perm V} (hmem : σ ∈ pairings V)
    (hinv : ∀ x, σ (σ x) = x) (hne : ∀ x, σ x ≠ x)
    {A : Finset V} (hA : ∀ x ∈ A, σ x ∈ A) :
    σ ∈ config (restrict hinv hne hA) :=
  mem_config.mpr ⟨hmem, fun x hx => by rw [restrict_perm_apply, if_pos hx]⟩

/-- **A matching has a configuration on `A` exactly when it closes `A`.** -/
theorem closes_iff_exists_config {σ : Equiv.Perm V} (hmem : σ ∈ pairings V)
    {A : Finset V} :
    (∀ x ∈ A, σ x ∈ A) ↔ ∃ α : LocalSwap V A, σ ∈ config α := by
  obtain ⟨hinv, hne⟩ := (Finset.mem_filter.mp hmem).2
  constructor
  · exact fun hA => ⟨restrict hinv hne hA, mem_config_restrict hmem hinv hne hA⟩
  · rintro ⟨α, hα⟩ x hx
    rw [(mem_config.mp hα).2 x hx]
    exact α.closed x hx

/-- **And that configuration is unique.**  Two local swaps sharing a matching are
equal, so the configuration families are pairwise disjoint. -/
theorem config_inj {α β : LocalSwap V A} {σ : Equiv.Perm V}
    (hα : σ ∈ config α) (hβ : σ ∈ config β) : α = β := by
  refine LocalSwap.ext' ?_
  ext x
  by_cases hx : x ∈ A
  · rw [← (mem_config.mp hα).2 x hx, ← (mem_config.mp hβ).2 x hx]
  · rw [α.fixes_outside x hx, β.fixes_outside x hx]

/-! ### Configurations contribute proportionally

Every matching in a configuration family carries the same weight product inside
`A`, so that product factors out of the family's contribution.  What remains — the
sum of the outside products — turns out not to depend on which matching of `A` was
chosen, because regrafting is a bijection between families and leaves the outside
untouched.

So the amplitude's entire dependence on `A` runs through the weight products of
`A`'s own matchings, with one common factor for everything outside.  Cancellation
is the case where those products sum to zero.
-/

/-- The weight product inside `A` factors out of a configuration family. -/
theorem sum_config_eq_mul (W : Sym2 (V × C) → R) (c : V → C) (α : LocalSwap V A) :
    ∑ σ ∈ config α, ∏ e ∈ edges σ, W (Sym2.map (paint c) e)
      = permEdgeProd W c α.perm A * ∑ σ ∈ config α, permEdgeProd W c σ Aᶜ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [mem_config] at hσ
  rw [prod_edges_split_perm W c (closed_of_agrees α hσ.2), permEdgeProd_congr W c hσ.2]

/-- The outside sum is the same for every matching of `A`: regrafting is a
bijection between the families and never touches the outside. -/
theorem sum_config_outside_eq (W : Sym2 (V × C) → R) (c : V → C) (α β : LocalSwap V A) :
    ∑ σ ∈ config β, permEdgeProd W c σ Aᶜ = ∑ σ ∈ config α, permEdgeProd W c σ Aᶜ := by
  rw [config_eq_image α β, Finset.sum_image (graft_injOn α β)]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact permEdgeProd_congr W c (fun x hx => graft_of_notMem α β σ (Finset.mem_compl.mp hx))

/-- **Configurations contribute proportionally.**  Two configuration families
contribute in the ratio of their weight products over `A`.  Stated without
division, so it holds over any commutative semiring and needs no invertibility.

This is the whole content of the local structure: the amplitude sees `A` only
through the weight products of `A`'s matchings. -/
theorem sum_config_mul_comm (W : Sym2 (V × C) → R) (c : V → C) (α β : LocalSwap V A) :
    (∑ σ ∈ config β, ∏ e ∈ edges σ, W (Sym2.map (paint c) e)) * permEdgeProd W c α.perm A
      = (∑ σ ∈ config α, ∏ e ∈ edges σ, W (Sym2.map (paint c) e))
          * permEdgeProd W c β.perm A := by
  rw [sum_config_eq_mul, sum_config_eq_mul, sum_config_outside_eq W c α β]
  ring

/-- Local swaps are determined by their permutation, so equality is decidable. -/
instance : DecidableEq (LocalSwap V A) := fun α β =>
  decidable_of_iff (α.perm = β.perm) ⟨LocalSwap.ext', fun h => by rw [h]⟩

/-- Distinct local swaps have disjoint configuration families. -/
theorem pairwiseDisjoint_config (L : Finset (LocalSwap V A)) :
    (L : Set (LocalSwap V A)).PairwiseDisjoint (config (V := V) (A := A)) := by
  intro α _ β _ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  exact fun σ hα hβ => hne (config_inj hα hβ)

/-- **Cancellation from a vanishing sum of products.**  If a family of matchings
of `A` has weight products summing to zero, then every perfect matching whose
restriction to `A` lies in that family drops out of the amplitude together.

This is the criterion that bites in practice.  Pairwise cancellation asks two
products to be exact negatives; this asks only that a family sum to zero, which
for a four-vertex set means one linear relation among three products. -/
theorem sum_biUnion_config_eq_zero (W : Sym2 (V × C) → R) (c : V → C)
    (L : Finset (LocalSwap V A))
    (hprod : ∑ α ∈ L, permEdgeProd W c α.perm A = 0) :
    ∑ σ ∈ L.biUnion config, ∏ e ∈ edges σ, W (Sym2.map (paint c) e) = 0 := by
  rcases L.eq_empty_or_nonempty with rfl | ⟨α₀, hα₀⟩
  · simp
  · rw [Finset.sum_biUnion (pairwiseDisjoint_config L)]
    have hterm : ∀ α ∈ L, (∑ σ ∈ config α, ∏ e ∈ edges σ, W (Sym2.map (paint c) e))
        = permEdgeProd W c α.perm A * ∑ σ ∈ config α₀, permEdgeProd W c σ Aᶜ := by
      intro α _
      rw [sum_config_eq_mul, sum_config_outside_eq W c α₀ α]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hprod, zero_mul]

/-- The usable form: such a family may be deleted from the amplitude. -/
theorem amplitude_eq_sum_sdiff_biUnion (W : Sym2 (V × C) → R) (c : V → C)
    (L : Finset (LocalSwap V A))
    (hprod : ∑ α ∈ L, permEdgeProd W c α.perm A = 0) :
    amplitude W c
      = ∑ σ ∈ pairings V \ L.biUnion config, ∏ e ∈ edges σ, W (Sym2.map (paint c) e) := by
  have hsub : L.biUnion config ⊆ pairings V :=
    Finset.biUnion_subset.mpr (fun α _ => config_subset α)
  have hsplit :=
    Finset.sum_sdiff (f := fun σ => ∏ e ∈ edges σ, W (Sym2.map (paint c) e)) hsub
  simp only [amplitude]
  rw [← hsplit, sum_biUnion_config_eq_zero W c L hprod, add_zero]

/-! ### The outside factor is the complement's matching sum

The contribution of a configuration family splits into the weight product inside
`A` and a sum over everything outside.  That outside sum is not merely common to
all the families — it is exactly the matching sum of the complement.

The identification is again a right multiplication: a matching agreeing with `α`
on `A` becomes a matching of the complement by multiplying by `α`, which cancels
the inside and leaves the outside alone.
-/

omit [Fintype V] in
/-- A local swap squares to the identity. -/
theorem LocalSwap.perm_mul_self (α : LocalSwap V A) : α.perm * α.perm = 1 := by
  ext x
  exact α.involutive x

/-- Multiplying by the local swap carries a configuration family onto the
matchings of the complement. -/
theorem config_eq_image_pairingsOn (α : LocalSwap V A) :
    config α = (MatchingSum.pairingsOn Aᶜ).image (fun τ => τ * α.perm) := by
  ext σ
  simp only [Finset.mem_image]
  constructor
  · intro hσ
    obtain ⟨hmem, hagree⟩ := mem_config.mp hσ
    obtain ⟨hinv, hnf⟩ := (Finset.mem_filter.mp hmem).2
    have hcl : ∀ x ∈ A, σ x ∈ A := closed_of_agrees α hagree
    have hclc : ∀ x, x ∉ A → σ x ∉ A := fun x hx hmemA => hx (by
      have := hcl _ hmemA; rwa [hinv] at this)
    have hin : ∀ x ∈ A, (σ * α.perm) x = x := by
      intro x hx
      show σ (α.perm x) = x
      rw [hagree _ (α.closed x hx), α.involutive]
    have hout : ∀ x, x ∉ A → (σ * α.perm) x = σ x := by
      intro x hx
      show σ (α.perm x) = σ x
      rw [α.fixes_outside x hx]
    refine ⟨σ * α.perm, MatchingSum.mem_pairingsOn.mpr ⟨fun x => ?_, fun x hx => ?_,
      fun x hx => ?_⟩, ?_⟩
    · by_cases hxA : x ∈ A
      · rw [hin x hxA, hin x hxA]
      · rw [hout x hxA, hout _ (hclc x hxA), hinv]
    · rw [Finset.mem_compl] at hx
      rw [hout x hx]
      exact hnf x
    · rw [Finset.mem_compl, not_not] at hx
      exact hin x hx
    · rw [mul_assoc, α.perm_mul_self, mul_one]
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨hinv, hnf, hfix⟩ := MatchingSum.mem_pairingsOn.mp hτ
    have hfixA : ∀ x ∈ A, τ x = x := fun x hx => hfix x (by simp [hx])
    have hclc : ∀ x, x ∉ A → τ x ∉ A := by
      intro x hx hmemA
      exact hx (by rw [← hinv x, hfixA _ hmemA]; exact hmemA)
    have hin : ∀ x ∈ A, (τ * α.perm) x = α.perm x := by
      intro x hx
      show τ (α.perm x) = α.perm x
      exact hfixA _ (α.closed x hx)
    have hout : ∀ x, x ∉ A → (τ * α.perm) x = τ x := by
      intro x hx
      show τ (α.perm x) = τ x
      rw [α.fixes_outside x hx]
    refine mem_config.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => ?_, fun x => ?_⟩,
      fun x hx => hin x hx⟩
    · by_cases hxA : x ∈ A
      · rw [hin x hxA, hin _ (α.closed x hxA), α.involutive]
      · rw [hout x hxA, hout _ (hclc x hxA), hinv]
    · by_cases hxA : x ∈ A
      · rw [hin x hxA]
        exact α.moves_inside x hxA
      · rw [hout x hxA]
        exact hnf x (Finset.mem_compl.mpr hxA)

/-- **The outside factor is the complement's matching sum.** -/
theorem sum_config_outside_eq_pmSum (W : Sym2 (V × C) → R) (c : V → C)
    (α : LocalSwap V A) :
    ∑ σ ∈ config α, permEdgeProd W c σ Aᶜ = MatchingSum.pmSum W c Aᶜ := by
  rw [config_eq_image_pairingsOn α,
    Finset.sum_image (fun _ _ _ _ h => mul_right_cancel h), MatchingSum.pmSum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  refine permEdgeProd_congr W c (fun x hx => ?_)
  show τ (α.perm x) = τ x
  rw [α.fixes_outside x (Finset.mem_compl.mp hx)]

/-- **A configuration factors.**  Its contribution is the weight product inside
`A` times the matching sum of everything outside.  Nothing about `A` enters the
second factor and nothing about the complement enters the first. -/
theorem sum_config_eq_mul_pmSum (W : Sym2 (V × C) → R) (c : V → C) (α : LocalSwap V A) :
    ∑ σ ∈ config α, ∏ e ∈ edges σ, W (Sym2.map (paint c) e)
      = permEdgeProd W c α.perm A * MatchingSum.pmSum W c Aᶜ := by
  rw [sum_config_eq_mul, sum_config_outside_eq_pmSum]

/-! ### Multiplicativity across a closed split

The matchings that respect a split of the vertices contribute the product of the
two sides' matching sums.  The composition law already holds in the library over
subtypes; stated through `pmSum` it needs no type surgery and no instances on the
two halves, so it composes with everything else here.
-/

/-- A local swap is a matching of its set. -/
theorem LocalSwap.perm_mem_pairingsOn (α : LocalSwap V A) :
    α.perm ∈ MatchingSum.pairingsOn A :=
  MatchingSum.mem_pairingsOn.mpr ⟨α.involutive, α.moves_inside, α.fixes_outside⟩

/-- A matching of a set is a local swap. -/
def LocalSwap.ofMem {ρ : Equiv.Perm V} (h : ρ ∈ MatchingSum.pairingsOn A) : LocalSwap V A where
  perm := ρ
  involutive := (MatchingSum.mem_pairingsOn.mp h).1
  fixes_outside := (MatchingSum.mem_pairingsOn.mp h).2.2
  moves_inside := (MatchingSum.mem_pairingsOn.mp h).2.1

/-- The configuration family of a matching of `A`, named without its swap
structure so that families can be indexed by a `Finset`. -/
def configOf (ρ : Equiv.Perm V) (A : Finset V) : Finset (Equiv.Perm V) :=
  (pairings V).filter (fun σ => ∀ x ∈ A, σ x = ρ x)

theorem config_eq_configOf (α : LocalSwap V A) : config α = configOf α.perm A := rfl

/-- **The matchings closing a set are exactly the configuration families of that
set's own matchings.** -/
theorem filter_closing_eq_biUnion (A : Finset V) :
    (pairings V).filter (fun σ => ∀ x ∈ A, σ x ∈ A)
      = (MatchingSum.pairingsOn A).biUnion (fun ρ => configOf ρ A) := by
  ext σ
  simp only [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hmem, hcl⟩
    obtain ⟨hinv, hne⟩ := (Finset.mem_filter.mp hmem).2
    refine ⟨(restrict hinv hne hcl).perm, LocalSwap.perm_mem_pairingsOn _, ?_⟩
    exact Finset.mem_filter.mpr ⟨hmem, fun x hx => by rw [restrict_perm_apply, if_pos hx]⟩
  · rintro ⟨ρ, hρ, hσ⟩
    obtain ⟨hmem, hagree⟩ := Finset.mem_filter.mp hσ
    refine ⟨hmem, fun x hx => ?_⟩
    rw [hagree x hx]
    exact MatchingSum.pairingsOn_closed hρ x hx

theorem pairwiseDisjoint_configOf (A : Finset V) (L : Finset (Equiv.Perm V))
    (hL : ∀ ρ ∈ L, ρ ∈ MatchingSum.pairingsOn A) :
    (L : Set (Equiv.Perm V)).PairwiseDisjoint (fun ρ => configOf ρ A) := by
  intro ρ hρ ρ' hρ' hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro σ h1 h2
  refine hne ?_
  obtain ⟨-, ha1⟩ := Finset.mem_filter.mp h1
  obtain ⟨-, ha2⟩ := Finset.mem_filter.mp h2
  have hout1 := (MatchingSum.mem_pairingsOn.mp (hL ρ hρ)).2.2
  have hout2 := (MatchingSum.mem_pairingsOn.mp (hL ρ' hρ')).2.2
  ext x
  by_cases hx : x ∈ A
  · rw [← ha1 x hx, ← ha2 x hx]
  · rw [hout1 x hx, hout2 x hx]

/-- **Multiplicativity across a closed split.**  The matchings that keep a vertex
set to itself contribute the matching sum of that set times the matching sum of
its complement. -/
theorem sum_closing_eq_pmSum_mul (W : Sym2 (V × C) → R) (c : V → C) (A : Finset V) :
    (∑ σ ∈ (pairings V).filter (fun σ => ∀ x ∈ A, σ x ∈ A),
        ∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      = MatchingSum.pmSum W c A * MatchingSum.pmSum W c Aᶜ := by
  rw [filter_closing_eq_biUnion,
    Finset.sum_biUnion (pairwiseDisjoint_configOf A _ (fun _ h => h))]
  have hterm : ∀ ρ ∈ MatchingSum.pairingsOn A,
      (∑ σ ∈ configOf ρ A, ∏ e ∈ edges σ, W (Sym2.map (paint c) e))
        = permEdgeProd W c ρ A * MatchingSum.pmSum W c Aᶜ := by
    intro ρ hρ
    have := sum_config_eq_mul_pmSum W c (LocalSwap.ofMem hρ)
    rwa [config_eq_configOf] at this
  have hA : MatchingSum.pmSum W c A
      = ∑ ρ ∈ MatchingSum.pairingsOn A, permEdgeProd W c ρ A := rfl
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← hA]

section LocalRelation

variable {S : Type*} [CommRing S] [NoZeroDivisors S]

/-- **A relation between two matchings localises to where they differ.**  If two
matchings agree outside a set and the set is closed under both, everything outside
is a common factor.  When that factor does not vanish, a relation between their
whole products becomes the same relation between their products over the set alone.

Applied to two matchings differing by a single alternating four-cycle, this turns
the statement that their amplitude contributions cancel into an equation among four
weights — the determinant that keeps reappearing. -/
theorem local_relation_of_sum_eq_zero (W : Sym2 (V × C) → S) (c : V → C)
    {σ τ : Equiv.Perm V} {A : Finset V}
    (hσA : ∀ x ∈ A, σ x ∈ A) (hτA : ∀ x ∈ A, τ x ∈ A)
    (hagree : ∀ x, x ∉ A → σ x = τ x)
    (hQ : permEdgeProd W c σ Aᶜ ≠ 0)
    (hsum : (∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      + (∏ e ∈ edges τ, W (Sym2.map (paint c) e)) = 0) :
    permEdgeProd W c σ A + permEdgeProd W c τ A = 0 := by
  have houts : permEdgeProd W c τ Aᶜ = permEdgeProd W c σ Aᶜ :=
    permEdgeProd_congr W c (fun x hx => (hagree x (Finset.mem_compl.mp hx)).symm)
  rw [prod_edges_split_perm W c hσA, prod_edges_split_perm W c hτA, houts,
    ← add_mul] at hsum
  exact (mul_eq_zero.mp hsum).resolve_right hQ

end LocalRelation

/-! ### A factorisation dichotomy

Several routes into this problem end at the same place: the matching sum over a
four-vertex set must vanish.  The determinant forced at a colour-slice of degree
two, the criterion for a local family to cancel, and the relation between two
compatible matchings differing by one alternating cycle are all that statement.

Here is the general form.  If a colouring kills every matching that crosses the
boundary of a set, then what remains factors as the two sides' matching sums, the
amplitude must vanish, and the complex numbers have no zero divisors.  So one side
or the other must vanish — and which one is not determined, which is exactly why
this is a dichotomy rather than a descent.
-/

/-- **A colouring with no crossing forces one side to vanish.**  If every matching
crossing the boundary of `A` contributes nothing at a non-constant colouring, then
the matching sum over `A` or the matching sum over its complement is zero. -/
theorem pmSum_mul_eq_zero_of_no_crossing (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (c : V → Fin 3) (hc : ¬ Amplitude.Monochromatic c) (A : Finset V)
    (hcross : ∀ σ ∈ pairings V, ¬ (∀ x ∈ A, σ x ∈ A) →
      (∏ e ∈ edges σ, W (Sym2.map (paint c) e)) = 0) :
    MatchingSum.pmSum W c A = 0 ∨ MatchingSum.pmSum W c Aᶜ = 0 := by
  classical
  refine mul_eq_zero.mp ?_
  rw [← sum_closing_eq_pmSum_mul W c A]
  have hsplit := Finset.sum_filter_add_sum_filter_not (pairings V)
    (fun σ => ∀ x ∈ A, σ x ∈ A) (fun σ => ∏ e ∈ edges σ, W (Sym2.map (paint c) e))
  have hrest : (∑ σ ∈ (pairings V).filter (fun σ => ¬ ∀ x ∈ A, σ x ∈ A),
      ∏ e ∈ edges σ, W (Sym2.map (paint c) e)) = 0 :=
    Finset.sum_eq_zero (fun σ hσ => by
      obtain ⟨hmem, hnot⟩ := Finset.mem_filter.mp hσ
      exact hcross σ hmem hnot)
  have hamp := hzero c hc
  rw [amplitude] at hamp
  rw [← hsplit, hrest, add_zero] at hamp
  exact hamp

/-- **One live side kills the other.**  The dichotomy read in the direction that is
usable: if the matching sum over a set does not vanish, the matching sum over its
complement does.

Which side vanishes is not determined in general — measured on the proved six-vertex
two-colour solution, the distinguished side and its complement each survive equally
often, and size does not decide.  What the statement does give is a lever: exhibit a
single set whose matching sum is nonzero and the complement's vanishing follows.  For
a two-element set the matching sum is just the edge's weight, so one nonvanishing
weight at a non-constant colouring forces the matching sum over everything else to
vanish. -/
theorem pmSum_compl_eq_zero_of_ne_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (c : V → Fin 3) (hc : ¬ Amplitude.Monochromatic c) (A : Finset V)
    (hcross : ∀ σ ∈ pairings V, ¬ (∀ x ∈ A, σ x ∈ A) →
      (∏ e ∈ edges σ, W (Sym2.map (paint c) e)) = 0)
    (hne : MatchingSum.pmSum W c A ≠ 0) :
    MatchingSum.pmSum W c Aᶜ = 0 :=
  (pmSum_mul_eq_zero_of_no_crossing W hzero c hc A hcross).resolve_left hne


section Cancellation

variable {S : Type*} [CommRing S]

/-- **Local cancellation.**  If the weight products of two matchings of `A` are
negatives of one another, every perfect matching agreeing with one of them on `A`
cancels against its regraft, and the whole family contributes nothing to the
amplitude.

The hypothesis is a single scalar equation about `A` alone.  It never mentions the
matchings being cancelled, and it places no condition on the vertex count. -/
theorem sum_config_union_eq_zero (W : Sym2 (V × C) → S) (c : V → C)
    (α β : LocalSwap V A) {a : V} (ha : a ∈ A) (hab : α.perm a ≠ β.perm a)
    (hprod : permEdgeProd W c β.perm A = -permEdgeProd W c α.perm A) :
    ∑ σ ∈ config α ∪ config β, ∏ e ∈ edges σ, W (Sym2.map (paint c) e) = 0 := by
  rw [Finset.sum_union (disjoint_config ha hab), config_eq_image α β,
    Finset.sum_image (graft_injOn α β), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun σ hσ => ?_)
  rw [mem_config] at hσ
  obtain ⟨-, hagree⟩ := hσ
  have hgagree := graft_agrees α β hagree
  rw [prod_edges_split_perm W c (closed_of_agrees α hagree),
    prod_edges_split_perm W c (closed_of_agrees β hgagree),
    permEdgeProd_congr W c hagree, permEdgeProd_congr W c hgagree,
    permEdgeProd_congr (A := Aᶜ) W c
      (fun x hx => graft_of_notMem α β σ (Finset.mem_compl.mp hx)),
    hprod]
  ring

/-- The usable form: a cancelling family may simply be deleted from the amplitude. -/
theorem amplitude_eq_sum_sdiff_config (W : Sym2 (V × C) → S) (c : V → C)
    (α β : LocalSwap V A) {a : V} (ha : a ∈ A) (hab : α.perm a ≠ β.perm a)
    (hprod : permEdgeProd W c β.perm A = -permEdgeProd W c α.perm A) :
    amplitude W c
      = ∑ σ ∈ pairings V \ (config α ∪ config β), ∏ e ∈ edges σ, W (Sym2.map (paint c) e) := by
  have hsub : config α ∪ config β ⊆ pairings V :=
    Finset.union_subset (config_subset α) (config_subset β)
  have hsplit :=
    Finset.sum_sdiff (f := fun σ => ∏ e ∈ edges σ, W (Sym2.map (paint c) e)) hsub
  simp only [amplitude]
  rw [← hsplit, sum_config_union_eq_zero W c α β ha hab hprod, add_zero]

end Cancellation

end LocalCancellation
