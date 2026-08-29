import Mathlib
import Mettapedia.Combinatorics.Matching.Pairing
import Mettapedia.Combinatorics.Matching.Amplitude

/-!
# Bridging the two representations of a perfect matching

`MatchingParity.Pairing` carries a perfect matching as a structure: a partner
function with the two involution laws.  That is the convenient form for building
matchings — exchange along a closed set, for instance, is stated there.

`Amplitude.pairings` carries the same data as a `Finset` of permutations.  That is
the convenient form for summing over matchings, which is what an amplitude does.

Neither representation is preferable and both are needed, so this file makes them
the same thing: a matching built by exchange can be handed to the amplitude, and a
matching indexing an amplitude term can be exchanged.  Everything here is uniform
in the vertex set.
-/

namespace MatchingBridge

open MatchingParity Amplitude

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A pairing, viewed as a permutation, is one of the matchings the amplitude
sums over. -/
theorem toPerm_mem_pairings (σ : Pairing V) : σ.toPerm ∈ pairings V := by
  simp only [pairings, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun x => σ.partner_partner x, fun x => σ.partner_ne x⟩

/-- A permutation the amplitude sums over is a pairing. -/
def ofMem {σ : Equiv.Perm V} (h : σ ∈ pairings V) : Pairing V where
  partner := σ
  partner_partner := ((Finset.mem_filter.mp h).2).1
  partner_ne := ((Finset.mem_filter.mp h).2).2

@[simp] theorem ofMem_partner {σ : Equiv.Perm V} (h : σ ∈ pairings V) (x : V) :
    (ofMem h).partner x = σ x := rfl

@[simp] theorem toPerm_ofMem {σ : Equiv.Perm V} (h : σ ∈ pairings V) :
    (ofMem h).toPerm = σ := by
  ext x
  rfl

@[simp] theorem ofMem_toPerm (σ : Pairing V) :
    ofMem (toPerm_mem_pairings σ) = σ := rfl

/-- **Exchange delivered to the amplitude.**  Exchanging two matchings along a set
closed under both produces a matching the amplitude sums over. -/
theorem exchange_mem_pairings (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s) :
    (σ.exchange τ s hσ hτ).toPerm ∈ pairings V :=
  toPerm_mem_pairings _

/-- **The edges of an exchange.**  Inside the closed set the edges are the second
matching's, outside they are the first's.  This is the computation every sign
argument runs: the amplitude term of an exchange differs from the original exactly
in the factors indexed by the exchanged set. -/
theorem edges_exchange (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s) :
    edges (σ.exchange τ s hσ hτ).toPerm
      = s.image (fun x => s(x, τ.partner x)) ∪ sᶜ.image (fun x => s(x, σ.partner x)) := by
  classical
  unfold edges
  rw [← Finset.union_compl s, Finset.image_union]
  congr 1
  · refine Finset.image_congr (fun x hx => ?_)
    rw [Pairing.toPerm_apply, Pairing.exchange_of_mem σ τ s hσ hτ hx]
  · refine Finset.image_congr (fun x hx => ?_)
    rw [Pairing.toPerm_apply,
      Pairing.exchange_of_notMem σ τ s hσ hτ (Finset.mem_compl.mp hx)]

/-! ### The sign an exchange produces

Everything outside the exchanged set is untouched, so comparing an exchange to
its original reduces to comparing the two matchings inside the set.  This is what
makes exchange a usable source of sign-reversing involutions: the criterion is
local to the set exchanged, and the rest of the matching never enters.
-/

variable {C : Type*} {R : Type*} [CommSemiring R]

/-- The product of the weights of a matching's edges met by a vertex set. -/
def edgeProd (W : Sym2 (V × C) → R) (c : V → C) (ρ : Pairing V) (A : Finset V) : R :=
  ∏ e ∈ A.image (fun x => s(x, ρ.partner x)), W (Sym2.map (paint c) e)

/-- A matching's edges split along any vertex set. -/
theorem edges_split (ρ : Pairing V) (A : Finset V) :
    edges ρ.toPerm
      = A.image (fun x => s(x, ρ.partner x)) ∪ Aᶜ.image (fun x => s(x, ρ.partner x)) := by
  classical
  unfold edges
  rw [← Finset.union_compl A, Finset.image_union]
  simp only [Pairing.toPerm_apply]

/-- Along a *closed* set the split is disjoint: an edge with one endpoint inside
has both inside, and an edge with one endpoint outside has both outside. -/
theorem disjoint_edges_image (ρ : Pairing V) {A : Finset V}
    (hA : ∀ x ∈ A, ρ.partner x ∈ A) :
    Disjoint (A.image (fun x => s(x, ρ.partner x)))
      (Aᶜ.image (fun x => s(x, ρ.partner x))) := by
  classical
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

/-- The edge product of a matching factors across a closed set. -/
theorem prod_edges_split (W : Sym2 (V × C) → R) (c : V → C) (ρ : Pairing V)
    {A : Finset V} (hA : ∀ x ∈ A, ρ.partner x ∈ A) :
    (∏ e ∈ edges ρ.toPerm, W (Sym2.map (paint c) e))
      = edgeProd W c ρ A * edgeProd W c ρ Aᶜ := by
  rw [edges_split ρ A, Finset.prod_union (disjoint_edges_image ρ hA)]
  rfl

omit [Fintype V] in
/-- An exchanged set is still closed under the exchange. -/
theorem exchange_closed (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s) :
    ∀ x ∈ s, (σ.exchange τ s hσ hτ).partner x ∈ s := by
  intro x hx
  rw [Pairing.exchange_of_mem σ τ s hσ hτ hx]
  exact hτ x hx

omit [Fintype V] in
/-- Inside the exchanged set, the exchange's edge product is the second
matching's. -/
theorem edgeProd_exchange_inside (W : Sym2 (V × C) → R) (c : V → C)
    (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s) :
    edgeProd W c (σ.exchange τ s hσ hτ) s = edgeProd W c τ s := by
  classical
  unfold edgeProd
  congr 1
  refine Finset.image_congr (fun x hx => ?_)
  rw [Pairing.exchange_of_mem σ τ s hσ hτ hx]

/-- Outside it, the exchange's edge product is the first matching's. -/
theorem edgeProd_exchange_outside (W : Sym2 (V × C) → R) (c : V → C)
    (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s) :
    edgeProd W c (σ.exchange τ s hσ hτ) sᶜ = edgeProd W c σ sᶜ := by
  classical
  unfold edgeProd
  congr 1
  refine Finset.image_congr (fun x hx => ?_)
  rw [Pairing.exchange_of_notMem σ τ s hσ hτ (Finset.mem_compl.mp hx)]

/-- **The exchange's amplitude term.**  It is the second matching's product inside
the exchanged set times the first matching's product outside. -/
theorem prod_edges_exchange (W : Sym2 (V × C) → R) (c : V → C)
    (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s) :
    (∏ e ∈ edges (σ.exchange τ s hσ hτ).toPerm, W (Sym2.map (paint c) e))
      = edgeProd W c τ s * edgeProd W c σ sᶜ := by
  rw [prod_edges_split W c _ (exchange_closed σ τ s hσ hτ),
    edgeProd_exchange_inside, edgeProd_exchange_outside]

section SignCriterion

variable {S : Type*} [CommRing S]

/-- **The sign criterion for exchange.**  An exchange negates the amplitude term
exactly when it negates the weight product inside the exchanged set.  Everything
outside is untouched and cancels from the comparison, so the criterion never
mentions the rest of the matching.

This is the hypothesis the involution principle asks for, reduced to a statement
about one closed set. -/
theorem prod_edges_exchange_eq_neg (W : Sym2 (V × C) → S) (c : V → C)
    (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s)
    (h : edgeProd W c τ s = -edgeProd W c σ s) :
    (∏ e ∈ edges (σ.exchange τ s hσ hτ).toPerm, W (Sym2.map (paint c) e))
      = -∏ e ∈ edges σ.toPerm, W (Sym2.map (paint c) e) := by
  rw [prod_edges_exchange, prod_edges_split W c σ hσ, h]
  ring

end SignCriterion

end MatchingBridge
