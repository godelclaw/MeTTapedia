import Mathlib
import Mettapedia.Combinatorics.Matching.Amplitude

/-!
# Gauge freedom in the weights

Attaching a factor to each colour and multiplying every weight by the factors of
its two endpoints rescales the whole amplitude by a single number: the product of
the factors over the vertices, read through the colouring.  The rescaling is
uniform across matchings because every matching covers every vertex exactly once,
so the same factors appear in every term.


Everything is uniform in the vertex set.
-/

namespace Gauge

open Amplitude

variable {V C : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]

/-- The rescaling factor of an edge: the product of the factors of its two
endpoints' colours. -/
def colourScale (s : C → R) : Sym2 (V × C) → R :=
  Sym2.lift ⟨fun p q => s p.2 * s q.2, fun _ _ => mul_comm _ _⟩

/-- **Every matching collects the same factors.**  A matching covers each vertex
exactly once, so the product of its edge factors is the product over all vertices,
independent of which matching it is. -/
theorem prod_colourScale {σ : Equiv.Perm V} (hσ : σ ∈ pairings V) (c : V → C) (s : C → R) :
    ∏ e ∈ edges σ, colourScale s (Sym2.map (paint c) e) = ∏ v : V, s (c v) := by
  obtain ⟨hinv, hnf⟩ := (Finset.mem_filter.mp hσ).2
  have hmaps : ∀ v ∈ (Finset.univ : Finset V), s(v, σ v) ∈ edges σ :=
    fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ v)
  rw [← Finset.prod_fiberwise_of_maps_to hmaps]
  refine Finset.prod_congr rfl (fun e he => ?_)
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp he
  have hfib : (Finset.univ.filter (fun x => s(x, σ x) = s(a, σ a))) = {a, σ a} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, hinv a⟩
  rw [hfib, Finset.prod_insert (by simpa using Ne.symm (hnf a)), Finset.prod_singleton]
  rfl

/-- **The amplitude under rescaling.**  Multiplying every weight by its endpoints'
colour factors multiplies the amplitude by one number, the same for every term. -/
theorem amplitude_colourScale (W : Sym2 (V × C) → R) (c : V → C) (s : C → R) :
    amplitude (fun e => colourScale s e * W e) c = (∏ v : V, s (c v)) * amplitude W c := by
  rw [amplitude, amplitude, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [← prod_colourScale hσ c s, ← Finset.prod_mul_distrib]

/-! ### The full gauge: a factor at every site, in every colour

The rescaling above attaches a factor to each *colour*.  The equations tolerate far more: a factor
at every site in every colour, independently.  Every matching still covers every site exactly once,
so the amplitude again picks up a single number -- now the product over sites of the factor at the
colour that site is wearing.

A nowhere-vanishing gauge never moves the zero pattern.  Consequently any
support property is constant on gauge orbits, while cycle products supply
natural gauge-covariant quantities. -/

/-- The rescaling factor of an edge under a factor at each site in each colour. -/
def siteScale (μ : V × C → R) : Sym2 (V × C) → R :=
  Sym2.lift ⟨fun p q => μ p * μ q, fun _ _ => mul_comm _ _⟩

/-- **Every matching collects the same site factors.** -/
theorem prod_siteScale {σ : Equiv.Perm V} (hσ : σ ∈ pairings V) (c : V → C) (μ : V × C → R) :
    ∏ e ∈ edges σ, siteScale μ (Sym2.map (paint c) e) = ∏ v : V, μ (v, c v) := by
  obtain ⟨hinv, hnf⟩ := (Finset.mem_filter.mp hσ).2
  have hmaps : ∀ v ∈ (Finset.univ : Finset V), s(v, σ v) ∈ edges σ :=
    fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ v)
  rw [← Finset.prod_fiberwise_of_maps_to hmaps]
  refine Finset.prod_congr rfl (fun e he => ?_)
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp he
  have hfib : (Finset.univ.filter (fun x => s(x, σ x) = s(a, σ a))) = {a, σ a} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, hinv a⟩
  rw [hfib, Finset.prod_insert (by simpa using Ne.symm (hnf a)), Finset.prod_singleton]
  rfl

/-- **The amplitude under the full gauge.** -/
theorem amplitude_siteScale (W : Sym2 (V × C) → R) (c : V → C) (μ : V × C → R) :
    amplitude (fun e => siteScale μ e * W e) c = (∏ v : V, μ (v, c v)) * amplitude W c := by
  rw [amplitude, amplitude, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [← prod_siteScale hσ c μ, ← Finset.prod_mul_distrib]

/-- **The gauge never moves the support.**  A weight vanishes after rescaling exactly when it
vanished before, so support minimality is a property of the whole gauge orbit. -/
theorem siteScale_ne_zero_iff {R : Type*} [CommRing R] [NoZeroDivisors R]
    (W : Sym2 (V × C) → R) (μ : V × C → R) (hμ : ∀ p, μ p ≠ 0) (p q : V × C) :
    siteScale μ s(p, q) * W s(p, q) ≠ 0 ↔ W s(p, q) ≠ 0 := by
  constructor
  · intro h hw
    exact h (by rw [hw, mul_zero])
  · intro hw h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      exacts [hμ p h'', hμ q h'']
    · exact hw h'

/-- **The pair identity is gauge-invariant.**  Both of its products pick up the same factor -- the
four site factors of the four endpoints -- so the whole expression rescales rather than changing
shape.  The identity is therefore a statement about the gauge orbit, not about a representative,
and any normalization the weights are put into leaves it standing.

This is what makes a cycle product the right currency.  The gauge cannot move the support and
cannot alter this expression except by an overall factor, so the conditions it imposes are the
ones a weight-level argument has to work with. -/
theorem quad_identity_siteScale (W : Sym2 (V × C) → R) (μ : V × C → R)
    (a b x y : V) (k : C) :
    siteScale μ s((a, k), (x, k)) * W s((a, k), (x, k))
        * (siteScale μ s((b, k), (y, k)) * W s((b, k), (y, k)))
      + siteScale μ s((a, k), (y, k)) * W s((a, k), (y, k))
        * (siteScale μ s((b, k), (x, k)) * W s((b, k), (x, k)))
      = (μ (a, k) * μ (b, k) * μ (x, k) * μ (y, k))
        * (W s((a, k), (x, k)) * W s((b, k), (y, k))
          + W s((a, k), (y, k)) * W s((b, k), (x, k))) := by
  simp only [siteScale, Sym2.lift_mk]
  ring

end Gauge
