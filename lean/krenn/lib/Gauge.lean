import Mathlib
import Amplitude

/-!
# Gauge freedom in the weights

Attaching a factor to each colour and multiplying every weight by the factors of
its two endpoints rescales the whole amplitude by a single number: the product of
the factors over the vertices, read through the colouring.  The rescaling is
uniform across matchings because every matching covers every vertex exactly once,
so the same factors appear in every term.

The consequence is that the normalisation demanded of a GHZ configuration — that
the monochromatic amplitudes be *one* rather than merely nonzero — costs nothing.
Any configuration with nonvanishing monochromatic amplitudes can be rescaled to
one with them equal to one, and the vanishing conditions survive because a nonzero
factor cannot turn a zero into anything else.

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

/-- **The normalisation is free.**  A GHZ configuration can be rescaled so that its
monochromatic amplitudes are exactly one, with every vanishing condition
preserved.  So requiring the value one rather than merely nonzero excludes no
solution. -/
theorem exists_normalized [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ) (h : KrennGu.IsGHZ W) :
    ∃ W' : Sym2 (V × Fin 3) → ℂ,
      (∀ k : Fin 3, amplitude W' (Amplitude.const k) = 1) ∧
      (∀ c : V → Fin 3, ¬ Monochromatic c → amplitude W' c = 0) := by
  obtain ⟨hne, hzero⟩ := h
  have hcard : 0 < Fintype.card V := Fintype.card_pos
  choose s hs using fun k : Fin 3 =>
    IsAlgClosed.exists_pow_nat_eq (amplitude W (Amplitude.const k))⁻¹ hcard
  refine ⟨fun e => colourScale s e * W e, fun k => ?_, fun c hc => ?_⟩
  · rw [amplitude_colourScale]
    have hprod : ∏ _v : V, s k = s k ^ Fintype.card V := by
      rw [Finset.prod_const, Finset.card_univ]
    have hconst : ∏ v : V, s (Amplitude.const k v) = s k ^ Fintype.card V := hprod
    rw [hconst, hs k, inv_mul_cancel₀ (hne k)]
  · rw [amplitude_colourScale, hzero c hc, mul_zero]


/-! ### The full gauge: a factor at every site, in every colour

The rescaling above attaches a factor to each *colour*.  The equations tolerate far more: a factor
at every site in every colour, independently.  Every matching still covers every site exactly once,
so the amplitude again picks up a single number -- now the product over sites of the factor at the
colour that site is wearing.

Two consequences worth having.  A GHZ configuration stays one under any nowhere-vanishing gauge,
so the group acting on solutions is `(V × colours)`-many scalars rather than three.  And the gauge
never moves the support: a weight is zero after rescaling exactly when it was zero before.  So
support minimality is a property of the whole gauge orbit, and any argument that hopes to use the
weights must use quantities the gauge cannot change -- products around cycles, and nothing else. -/

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

/-- **A solution stays a solution under any nowhere-vanishing gauge.** -/
theorem isGHZ_siteScale [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ) (μ : V × Fin 3 → ℂ)
    (hμ : ∀ p, μ p ≠ 0) (h : KrennGu.IsGHZ W) :
    KrennGu.IsGHZ (fun e => siteScale μ e * W e) := by
  classical
  refine ⟨fun k => ?_, fun c hc => ?_⟩
  · rw [amplitude_siteScale W (Amplitude.const (V := V) k) μ]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun v _ => hμ _)) (h.1 k)
  · rw [amplitude_siteScale W c μ, h.2 c hc, mul_zero]

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
