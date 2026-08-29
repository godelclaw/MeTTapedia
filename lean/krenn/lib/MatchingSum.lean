import Amplitude
import Mettapedia.Combinatorics.Matching.Sum

/-!
# Krenn–Gu matching-sum consequences

The reusable subset matching sum, deletion calculus, locality, relabelling, and
perturbation theory live in `Mettapedia.Combinatorics.Matching.Sum`.  This file
retains the three-colour GHZ equations and descent statements.
-/

namespace MatchingSum

open MatchingParity Amplitude

variable {V C : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommSemiring R]

/-- **The vertex equations.**  For a normalised solution, fixing a vertex `u` and a
background colour `k`, the matching sums of the complements of `u`'s incident edges
satisfy one linear equation for each colour `u` could wear: the coefficients are
`u`'s own weights, the right-hand side is one when the colour matches the
background and zero otherwise.

The unknowns are indexed by `u`'s partners, so the system's size is `u`'s degree.
Nothing in it grows with the vertex count. -/
theorem vertex_equations [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (k j : Fin 3) (hV : 2 ≤ Fintype.card V) :
    (∑ v ∈ Finset.univ.erase u,
        W s((u, j), (v, k)) *
          pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v))
      = if j = k then 1 else 0 := by
  classical
  set c : V → Fin 3 := Function.update (Amplitude.const k) u j with hc
  have hcu : c u = j := by rw [hc, Function.update_self]
  have hcv : ∀ v, v ≠ u → c v = k := fun v hv => by
    rw [hc, Function.update_of_ne hv]; rfl
  have hexp := amplitude_eq_sum_pmSum W c u
  have hterms : ∀ v ∈ Finset.univ.erase u,
      W (Sym2.map (paint c) s(u, v)) * pmSum W c ((Finset.univ.erase u).erase v)
        = W s((u, j), (v, k)) *
            pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v) := by
    intro v hv
    have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    have hedge : Sym2.map (paint c) s(u, v) = s((u, j), (v, k)) := by
      rw [show Sym2.map (paint c) s(u, v) = s((u, c u), (v, c v)) from rfl, hcu, hcv v hvu]
    rw [hedge, hc, pmSum_update_of_notMem W (Amplitude.const k) u j
      (fun hmem => Finset.notMem_erase u Finset.univ (Finset.mem_of_mem_erase hmem))]
  have hsum : (∑ v ∈ Finset.univ.erase u,
      W s((u, j), (v, k)) *
        pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v)) = amplitude W c := by
    rw [hexp]
    exact (Finset.sum_congr rfl hterms).symm
  rw [hsum]
  by_cases hjk : j = k
  · rw [if_pos hjk]
    have : c = Amplitude.const k := by
      funext v
      by_cases hv : v = u
      · rw [hv, hcu, hjk]; rfl
      · rw [hcv v hv]; rfl
    rw [this]
    exact hone k
  · rw [if_neg hjk]
    refine hzero c ?_
    rintro ⟨b, hb⟩
    obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) u
    exact hjk (hcu.symm.trans ((hb u).trans ((hb w).symm.trans (hcv w hw))))

/-! ### Capping a solution at a pair of vertices

A *cap* is a bilinear form on the colours, applied at two chosen vertices: sum the
amplitude over all colours those two might wear, weighted by the form.

When the form has constant diagonal, capping the target returns the target on two
fewer vertices, scaled.  The reason is that the target is supported on the constant
colourings, so only the diagonal of the form is ever consulted — every off-diagonal
entry meets a colouring that is not constant, and those contribute nothing.

This is what makes a cap a candidate reduction: it does to the *target* exactly what
one wants, leaving the whole difficulty on the side of what it does to the solution.
-/

/-- The cap of an amplitude at a pair of vertices, by a bilinear form on colours. -/
noncomputable def capAmp (W : Sym2 (V × Fin 3) → ℂ) (C : Fin 3 → Fin 3 → ℂ)
    (p q : V) (cR : V → Fin 3) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    C a b * amplitude W (Function.update (Function.update cR p a) q b)

/-- **A constant-diagonal cap returns the target, scaled.**  On a colouring constant
away from the capped pair, the cap of a solution's amplitude is the diagonal value. -/
theorem capAmp_of_const (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p q : V} (hpq : q ≠ p) (C : Fin 3 → Fin 3 → ℂ) (κ : ℂ) (hκ : ∀ a, C a a = κ)
    (cR : V → Fin 3) (v : Fin 3) (hconst : ∀ x, x ≠ p → x ≠ q → cR x = v)
    {w : V} (hwp : w ≠ p) (hwq : w ≠ q) :
    capAmp W C p q cR = κ := by
  classical
  have hval : ∀ a b : Fin 3,
      Function.update (Function.update cR p a) q b p = a ∧
      Function.update (Function.update cR p a) q b q = b ∧
      ∀ x, x ≠ p → x ≠ q →
        Function.update (Function.update cR p a) q b x = v := by
    intro a b
    refine ⟨?_, ?_, ?_⟩
    · rw [Function.update_of_ne hpq.symm, Function.update_self]
    · rw [Function.update_self]
    · intro x hxp hxq
      rw [Function.update_of_ne hxq, Function.update_of_ne hxp, hconst x hxp hxq]
  have hterm : ∀ a b : Fin 3,
      amplitude W (Function.update (Function.update cR p a) q b)
        = if a = v ∧ b = v then 1 else 0 := by
    intro a b
    obtain ⟨hp, hq, hr⟩ := hval a b
    by_cases h : a = v ∧ b = v
    · rw [if_pos h]
      have : Function.update (Function.update cR p a) q b = Amplitude.const v := by
        funext x
        by_cases hxp : x = p
        · rw [hxp, hp, h.1]; rfl
        · by_cases hxq : x = q
          · rw [hxq, hq, h.2]; rfl
          · rw [hr x hxp hxq]; rfl
      rw [this]; exact hone v
    · rw [if_neg h]
      refine hzero _ (fun ⟨m, hm⟩ => h ⟨?_, ?_⟩)
      · rw [← hp, hm p, ← hm w, hr w hwp hwq]
      · rw [← hq, hm q, ← hm w, hr w hwp hwq]
  unfold capAmp
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hterm a b]))]
  fin_cases v <;> simp [Fin.sum_univ_three, hκ]

/-! ### No colouring may have a unique compatible matching

Call a matching *compatible* with a colouring when every one of its edges carries a
nonzero weight at the colours that colouring gives the edge's endpoints.  Only
compatible matchings contribute to an amplitude.

If a non-constant colouring had exactly one compatible matching, that matching's
product would be the whole amplitude.  The amplitude must vanish; a product of
nonzero factors does not.  So every non-constant colouring has either no compatible
matching or at least two.

This is the combinatorial heart of the argument that rules out the
colour-per-matching constructions, said for arbitrary weight systems.  It reduces a
question about complex weights to one about the *supports* alone: to refute a
candidate support system it suffices to exhibit a single non-constant colouring
admitting exactly one matching.
-/

/-- **No non-constant colouring has a unique compatible matching.** -/
theorem not_unique_compatible (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (c : V → Fin 3) (hc : ¬ Amplitude.Monochromatic c)
    (σ : Equiv.Perm V) (hσ : σ ∈ pairings V)
    (hpos : (∏ e ∈ edges σ, W (Sym2.map (paint c) e)) ≠ 0)
    (huniq : ∀ τ ∈ pairings V, τ ≠ σ →
      (∏ e ∈ edges τ, W (Sym2.map (paint c) e)) = 0) :
    False := by
  have hamp := hzero c hc
  rw [amplitude, Finset.sum_eq_single σ (fun τ hτ hne => huniq τ hτ hne)
    (fun h => absurd hσ h)] at hamp
  exact hpos hamp

/-- **Two compatible matchings have opposite products.**  If a non-constant
colouring admits exactly two compatible matchings, their products are negatives of
one another.

This is the refinement that reaches where excluding a *unique* compatible matching
cannot.  Where that principle yields a contradiction only when a colouring singles
out one matching, this yields an *equation* whenever it singles out two — and when
those two differ by a single alternating four-cycle, the equation involves four
weights and nothing else. -/
theorem compatible_pair_neg (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (c : V → Fin 3) (hc : ¬ Amplitude.Monochromatic c)
    (σ τ : Equiv.Perm V) (hσ : σ ∈ pairings V) (hτ : τ ∈ pairings V) (hne : σ ≠ τ)
    (hrest : ∀ ρ ∈ pairings V, ρ ≠ σ → ρ ≠ τ →
      (∏ e ∈ edges ρ, W (Sym2.map (paint c) e)) = 0) :
    (∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      + (∏ e ∈ edges τ, W (Sym2.map (paint c) e)) = 0 := by
  have hamp := hzero c hc
  rwa [amplitude, Finset.sum_eq_add_of_mem σ τ hσ hτ hne
    (fun ρ hρ h => hrest ρ hρ h.1 h.2)] at hamp

/-- Read as a determinant: the two products are equal up to sign, so their
difference from a common factor is a vanishing two-by-two determinant whenever the
matchings share all but one alternating cycle. -/
theorem compatible_pair_eq_neg (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (c : V → Fin 3) (hc : ¬ Amplitude.Monochromatic c)
    (σ τ : Equiv.Perm V) (hσ : σ ∈ pairings V) (hτ : τ ∈ pairings V) (hne : σ ≠ τ)
    (hrest : ∀ ρ ∈ pairings V, ρ ≠ σ → ρ ≠ τ →
      (∏ e ∈ edges ρ, W (Sym2.map (paint c) e)) = 0) :
    (∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      = -(∏ e ∈ edges τ, W (Sym2.map (paint c) e)) := by
  have h := compatible_pair_neg W hzero c hc σ τ hσ hτ hne hrest
  linear_combination h

/-! ### The vertex equations at an arbitrary background

Fixing the background to a constant colour was a choice, and a lossy one.  Against
an arbitrary background colouring the same expansion holds, and when that
background is *not* constant away from the vertex, the right-hand side is zero for
**all three** colours the vertex could wear — not two out of three.

So every non-constant background supplies a vector annihilated by all three of the
vertex's weight rows at once.  That is a far stronger condition than the constant
background gives, and there is one for each of the exponentially many non-constant
backgrounds.
-/

/-- **All three rows annihilate a non-constant background.**  If a colouring is
already non-constant away from `u`, then whatever colour `u` takes the amplitude
vanishes, so the matching sums of the complements of `u`'s incident edges are
annihilated by every one of `u`'s weight rows. -/
theorem vertex_equations_of_not_const (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (c : V → Fin 3) {x y : V} (hx : x ≠ u) (hy : y ≠ u) (hxy : c x ≠ c y)
    (j : Fin 3) :
    (∑ v ∈ Finset.univ.erase u,
      W s((u, j), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v)) = 0 := by
  classical
  set c' : V → Fin 3 := Function.update c u j with hc'
  have hc'v : ∀ v : V, v ≠ u → c' v = c v := fun v hv => by
    rw [hc', Function.update_of_ne hv]
  have hexp := amplitude_eq_sum_pmSum W c' u
  have hterms : ∀ v ∈ Finset.univ.erase u,
      W (Sym2.map (paint c') s(u, v)) * pmSum W c' ((Finset.univ.erase u).erase v)
        = W s((u, j), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v) := by
    intro v hv
    have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    have hedge : Sym2.map (paint c') s(u, v) = s((u, j), (v, c v)) := by
      rw [show Sym2.map (paint c') s(u, v) = s((u, c' u), (v, c' v)) from rfl,
        hc', Function.update_self, ← hc', hc'v v hvu]
    rw [hedge, hc', pmSum_update_of_notMem W c u j
      (fun hmem => Finset.notMem_erase u Finset.univ (Finset.mem_of_mem_erase hmem))]
  have hnm : ¬ Amplitude.Monochromatic c' := by
    rintro ⟨b, hb⟩
    exact hxy (by rw [← hc'v x hx, hb x, ← hb y, hc'v y hy])
  rw [← Finset.sum_congr rfl hterms, ← hexp]
  exact hzero c' hnm

/-! ### A restriction every solution must satisfy at every vertex

The vertex equations say a single vector — the matching sums of the complements of
one vertex's incident edges — is annihilated by two rows of that vertex's weights
and sent to one by the third.  A vector cannot do that if the third row is a
combination of the other two.

So at *every* vertex of *every* solution, on *any* number of vertices, the weights
keeping that vertex monochromatic are linearly independent of the weights that do
not.  This is a restriction on an arbitrary counterexample, not a computation about
a fixed one.
-/

/-- **The monochromatic row is independent.**  At every vertex and every colour, the
weights that keep the vertex monochromatic are not a linear combination of the
weights that break it. -/
theorem monochromatic_row_independent [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : 2 ≤ Fintype.card V)
    (u : V) (k j₁ j₂ : Fin 3) (hj₁ : j₁ ≠ k) (hj₂ : j₂ ≠ k) (a b : ℂ)
    (h : ∀ v : V, v ≠ u → W s((u, k), (v, k))
      = a * W s((u, j₁), (v, k)) + b * W s((u, j₂), (v, k))) :
    False := by
  have e0 := vertex_equations W hone hzero u k k hV
  have e1 := vertex_equations W hone hzero u k j₁ hV
  have e2 := vertex_equations W hone hzero u k j₂ hV
  rw [if_pos rfl] at e0
  rw [if_neg hj₁] at e1
  rw [if_neg hj₂] at e2
  rw [Finset.sum_congr rfl (fun v hv => by rw [h v (Finset.mem_erase.mp hv).1]; ring :
      ∀ v ∈ Finset.univ.erase u,
      W s((u, k), (v, k)) *
          pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v)
        = a * (W s((u, j₁), (v, k)) *
            pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v))
          + b * (W s((u, j₂), (v, k)) *
            pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v))),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1, e2] at e0
  simp at e0

theorem exists_third_colour : ∀ k j : Fin 3, ∃ j₂ : Fin 3, j₂ ≠ k ∧ j₂ ≠ j := by decide

/-- **No vanishing combination involves the monochromatic row.**  At every vertex,
a linear relation among the three weight rows must give the monochromatic row
coefficient zero.

This does *not* make the three rows independent.  It is stated for one background
colour, and at that colour only the monochromatic row is independent of the other
two; the other two may well be dependent — indeed at a vertex of degree two they
must be. -/
theorem row_combination [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : 2 ≤ Fintype.card V)
    (u : V) (k j₁ j₂ : Fin 3) (hj₁ : j₁ ≠ k) (hj₂ : j₂ ≠ k)
    (a b c : ℂ)
    (h : ∀ v : V, v ≠ u →
      a * W s((u, j₁), (v, k)) + b * W s((u, j₂), (v, k)) + c * W s((u, k), (v, k)) = 0) :
    c = 0 := by
  by_contra hc
  refine monochromatic_row_independent W hone hzero hV u k j₁ j₂ hj₁ hj₂
    (-a / c) (-b / c) (fun v hv => ?_)
  have hvv := h v hv
  field_simp
  linear_combination hvv

/-- **Every vertex has a monochromatic partner.**  For each background colour there
is a partner whose edge carries a nonzero weight at that colour: the monochromatic
row never vanishes.

This is the whole of what one background colour gives.  It does *not* bound the
degree below by three: a vertex with one partner is consistent provided its
colour-breaking weights vanish, and a vertex with two is consistent provided a
determinant does.  The rows of a single background colour are not independent —
only the monochromatic one is independent of the other two. -/
theorem monochromatic_row_ne_zero [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : 2 ≤ Fintype.card V) (u : V) (k : Fin 3) :
    ∃ v : V, v ≠ u ∧ W s((u, k), (v, k)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j₁, hj₁k, -⟩ := exists_third_colour k k
  obtain ⟨j₂, hj₂k, -⟩ := exists_third_colour k j₁
  exact one_ne_zero
    (row_combination W hone hzero hV u k j₁ j₂ hj₁k hj₂k 0 0 1
      (fun v hv => by rw [hcon v hv]; ring))

/-- **A vertex with one partner is diagonal.**  If every weight at `u` vanishes
except on the edge to `v`, then every weight breaking `u`'s monochromacy vanishes
there too: the edge can only carry matching colours. -/
theorem degree_one_diagonal [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : 2 ≤ Fintype.card V)
    (u v : V) (k j : Fin 3) (hj : j ≠ k)
    (hdeg : ∀ w : V, w ≠ u → w ≠ v → ∀ i : Fin 3, W s((u, i), (w, k)) = 0) :
    W s((u, j), (v, k)) = 0 := by
  by_contra hne
  obtain ⟨j₂, hj₂k, -⟩ := exists_third_colour k j
  refine monochromatic_row_independent W hone hzero hV u k j j₂ hj hj₂k
    (W s((u, k), (v, k)) / W s((u, j), (v, k))) 0 (fun w hw => ?_)
  by_cases hwv : w = v
  · subst hwv
    rw [zero_mul, add_zero, div_mul_cancel₀ _ hne]
  · rw [hdeg w hw hwv k, hdeg w hw hwv j]
    ring

/-- **A vertex with two partners forces a determinant to vanish.**  If every weight
at `u` vanishes outside the edges to `v` and `w`, then the two colour-breaking rows
are linearly dependent on those two coordinates.

Otherwise they would span the plane, the monochromatic row would be a combination
of them, and no vector could be annihilated by both while being sent to one by the
third.  So low degree is not merely inconvenient for a solution — it imposes an
equation. -/
theorem degree_two_det [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : 2 ≤ Fintype.card V)
    (u v w : V) (k j₁ j₂ : Fin 3) (hj₁ : j₁ ≠ k) (hj₂ : j₂ ≠ k)
    (hdeg : ∀ x : V, x ≠ u → x ≠ v → x ≠ w → ∀ i : Fin 3, W s((u, i), (x, k)) = 0) :
    W s((u, j₁), (v, k)) * W s((u, j₂), (w, k))
      - W s((u, j₂), (v, k)) * W s((u, j₁), (w, k)) = 0 := by
  by_contra hdet
  set A := W s((u, j₁), (v, k)) with hA
  set B := W s((u, j₁), (w, k)) with hB
  set C := W s((u, j₂), (v, k)) with hC
  set D := W s((u, j₂), (w, k)) with hD
  set E := W s((u, k), (v, k)) with hE
  set F := W s((u, k), (w, k)) with hF
  set d := A * D - C * B with hdd
  have hd : d ≠ 0 := hdet
  have hv : E = ((E * D - C * F) / d) * A + ((A * F - E * B) / d) * C := by
    field_simp
    rw [hdd]
    ring
  have hw : F = ((E * D - C * F) / d) * B + ((A * F - E * B) / d) * D := by
    field_simp
    rw [hdd]
    ring
  refine monochromatic_row_independent W hone hzero hV u k j₁ j₂ hj₁ hj₂
    ((E * D - C * F) / d) ((A * F - E * B) / d) (fun x hx => ?_)
  by_cases hxv : x = v
  · rw [hxv]; exact hv
  · by_cases hxw : x = w
    · rw [hxw]; exact hw
    · rw [hdeg x hx hxv hxw k, hdeg x hx hxv hxw j₁, hdeg x hx hxv hxw j₂]
      ring

/-! ### Closing the gap between the two backgrounds

The constant background forces the vertex's vector to be nonzero but only two rows
annihilate it.  The non-constant background has all three rows annihilating but
gives no reason for the vector to be nonzero.  A contradiction needs both at once.

They meet.  Recolour a single vertex `v₀` away from the background.  The vector's
`v₀` coordinate is a matching sum over a set that *excludes* `v₀`, so by locality it
does not notice the recolouring — it is the same number as before.  Choose `v₀`
where the constant background already made it nonzero, and the resulting
non-constant background inherits a nonzero coordinate while gaining the third
annihilation.
-/

/-- **A non-constant background with a nonzero vector.**  For every vertex there is
a colouring, non-constant away from it, all three of whose weight rows annihilate a
vector that is not zero. -/
theorem exists_nonconst_background_nonzero [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : 3 ≤ Fintype.card V) (u : V) (k : Fin 3) :
    ∃ (c : V → Fin 3) (v₀ x y : V), x ≠ u ∧ y ≠ u ∧ c x ≠ c y ∧
      v₀ ∈ Finset.univ.erase u ∧
      pmSum W c ((Finset.univ.erase u).erase v₀) ≠ 0 := by
  classical
  -- the constant background makes some coordinate nonzero
  have hk := vertex_equations W hone hzero u k k (by omega)
  rw [if_pos rfl] at hk
  obtain ⟨v₀, hv₀, hv₀ne⟩ : ∃ v₀ ∈ Finset.univ.erase u,
      W s((u, k), (v₀, k)) *
        pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact one_ne_zero (hk ▸ Finset.sum_eq_zero hcon)
  have hD : pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v₀) ≠ 0 :=
    fun h => hv₀ne (by rw [h, mul_zero])
  -- a third vertex, distinct from both
  obtain ⟨w, hw⟩ : (Finset.univ \ ({u, v₀} : Finset V)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ_sdiff]
    have : ({u, v₀} : Finset V).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    omega
  rw [Finset.mem_sdiff] at hw
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  obtain ⟨-, hwu, hwv₀⟩ := hw
  -- recolour v₀ only
  obtain ⟨m, hmk, -⟩ := exists_third_colour k k
  refine ⟨Function.update (Amplitude.const k) v₀ m, v₀, v₀, w,
    (Finset.mem_erase.mp hv₀).1, hwu, ?_, hv₀, ?_⟩
  · rw [Function.update_self, Function.update_of_ne hwv₀]
    exact fun h => hmk h
  · rw [pmSum_update_of_notMem W (Amplitude.const k) v₀ m (Finset.notMem_erase _ _)]
    exact hD

/-- **Every vertex of every solution is degenerate.**  At each vertex there is a
background colouring and a *nonzero* vector, indexed by that vertex's partners,
which all three of its weight rows annihilate.

This is the two halves put together: the constant background supplies the nonzero
coordinate, recolouring one vertex supplies the third annihilation, and locality
guarantees the recolouring does not disturb the coordinate that was nonzero.

The statement is uniform: it holds at every vertex, for any number of vertices, and
needs nothing of the solution but the defining equations.

**It can be vacuous, and often is.**  The nonzero coordinate is the vertex that was
recoloured, and recolouring it moves the row entry there to a different weight.  On
the four-vertex solution of `FourVertices` all three rows vanish at that coordinate
in every instance, so the annihilation holds for free and carries no information.

The tension is structural, not accidental: locality preserves the coordinate only
because the recoloured vertex is excluded from the matching sum, and that same
vertex is the one whose row entry the recolouring disturbs.

The criterion is sharp.  The normalisation that makes the coordinate nonzero
*requires* the edge `u`–`v₀` to carry weight when `v₀` wears the background colour.
The recoloured row entry is that same edge with `v₀` wearing a different colour.  So
the degeneracy is informative exactly when that edge carries weight at two different
colours of `v₀`, and vacuous when it carries weight at only one.

That is why the four-vertex solution defeats it in every instance: there every edge
carries weight at a single colour by construction.  Which suggests the split the
argument wants — solutions whose edges are single-coloured are of the
colour-per-matching kind and understood; the degeneracy has content only on the
others. -/
theorem vertex_degenerate [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : 3 ≤ Fintype.card V) (u : V) :
    ∃ c : V → Fin 3,
      (∃ v ∈ Finset.univ.erase u, pmSum W c ((Finset.univ.erase u).erase v) ≠ 0) ∧
      ∀ j : Fin 3, (∑ v ∈ Finset.univ.erase u,
        W s((u, j), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v)) = 0 := by
  obtain ⟨c, v₀, x, y, hx, hy, hxy, hv₀, hne⟩ :=
    exists_nonconst_background_nonzero W hone hzero hV u 0
  exact ⟨c, ⟨v₀, hv₀, hne⟩,
    fun j => vertex_equations_of_not_const W hzero u c hx hy hxy j⟩

/-! ### A solution on a vertex subset

The conjecture's remaining hypothesis relates a solution on `2n` vertices to one on
`2n - 2`, which as stated compares two different vertex *types*.  The subset
matching sum lets the same statement be made inside one type, where the library's
machinery applies to both sides at once.
-/

/-- A GHZ configuration carried by a vertex subset: every monochromatic matching
sum over `S` is nonzero, and every colouring not constant on `S` gives zero.

By locality this depends only on the weights of edges inside `S`, so it is a
statement about the induced subgraph however the weights behave elsewhere. -/
def IsGHZOn (W : Sym2 (V × Fin 3) → ℂ) (S : Finset V) : Prop :=
  (∀ k : Fin 3, pmSum W (Amplitude.const k) S ≠ 0) ∧
    (∀ c : V → Fin 3, ¬ (∀ x ∈ S, ∀ y ∈ S, c x = c y) → pmSum W c S = 0)

/-- On the whole vertex set this is the library's own notion of a solution. -/
theorem isGHZOn_univ_iff [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ) :
    IsGHZOn W Finset.univ ↔ KrennGu.IsGHZ W := by
  have hconst : ∀ c : V → Fin 3,
      (∀ x ∈ (Finset.univ : Finset V), ∀ y ∈ (Finset.univ : Finset V), c x = c y)
        ↔ Amplitude.Monochromatic c := by
    intro c
    constructor
    · intro h
      obtain ⟨x⟩ := ‹Nonempty V›
      exact ⟨c x, fun v => h v (Finset.mem_univ v) x (Finset.mem_univ x)⟩
    · rintro ⟨k, hk⟩ x - y -
      rw [hk, hk]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun c hc => ?_⟩
    · rw [← pmSum_univ]
      exact h1 k
    · rw [← pmSum_univ]
      exact h2 c (fun hh => hc ((hconst c).mp hh))
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun c hc => ?_⟩
    · rw [pmSum_univ]
      exact h1 k
    · rw [pmSum_univ]
      exact h2 c (fun hm => hc ((hconst c).mpr hm))

/-- **The remaining hypothesis, inside one vertex type.**  A solution on a subset of
at least eight vertices yields a solution on a subset two smaller.  The bound of
eight is the same one the conjecture needs: descent must never terminate at the
four-vertex case, which genuinely has a solution. -/
def DescentOn (V : Type*) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (W : Sym2 (V × Fin 3) → ℂ) (S : Finset V), 8 ≤ S.card → IsGHZOn W S →
    ∃ (W' : Sym2 (V × Fin 3) → ℂ) (S' : Finset V), S'.card + 2 = S.card ∧ IsGHZOn W' S'

/-- **A solution on a subset has even size.**  Odd sets carry no matchings at all, so their sums
vanish and the first condition fails.  Descent by two therefore stays inside the even world, which
is what makes the scheme's step size the right one. -/
theorem isGHZOn_even (W : Sym2 (V × Fin 3) → ℂ) {S : Finset V} (h : IsGHZOn W S) :
    Even S.card := by
  by_contra hodd
  exact h.1 0 (pmSum_of_odd W (Amplitude.const 0) hodd)

/-! ### The descent scheme reaches the official statement

`DescentOn` lives inside one vertex type, while `Descent` -- the hypothesis the official bridge
consumes -- is stated across types.  The two are connected by the transports already proved above:
a matching sum over a subset is the amplitude of the restricted system on the subtype, and
relabelling the sites along a bijection preserves amplitudes.  So a descent step proved inside one
vertex type does reach the official statement, and nothing further is needed to make it usable. -/

/-- **A solution on a subset is a solution on the subtype.** -/
theorem isGHZ_restrict_of_isGHZOn (W : Sym2 (V × Fin 3) → ℂ) {S : Finset V}
    (h : IsGHZOn W S) : KrennGu.IsGHZ (restrictW W S) := by
  classical
  refine ⟨fun k => ?_, fun c' hc' => ?_⟩
  · have := amplitude_restrictSites W S (Amplitude.const (V := V) k)
    have hfun : (fun u : ↥S => (Amplitude.const (V := V) k) (u : V))
        = Amplitude.const (V := ↥S) k := rfl
    rw [hfun] at this
    rw [this]
    exact h.1 k
  · set c : V → Fin 3 := fun v => if hv : v ∈ S then c' ⟨v, hv⟩ else 0 with hcdef
    have hfun : (fun u : ↥S => c (u : V)) = c' := by
      funext u
      simp only [hcdef, dif_pos u.2]
    have hrestr := amplitude_restrictSites W S c
    rw [hfun] at hrestr
    rw [hrestr]
    refine h.2 c (fun hconst => hc' ?_)
    obtain ⟨u⟩ : Nonempty ↥S := by
      by_contra hno
      exact hc' ⟨0, fun v => absurd ⟨v⟩ hno⟩
    refine ⟨c' u, fun v => ?_⟩
    exact (congrFun hfun v).symm.trans
      ((hconst (v : V) v.2 (u : V) u.2).trans (congrFun hfun u))

/-- **Descent inside one vertex type gives descent across types.** -/
theorem descent_of_descentOn (h : ∀ n : ℕ, DescentOn (Fin (2 * n))) : KrennGu.Descent := by
  classical
  intro n hn hsol
  obtain ⟨W, hW⟩ := hsol
  haveI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  have hGHZOn : IsGHZOn W Finset.univ := (isGHZOn_univ_iff W).mpr hW
  have hcard : 8 ≤ (Finset.univ : Finset (Fin (2 * n))).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨W', S', hS'card, hGHZOn'⟩ := h n W Finset.univ hcard hGHZOn
  have hSc : Fintype.card ↥S' = 2 * (n - 1) := by
    rw [Fintype.card_coe]
    have : (Finset.univ : Finset (Fin (2 * n))).card = 2 * n := by
      rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨e⟩ : Nonempty (Fin (2 * (n - 1)) ≃ ↥S') :=
    ⟨(Fintype.equivFinOfCardEq hSc).symm⟩
  refine ⟨relabelW (restrictW W' S') e, ?_⟩
  have hbase := isGHZ_restrict_of_isGHZOn W' hGHZOn'
  refine ⟨fun k => ?_, fun c hc => ?_⟩
  · have := amplitude_relabel (restrictW W' S') e (Amplitude.const (V := ↥S') k)
    have hfun : (fun u : Fin (2 * (n - 1)) => (Amplitude.const (V := ↥S') k) (e u))
        = Amplitude.const (V := Fin (2 * (n - 1))) k := rfl
    rw [hfun] at this
    rw [this]
    exact hbase.1 k
  · have hrel := amplitude_relabel (restrictW W' S') e (fun u : ↥S' => c (e.symm u))
    have hfun : (fun u : Fin (2 * (n - 1)) => (fun w : ↥S' => c (e.symm w)) (e u)) = c := by
      funext u; simp
    rw [hfun] at hrel
    rw [hrel]
    refine hbase.2 _ (fun hmono => hc ?_)
    obtain ⟨k, hk⟩ := hmono
    refine ⟨k, fun v => ?_⟩
    have := hk (e v)
    simpa using this

/-! ### A descent step from a pendant pair, and exactly what it is missing

Delete a site whose only live partner in some colour is its own pair-mate, together with that
mate.  Then every colouring that paints both of them that colour expands at the deleted site with
a *single* surviving term: the other candidates are dead either by the colour mismatch or by the
pendancy.  So the sum over the whole set is the deleted weight times the sum over the remainder.

Two of the three conditions for a solution come out of that at once.  The remainder's sum in the
pendant colour is non-zero, because the whole set's is and it factors.  And the remainder's sum
vanishes on every colouring non-constant there, because extending by the pendant colour keeps it
non-constant on the whole set, where it must vanish, and the factor divides out.

What is *not* delivered is the remainder's non-vanishing in the other two colours.  The deleted
pair is dead in them, so the factorization says nothing, and the sites that used to be matched
against the deleted pair in those colours are left to fend for themselves.

That is the whole of the remaining gap in the descent route, stated precisely: one non-vanishing,
in each of two colours, after deleting a pendant pair. -/

/-- **Deleting a pendant pair: the surviving term is unique.** -/
theorem pmSum_delete_pendant (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {S : Finset V} {u v : V} {k : Fin 3} (hu : u ∈ S) (hv : v ∈ S.erase u)
    (hpend : ∀ z ∈ S, z ≠ v → z ≠ u → W s((u, k), (z, k)) = 0)
    (c : V → Fin 3) (hcu : c u = k) (hcv : c v = k) :
    pmSum W c S = W s((u, k), (v, k)) * pmSum W c ((S.erase u).erase v) := by
  classical
  rw [pmSum_expand W c hu, Finset.sum_eq_single_of_mem v hv]
  · have hp : (Sym2.map (Amplitude.paint c) s(u, v)) = s((u, c u), (v, c v)) := rfl
    rw [hp, hcu, hcv]
  · intro z hz hzv
    have hzu : z ≠ u := Finset.ne_of_mem_erase hz
    have hzS : z ∈ S := Finset.mem_of_mem_erase hz
    have hp : (Sym2.map (Amplitude.paint c) s(u, z)) = s((u, c u), (z, c z)) := rfl
    rw [hp, hcu]
    by_cases hck : c z = k
    · rw [hck, hpend z hzS hzv hzu, zero_mul]
    · rw [hmono u z hzu k (c z) (fun hh => hck hh.symm), zero_mul]

/-- **Deleting a pendant pair delivers two of the three conditions.**  The remainder carries the
pendant colour, and vanishes on every colouring non-constant on it. -/
theorem descent_step_pendant (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {S : Finset V} (h : IsGHZOn W S) {u v : V} {k : Fin 3}
    (hu : u ∈ S) (hv : v ∈ S.erase u)
    (hpend : ∀ z ∈ S, z ≠ v → z ≠ u → W s((u, k), (z, k)) = 0) :
    pmSum W (Amplitude.const k) ((S.erase u).erase v) ≠ 0 ∧
      ∀ c' : V → Fin 3,
        ¬ (∀ x ∈ (S.erase u).erase v, ∀ y ∈ (S.erase u).erase v, c' x = c' y) →
        pmSum W c' ((S.erase u).erase v) = 0 := by
  classical
  have hconst := pmSum_delete_pendant W hmono hu hv hpend (Amplitude.const (V := V) k) rfl rfl
  have hne := h.1 k
  rw [hconst] at hne
  have hw : W s((u, k), (v, k)) ≠ 0 := fun hz => hne (by rw [hz, zero_mul])
  refine ⟨fun hz => hne (by rw [hz, mul_zero]), fun c' hc' => ?_⟩
  set T : Finset V := (S.erase u).erase v with hT
  set c : V → Fin 3 := fun z => if z ∈ T then c' z else k with hcdef
  have hcT : ∀ z ∈ T, c z = c' z := by intro z hz; simp only [hcdef, if_pos hz]
  have huT : u ∉ T := by simp [hT]
  have hvT : v ∉ T := by simp [hT]
  have hcu : c u = k := by simp only [hcdef, if_neg huT]
  have hcv : c v = k := by simp only [hcdef, if_neg hvT]
  have hkey := pmSum_delete_pendant W hmono hu hv hpend c hcu hcv
  have hzero : pmSum W c S = 0 := by
    refine h.2 c (fun hall => hc' (fun x hx y hy => ?_))
    rw [← hcT x hx, ← hcT y hy]
    exact hall x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
  rw [hzero] at hkey
  have : pmSum W c T = 0 := by
    rcases mul_eq_zero.mp hkey.symm with h1 | h1
    exacts [absurd h1 hw, h1]
  rw [← this]
  exact pmSum_congr_colour W (fun z hz => (hcT z hz).symm)

end MatchingSum
