import Mathlib
import Mettapedia.Combinatorics.Matching.Sum

/-!
# Matching sums with a vector at every site

Put a vector `z p : C → R` at every site `p` and read each coloured weight against the vectors at
its two ends: the pair `pq` then carries the single number `∑ a b, z p a * z q b * W((p,a),(q,b))`.
The matching sum of these contracted weights is the matching sum of the original weights
contracted against the vectors: a sum over colourings, each weighted by the product of the vector
entries it selects (`pmSum_formW`).

Choosing the vectors so that some contracted weights vanish is how structure is forced: a site
whose contracted weights vanish towards all but a few partners has to be matched to one of those.
-/

namespace MatchingSiteVectors

open Amplitude MatchingSum

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
variable {R : Type*} [CommRing R]

/-- The weights read against a vector at every site, as a single-colour weighting. -/
def formW (W : Sym2 (V × C) → R) (z : V → C → R) : Sym2 (V × Unit) → R :=
  Sym2.lift ⟨fun x y => ∑ a, ∑ b, z x.1 a * z y.1 b * W s((x.1, a), (y.1, b)),
    fun x y => by
      dsimp only
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      rw [Sym2.eq_swap]
      ring⟩

omit [Fintype V] [DecidableEq V] in
theorem formW_apply (W : Sym2 (V × C) → R) (z : V → C → R) (p q : V) (i j : Unit) :
    formW W z s((p, i), (q, j)) = ∑ a, ∑ b, z p a * z q b * W s((p, a), (q, b)) := rfl

omit [Fintype V] [DecidableEq V] in
theorem formW_paint (W : Sym2 (V × C) → R) (z : V → C → R) (p q : V) :
    formW W z (Sym2.map (paint fun _ => ()) s(p, q))
      = ∑ a, ∑ b, z p a * z q b * W s((p, a), (q, b)) := rfl

/-- The colourings that agree with `c₀` off `S`. -/
def colourings (S : Finset V) (c₀ : V → C) : Finset (V → C) :=
  Fintype.piFinset fun p => if p ∈ S then Finset.univ else {c₀ p}

theorem mem_colourings {S : Finset V} {c₀ f : V → C} :
    f ∈ colourings S c₀ ↔ ∀ p, p ∉ S → f p = c₀ p := by
  simp only [colourings, Fintype.mem_piFinset]
  refine forall_congr' fun p => ?_
  split_ifs with h <;> simp [h]

theorem colourings_empty (c₀ : V → C) : colourings (∅ : Finset V) c₀ = {c₀} := by
  ext f
  simp only [mem_colourings, Finset.notMem_empty, not_false_eq_true, forall_const,
    Finset.mem_singleton]
  exact ⟨fun h => funext h, fun h p => by rw [h]⟩

/-- **Splitting off one site.**  A colouring agreeing with `c₀` off `insert u S` is a colour at
`u` together with a colouring agreeing with `c₀` off `S`. -/
theorem sum_colourings_insert (S : Finset V) (c₀ : V → C) {u : V} (hu : u ∉ S)
    (G : (V → C) → R) :
    ∑ f ∈ colourings (insert u S) c₀, G f
      = ∑ a, ∑ f ∈ colourings S c₀, G (Function.update f u a) := by
  rw [← Finset.sum_product' (s := Finset.univ) (t := colourings S c₀)
    (f := fun a f => G (Function.update f u a))]
  symm
  refine Finset.sum_nbij' (fun af => Function.update af.2 u af.1)
    (fun f => (f u, Function.update f u (c₀ u))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, f⟩ h
    simp only [Finset.mem_product, Finset.mem_univ, true_and] at h ⊢
    rw [mem_colourings] at h ⊢
    intro p hp
    have hpu : p ≠ u := fun e => hp (e ▸ Finset.mem_insert_self u S)
    rw [Function.update_of_ne hpu]
    exact h p fun h' => hp (Finset.mem_insert_of_mem h')
  · intro f h
    simp only [Finset.mem_product, Finset.mem_univ, true_and] at h ⊢
    rw [mem_colourings] at h ⊢
    intro p hp
    by_cases hpu : p = u
    · rw [hpu, Function.update_self]
    · rw [Function.update_of_ne hpu]
      exact h p fun h' => (Finset.mem_insert.mp h').elim hpu hp
  · rintro ⟨a, f⟩ h
    simp only [Finset.mem_product, Finset.mem_univ, true_and] at h
    rw [mem_colourings] at h
    simp only [Function.update_self, Function.update_idem, Prod.mk.injEq, true_and]
    funext p
    by_cases hpu : p = u
    · rw [hpu, Function.update_self, h u hu]
    · rw [Function.update_of_ne hpu]
  · intro f _
    simp only [Function.update_idem, Function.update_eq_self]
  · intro _ _
    rfl

/-- **The contracted matching sum is the contraction of the matching sum.** -/
theorem pmSum_formW (W : Sym2 (V × C) → R) (z : V → C → R) (c₀ : V → C) :
    ∀ S : Finset V, pmSum (formW W z) (fun _ => ()) S
      = ∑ f ∈ colourings S c₀, (∏ p ∈ S, z p (f p)) * pmSum W f S := by
  intro S
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · simp [colourings_empty]
    rw [pmSum_expand _ _ hu]
    -- expand each colouring's matching sum at `u` too, and exchange the sums
    have hR : ∑ f ∈ colourings S c₀, (∏ p ∈ S, z p (f p)) * pmSum W f S
        = ∑ v ∈ S.erase u, ∑ f ∈ colourings S c₀, (∏ p ∈ S, z p (f p)) *
            (W (Sym2.map (paint f) s(u, v)) * pmSum W f ((S.erase u).erase v)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [pmSum_expand W f hu, Finset.mul_sum]
    rw [hR]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    set S'' := (S.erase u).erase v with hS''
    have huS'' : u ∉ S'' := by simp [hS'']
    have hvS'' : v ∉ S'' := by simp [hS'']
    have hSeq : S = insert u (insert v S'') := by
      rw [hS'', Finset.insert_erase hv, Finset.insert_erase hu]
    have hcard : S''.card < n := by
      rw [← hn, hSeq, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hvS'']
      · omega
      · simp [hvu.symm, huS'']
    rw [ih _ hcard S'' rfl, formW_paint, Finset.sum_mul]
    conv_rhs => rw [hSeq]
    rw [sum_colourings_insert _ _ (by simp [hvu.symm, huS''])]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_colourings_insert _ _ hvS'', Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [mem_colourings] at hf
    have hgu : Function.update (Function.update f v b) u a u = a := Function.update_self ..
    have hgv : Function.update (Function.update f v b) u a v = b := by
      rw [Function.update_of_ne hvu, Function.update_self]
    have hgS : ∀ p ∈ S'', Function.update (Function.update f v b) u a p = f p := by
      intro p hp
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hp huS''),
        Function.update_of_ne (ne_of_mem_of_not_mem hp hvS'')]
    have hprod : ∏ p ∈ S'', z p (Function.update (Function.update f v b) u a p)
        = ∏ p ∈ S'', z p (f p) := Finset.prod_congr rfl fun p hp => by rw [hgS p hp]
    rw [Finset.prod_insert (by simp [hvu.symm, huS'']), Finset.prod_insert hvS'', hgu, hgv,
      hprod,
      show Sym2.map (paint (Function.update (Function.update f v b) u a)) s(u, v)
        = s((u, a), (v, b)) by
          rw [Sym2.map_mk]; simp only [paint, hgu, hgv],
      pmSum_congr_colour W hgS]
    ring

end MatchingSiteVectors
