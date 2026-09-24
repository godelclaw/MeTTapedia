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

section Cut

variable {R' : Type*} [CommRing R'] {C' : Type*}

omit [Fintype C] in
/-- Matching sums split over a cut that no nonzero weight crosses. -/
theorem pmSum_union_of_no_crossing (W : Sym2 (V × C') → R') (c : V → C') {X Y : Finset V}
    (hXY : Disjoint X Y) (hcut : ∀ x ∈ X, ∀ y ∈ Y, W s((x, c x), (y, c y)) = 0) :
    pmSum W c (X ∪ Y) = pmSum W c X * pmSum W c Y := by
  rw [pmSum_factor_of_no_crossing W c X.card X (X ∪ Y) rfl Finset.subset_union_left
    (fun x hx y hy => hcut x hx y (by
      rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hXY.symm] at hy; exact hy)),
    Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hXY.symm]

omit [Fintype C] in
/-- **Two free sites over an odd cut.**  If the remaining sites split into two parts of odd size
that no nonzero weight crosses, then the two free sites are matched into different parts, and the
matching sum is a sum of two products. -/
theorem pmSum_two_over_odd_cut (W : Sym2 (V × C') → R') (c : V → C') {u v : V} {A B : Finset V}
    (huv : u ≠ v) (hAB : Disjoint A B) (huA : u ∉ A) (huB : u ∉ B) (hvA : v ∉ A) (hvB : v ∉ B)
    (hA : ¬ Even A.card) (hB : ¬ Even B.card)
    (hcut : ∀ x ∈ A, ∀ y ∈ B, W s((x, c x), (y, c y)) = 0) :
    pmSum W c (insert u (insert v (A ∪ B)))
      = (∑ w ∈ A, W (Sym2.map (paint c) s(u, w)) * pmSum W c (A.erase w))
          * (∑ l ∈ B, W (Sym2.map (paint c) s(v, l)) * pmSum W c (B.erase l))
        + (∑ w ∈ B, W (Sym2.map (paint c) s(u, w)) * pmSum W c (B.erase w))
          * (∑ l ∈ A, W (Sym2.map (paint c) s(v, l)) * pmSum W c (A.erase l)) := by
  have hcutXY : ∀ X ⊆ A, ∀ Y ⊆ B, pmSum W c (X ∪ Y) = pmSum W c X * pmSum W c Y :=
    fun X hX Y hY => pmSum_union_of_no_crossing W c (hAB.mono hX hY)
      fun x hx y hy => hcut x (hX hx) y (hY hy)
  have huT : u ∉ A ∪ B := by simp [huA, huB]
  have hvT : v ∉ A ∪ B := by simp [hvA, hvB]
  rw [pmSum_expand_pair W c (p := u) (q := v) (Finset.mem_insert_self u _) (by simp [Ne.symm huv]),
    Finset.erase_insert (by simp [huv, huT]), Finset.erase_insert hvT,
    hcutXY A (Finset.Subset.refl _) B (Finset.Subset.refl _), pmSum_of_odd W c hA, zero_mul, mul_zero, zero_add]
  -- each remaining term: expand at `v`
  have hinner : ∀ w ∈ A ∪ B, pmSum W c ((insert v (A ∪ B)).erase w)
      = ∑ l ∈ (A ∪ B).erase w, W (Sym2.map (paint c) s(v, l))
          * pmSum W c (((A ∪ B).erase w).erase l) := by
    intro w hw
    have hwv : w ≠ v := fun e => hvT (e ▸ hw)
    rw [Finset.erase_insert_of_ne (Ne.symm hwv),
      pmSum_expand W c (Finset.mem_insert_self v _),
      Finset.erase_insert (fun h => hvT (Finset.mem_of_mem_erase h))]
  rw [Finset.sum_congr rfl fun w hw => by rw [hinner w hw], Finset.sum_union hAB]
  have hA0 : pmSum W c A = 0 := pmSum_of_odd W c hA
  have hB0 : pmSum W c B = 0 := pmSum_of_odd W c hB
  -- a site of `A` first
  have partA : ∀ w ∈ A, ∑ l ∈ (A ∪ B).erase w, W (Sym2.map (paint c) s(v, l))
        * pmSum W c (((A ∪ B).erase w).erase l)
      = ∑ l ∈ B, W (Sym2.map (paint c) s(v, l)) * (pmSum W c (A.erase w) * pmSum W c (B.erase l)) := by
    intro w hw
    have hwB : w ∉ B := Finset.disjoint_left.mp hAB hw
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hwB,
      Finset.sum_union (hAB.mono_left (Finset.erase_subset w A))]
    rw [Finset.sum_eq_zero (fun l hl => by
      have hlB : l ∉ B := Finset.disjoint_left.mp hAB (Finset.mem_of_mem_erase hl)
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hlB,
        hcutXY _ ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) B (Finset.Subset.refl _), hB0,
        mul_zero, mul_zero]), zero_add]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlA : l ∉ A.erase w := fun h => Finset.disjoint_left.mp hAB (Finset.mem_of_mem_erase h) hl
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hlA,
      hcutXY _ (Finset.erase_subset w A) _ (Finset.erase_subset l B)]
  -- a site of `B` first
  have partB : ∀ w ∈ B, ∑ l ∈ (A ∪ B).erase w, W (Sym2.map (paint c) s(v, l))
        * pmSum W c (((A ∪ B).erase w).erase l)
      = ∑ l ∈ A, W (Sym2.map (paint c) s(v, l)) * (pmSum W c (A.erase l) * pmSum W c (B.erase w)) := by
    intro w hw
    have hwA : w ∉ A := Finset.disjoint_right.mp hAB hw
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hwA,
      Finset.sum_union (hAB.mono_right (Finset.erase_subset w B))]
    rw [Finset.sum_eq_zero (s := B.erase w) (fun l hl => by
      have hlA : l ∉ A := Finset.disjoint_right.mp hAB (Finset.mem_of_mem_erase hl)
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hlA,
        hcutXY A (Finset.Subset.refl _) _ ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)), hA0,
        zero_mul, mul_zero]), add_zero]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlB : l ∉ B.erase w := fun h => Finset.disjoint_left.mp hAB hl (Finset.mem_of_mem_erase h)
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hlB,
      hcutXY _ (Finset.erase_subset l A) _ (Finset.erase_subset w B)]
  have h1 : ∑ w ∈ A, W (Sym2.map (paint c) s(u, w)) * ∑ l ∈ (A ∪ B).erase w,
        W (Sym2.map (paint c) s(v, l)) * pmSum W c (((A ∪ B).erase w).erase l)
      = ∑ w ∈ A, W (Sym2.map (paint c) s(u, w)) * ∑ l ∈ B,
        W (Sym2.map (paint c) s(v, l)) * (pmSum W c (A.erase w) * pmSum W c (B.erase l)) :=
    Finset.sum_congr rfl fun w hw => by rw [partA w hw]
  have h2 : ∑ w ∈ B, W (Sym2.map (paint c) s(u, w)) * ∑ l ∈ (A ∪ B).erase w,
        W (Sym2.map (paint c) s(v, l)) * pmSum W c (((A ∪ B).erase w).erase l)
      = ∑ w ∈ B, W (Sym2.map (paint c) s(u, w)) * ∑ l ∈ A,
        W (Sym2.map (paint c) s(v, l)) * (pmSum W c (A.erase l) * pmSum W c (B.erase w)) :=
    Finset.sum_congr rfl fun w hw => by rw [partB w hw]
  rw [h1, h2, Finset.sum_mul_sum, Finset.sum_mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

end Cut

end MatchingSiteVectors
