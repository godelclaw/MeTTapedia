import Mathlib
import Mettapedia.Combinatorics.Matching.Pairing
import Mettapedia.Combinatorics.Matching.Amplitude

/-!
# The matching sum over a vertex subset

The amplitude sums over the perfect matchings of a whole vertex type.  Any
argument that reduces one vertex count to a smaller one needs the same sum indexed
by a *subset* of the vertices, since the smaller problem lives on fewer vertices
but must stay inside the same type.

A matching of a subset `S` is carried here by a permutation of the whole vertex
set: an involution that moves every vertex of `S` and fixes everything outside.
Nothing is lost — the matching is recovered by restriction — and the type never
changes, so a recursion that deletes two vertices stays in the same setting.

Everything below is uniform in the vertex set and in the subset.
-/

namespace MatchingSum

open MatchingParity Amplitude

variable {V C : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommSemiring R]

/-- The perfect matchings of a vertex subset `S`, carried by permutations of the
whole vertex set that fix everything outside `S`. -/
def pairingsOn (S : Finset V) : Finset (Equiv.Perm V) :=
  Finset.univ.filter
    (fun σ => (∀ x, σ (σ x) = x) ∧ (∀ x ∈ S, σ x ≠ x) ∧ (∀ x, x ∉ S → σ x = x))

theorem mem_pairingsOn {S : Finset V} {σ : Equiv.Perm V} :
    σ ∈ pairingsOn S ↔
      (∀ x, σ (σ x) = x) ∧ (∀ x ∈ S, σ x ≠ x) ∧ (∀ x, x ∉ S → σ x = x) := by
  simp [pairingsOn]

/-- A matching of `S` keeps `S` to itself: it has nowhere else to go. -/
theorem pairingsOn_closed {S : Finset V} {σ : Equiv.Perm V} (h : σ ∈ pairingsOn S) :
    ∀ x ∈ S, σ x ∈ S := by
  obtain ⟨hinv, hne, hout⟩ := mem_pairingsOn.mp h
  intro x hx
  by_contra hmem
  have h1 : σ (σ x) = σ x := hout _ hmem
  rw [hinv x] at h1
  exact hne x hx h1.symm

/-- Only sets of even size carry a matching. -/
theorem pairingsOn_eq_empty_of_odd {S : Finset V} (hS : ¬ Even S.card) :
    pairingsOn S = ∅ := by
  refine Finset.eq_empty_of_forall_notMem (fun σ hσ => ?_)
  obtain ⟨hinv, hne, -⟩ := mem_pairingsOn.mp hσ
  exact hS (even_card_of_closed_of_involutive hinv S (pairingsOn_closed hσ) hne)

/-- Nothing matches nothing, in exactly one way. -/
theorem pairingsOn_empty : pairingsOn (∅ : Finset V) = {1} := by
  ext σ
  rw [mem_pairingsOn, Finset.mem_singleton]
  constructor
  · rintro ⟨-, -, hout⟩
    ext x
    exact hout x (Finset.notMem_empty x)
  · rintro rfl
    exact ⟨fun x => rfl, fun x hx => absurd hx (Finset.notMem_empty x), fun x _ => rfl⟩

/-- **The matching sum over a vertex subset.**  Only the edges inside `S` are
weighted; the fixed points outside contribute nothing. -/
def pmSum (W : Sym2 (V × C) → R) (c : V → C) (S : Finset V) : R :=
  ∑ σ ∈ pairingsOn S, ∏ e ∈ S.image (fun x => s(x, σ x)), W (Sym2.map (paint c) e)

/-- The empty vertex set matches in one way, with an empty product. -/
@[simp] theorem pmSum_empty (W : Sym2 (V × C) → R) (c : V → C) :
    pmSum W c ∅ = 1 := by
  rw [pmSum, pairingsOn_empty]
  simp

/-- An odd vertex set has no matchings at all. -/
theorem pmSum_of_odd (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    (hS : ¬ Even S.card) : pmSum W c S = 0 := by
  rw [pmSum, pairingsOn_eq_empty_of_odd hS, Finset.sum_empty]

/-- On the whole vertex set the matching sum is the amplitude. -/
theorem pmSum_univ (W : Sym2 (V × C) → R) (c : V → C) :
    pmSum W c Finset.univ = amplitude W c := by
  rw [pmSum, amplitude]
  refine Finset.sum_congr ?_ (fun σ _ => rfl)
  ext σ
  constructor
  · intro h
    obtain ⟨hinv, hne, -⟩ := mem_pairingsOn.mp h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hinv, fun x => hne x (Finset.mem_univ x)⟩
  · intro h
    obtain ⟨hinv, hne⟩ := (Finset.mem_filter.mp h).2
    exact mem_pairingsOn.mpr
      ⟨hinv, fun x _ => hne x, fun x hx => absurd (Finset.mem_univ x) hx⟩

/-! ### The deletion recursion

Fix a vertex `u` of `S`.  Every matching of `S` sends `u` to some other vertex of
`S`, and deleting that pair leaves a matching of the rest.  Deleting the pair is
right multiplication by the transposition, which makes it a permutation for free
and makes the two directions inverse for free — the same device that carries
regrafting.

The result is the recursion every induction on vertex count runs on.
-/

variable {S : Finset V} {u v : V} {σ τ : Equiv.Perm V}

/-- Deleting the pair matched to `u`. -/
theorem mul_swap_mem_erase (hσ : σ ∈ pairingsOn S) (hu : u ∈ S) (hv : σ u = v) :
    σ * Equiv.swap u v ∈ pairingsOn ((S.erase u).erase v) := by
  obtain ⟨hinv, hne, hout⟩ := mem_pairingsOn.mp hσ
  have huv : u ≠ v := fun h => hne u hu (h ▸ hv)
  have hvu : σ v = u := by rw [← hv, hinv]
  have happ : ∀ x, (σ * Equiv.swap u v) x = σ (Equiv.swap u v x) := fun _ => rfl
  have hfu : (σ * Equiv.swap u v) u = u := by
    rw [happ, Equiv.swap_apply_left, hvu]
  have hfv : (σ * Equiv.swap u v) v = v := by
    rw [happ, Equiv.swap_apply_right, hv]
  have hoth : ∀ x, x ≠ u → x ≠ v → (σ * Equiv.swap u v) x = σ x := by
    intro x hxu hxv
    rw [happ, Equiv.swap_apply_of_ne_of_ne hxu hxv]
  -- a vertex other than `u` and `v` is sent to another such vertex
  have hstay : ∀ x, x ≠ u → x ≠ v → σ x ≠ u ∧ σ x ≠ v := by
    intro x hxu hxv
    refine ⟨fun h => hxv (by rw [← hv, ← h, hinv]), fun h => hxu (by rw [← hvu, ← h, hinv])⟩
  refine mem_pairingsOn.mpr ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · by_cases hxu : x = u
    · subst hxu; rw [hfu, hfu]
    · by_cases hxv : x = v
      · subst hxv; rw [hfv, hfv]
      · obtain ⟨h1, h2⟩ := hstay x hxu hxv
        rw [hoth x hxu hxv, hoth _ h1 h2, hinv]
  · obtain ⟨hxv, hx'⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxu, hxS⟩ := Finset.mem_erase.mp hx'
    rw [hoth x hxu hxv]
    exact hne x hxS
  · by_cases hxu : x = u
    · subst hxu; exact hfu
    · by_cases hxv : x = v
      · subst hxv; exact hfv
      · rw [hoth x hxu hxv]
        refine hout x (fun hxS => hx ?_)
        exact Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, hxS⟩⟩

/-- Reinstating the deleted pair. -/
theorem mul_swap_mem_of_erase (hτ : τ ∈ pairingsOn ((S.erase u).erase v))
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    τ * Equiv.swap u v ∈ pairingsOn S ∧ (τ * Equiv.swap u v) u = v := by
  obtain ⟨hinv, hne, hout⟩ := mem_pairingsOn.mp hτ
  have hfixu : τ u = u := hout u (fun h => absurd (Finset.mem_of_mem_erase h) (by simp))
  have hfixv : τ v = v := hout v (by simp)
  have happ : ∀ x, (τ * Equiv.swap u v) x = τ (Equiv.swap u v x) := fun _ => rfl
  have hu' : (τ * Equiv.swap u v) u = v := by rw [happ, Equiv.swap_apply_left, hfixv]
  have hv' : (τ * Equiv.swap u v) v = u := by rw [happ, Equiv.swap_apply_right, hfixu]
  have hoth : ∀ x, x ≠ u → x ≠ v → (τ * Equiv.swap u v) x = τ x := by
    intro x hxu hxv
    rw [happ, Equiv.swap_apply_of_ne_of_ne hxu hxv]
  have hstay : ∀ x, x ≠ u → x ≠ v → τ x ≠ u ∧ τ x ≠ v := by
    intro x hxu hxv
    refine ⟨fun h => hxu (by rw [← hfixu, ← h, hinv]), fun h => hxv (by rw [← hfixv, ← h, hinv])⟩
  refine ⟨mem_pairingsOn.mpr ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩, hu'⟩
  · by_cases hxu : x = u
    · subst hxu; rw [hu', hv']
    · by_cases hxv : x = v
      · subst hxv; rw [hv', hu']
      · obtain ⟨h1, h2⟩ := hstay x hxu hxv
        rw [hoth x hxu hxv, hoth _ h1 h2, hinv]
  · by_cases hxu : x = u
    · subst hxu; rw [hu']; exact fun h => huv h.symm
    · by_cases hxv : x = v
      · subst hxv; rw [hv']; exact huv
      · rw [hoth x hxu hxv]
        exact hne x (Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, hx⟩⟩)
  · have hxu : x ≠ u := fun h => hx (h ▸ hu)
    have hxv : x ≠ v := fun h => hx (h ▸ hv)
    rw [hoth x hxu hxv]
    exact hout x (fun h => hx (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)))

omit [Fintype V] in
@[simp] theorem mul_swap_apply_left : (τ * Equiv.swap u v) u = τ v := by
  show τ (Equiv.swap u v u) = τ v
  rw [Equiv.swap_apply_left]

omit [Fintype V] in
@[simp] theorem mul_swap_apply_right : (τ * Equiv.swap u v) v = τ u := by
  show τ (Equiv.swap u v v) = τ u
  rw [Equiv.swap_apply_right]

omit [Fintype V] in
theorem mul_swap_apply_other {x : V} (hxu : x ≠ u) (hxv : x ≠ v) :
    (τ * Equiv.swap u v) x = τ x := by
  show τ (Equiv.swap u v x) = τ x
  rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]

/-- The edges of a reinstated matching: the deleted pair together with the edges
of the smaller matching. -/
theorem image_mul_swap (hτ : τ ∈ pairingsOn ((S.erase u).erase v))
    (hu : u ∈ S) (hv : v ∈ S) :
    S.image (fun x => s(x, (τ * Equiv.swap u v) x))
      = insert s(u, v) (((S.erase u).erase v).image (fun x => s(x, τ x))) := by
  obtain ⟨-, -, hout⟩ := mem_pairingsOn.mp hτ
  have hfixu : τ u = u := hout u (fun h => absurd (Finset.mem_of_mem_erase h) (by simp))
  have hfixv : τ v = v := hout v (by simp)
  ext e
  simp only [Finset.mem_image, Finset.mem_insert]
  constructor
  · rintro ⟨x, hxS, rfl⟩
    by_cases hxu : x = u
    · subst hxu; exact Or.inl (by rw [mul_swap_apply_left, hfixv])
    · by_cases hxv : x = v
      · subst hxv
        refine Or.inl ?_
        rw [mul_swap_apply_right, hfixu]
        exact Sym2.eq_swap
      · exact Or.inr ⟨x, Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, hxS⟩⟩,
          by rw [mul_swap_apply_other hxu hxv]⟩
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · exact ⟨u, hu, by rw [mul_swap_apply_left, hfixv]⟩
    · obtain ⟨hxv, hx'⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxu, hxS⟩ := Finset.mem_erase.mp hx'
      exact ⟨x, hxS, by rw [mul_swap_apply_other hxu hxv]⟩

omit [Fintype V] in
/-- The deleted pair is not an edge of the smaller matching. -/
theorem notMem_image_erase :
    s(u, v) ∉ ((S.erase u).erase v).image (fun x => s(x, τ x)) := by
  intro h
  obtain ⟨x, hx, hex⟩ := Finset.mem_image.mp h
  obtain ⟨hxv, hx'⟩ := Finset.mem_erase.mp hx
  obtain ⟨hxu, -⟩ := Finset.mem_erase.mp hx'
  rw [Sym2.eq_iff] at hex
  rcases hex with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hxu rfl
  · exact hxv rfl

/-- The weight product of a reinstated matching factors off the deleted pair. -/
theorem prod_mul_swap (W : Sym2 (V × C) → R) (c : V → C)
    (hτ : τ ∈ pairingsOn ((S.erase u).erase v)) (hu : u ∈ S) (hv : v ∈ S) :
    (∏ e ∈ S.image (fun x => s(x, (τ * Equiv.swap u v) x)), W (Sym2.map (paint c) e))
      = W (Sym2.map (paint c) s(u, v))
          * ∏ e ∈ ((S.erase u).erase v).image (fun x => s(x, τ x)),
              W (Sym2.map (paint c) e) := by
  rw [image_mul_swap hτ hu hv, Finset.prod_insert notMem_image_erase]

/-- The matchings sending `u` to `v` are exactly the reinstatements. -/
theorem filter_eq_image_mul_swap (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    (pairingsOn S).filter (fun σ => σ u = v)
      = (pairingsOn ((S.erase u).erase v)).image (fun τ => τ * Equiv.swap u v) := by
  ext σ
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hσ, hσu⟩
    exact ⟨σ * Equiv.swap u v, mul_swap_mem_erase hσ hu hσu, by
      rw [mul_assoc, Equiv.swap_mul_self, mul_one]⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact mul_swap_mem_of_erase hτ hu hv huv

/-- **The deletion recursion.**  Every matching of `S` pairs `u` with some other
vertex; summing over that choice and deleting the pair expresses the matching sum
of `S` through the matching sums of two-vertex-smaller sets.

This is the recursion an induction on vertex count runs on, and it holds for every
vertex set and every subset. -/
theorem pmSum_expand (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V} {u : V}
    (hu : u ∈ S) :
    pmSum W c S
      = ∑ v ∈ S.erase u,
          W (Sym2.map (paint c) s(u, v)) * pmSum W c ((S.erase u).erase v) := by
  have hmaps : ∀ σ ∈ pairingsOn S, σ u ∈ S.erase u := by
    intro σ hσ
    obtain ⟨-, hne, -⟩ := mem_pairingsOn.mp hσ
    exact Finset.mem_erase.mpr ⟨hne u hu, pairingsOn_closed hσ u hu⟩
  rw [pmSum, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  obtain ⟨hvu, hvS⟩ := Finset.mem_erase.mp hv
  rw [filter_eq_image_mul_swap hu hvS (Ne.symm hvu),
    Finset.sum_image (fun _ _ _ _ h => mul_right_cancel h), pmSum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun τ hτ => prod_mul_swap W c hτ hu hvS)

/-- A nonzero matching sum has a partner whose incident weight and complementary
matching sum are both nonzero. -/
theorem exists_partner_ne_zero (W : Sym2 (V × C) → R) (c : V → C)
    {S : Finset V} {u : V} (hu : u ∈ S) (h : pmSum W c S ≠ 0) :
    ∃ v ∈ S.erase u, W (Sym2.map (paint c) s(u, v)) ≠ 0 ∧
      pmSum W c ((S.erase u).erase v) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  refine h ?_
  rw [pmSum_expand W c hu]
  refine Finset.sum_eq_zero fun v hv => ?_
  by_cases hw : W (Sym2.map (paint c) s(u, v)) = 0
  · rw [hw, zero_mul]
  · rw [hcon v hv hw, mul_zero]

/-- Two successive non-cancelling deletions, with the second pivot allowed to
depend on the first partner. -/
theorem exists_two_partners_ne_zero (W : Sym2 (V × C) → R) (c : V → C)
    {S : Finset V} {u : V} (hu : u ∈ S) (h : pmSum W c S ≠ 0)
    (p : V → V) :
    ∃ v ∈ S.erase u, W (Sym2.map (paint c) s(u, v)) ≠ 0 ∧
      (p v ∈ (S.erase u).erase v →
        ∃ q ∈ ((S.erase u).erase v).erase (p v),
          W (Sym2.map (paint c) s(p v, q)) ≠ 0 ∧
          pmSum W c ((((S.erase u).erase v).erase (p v)).erase q) ≠ 0) := by
  obtain ⟨v, hv, hw, hs⟩ := exists_partner_ne_zero W c hu h
  exact ⟨v, hv, hw, fun hp => exists_partner_ne_zero W c hp hs⟩

/-- A two-vertex matching sum is its single edge weight. -/
theorem pmSum_pair (W : Sym2 (V × C) → R) (c : V → C)
    {p q : V} (hqp : q ≠ p) :
    pmSum W c ({p, q} : Finset V) = W s((p, c p), (q, c q)) := by
  classical
  have hp : p ∈ ({p, q} : Finset V) := by simp
  have hpq : p ∉ ({q} : Finset V) := by simpa using (Ne.symm hqp)
  have herase : ({p, q} : Finset V).erase p = {q} := Finset.erase_insert hpq
  rw [pmSum_expand W c hp, herase, Finset.sum_singleton, Finset.erase_singleton,
    pmSum_empty, mul_one]
  rfl

/-- **The recursion determines the matching sum.**  A function on vertex subsets
that takes the value `1` on the empty set and satisfies the deletion recursion at
some vertex of every nonempty subset agrees with the matching sum everywhere.

This is what identifies an independently given definition of the sum — a list
recursion, say, or one produced by a different formalisation — with the matching
sum, without redoing any of the combinatorics.  Only one vertex per subset need
satisfy the recursion, so a definition that always deletes the first vertex of a
list qualifies. -/
theorem eq_pmSum_of_rec (W : Sym2 (V × C) → R) (c : V → C) (f : Finset V → R)
    (hemp : f ∅ = 1)
    (hrec : ∀ S : Finset V, S.Nonempty → ∃ u ∈ S,
        f S = ∑ v ∈ S.erase u,
          W (Sym2.map (paint c) s(u, v)) * f ((S.erase u).erase v)) :
    ∀ S : Finset V, f S = pmSum W c S := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [hemp, pmSum_empty]
    · obtain ⟨u, hu, hf⟩ := hrec S hS
      rw [hf, pmSum_expand W c hu]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have hsub : (S.erase u).erase v ⊂ S := by
        refine Finset.ssubset_iff_of_subset
          (fun y hy => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)) |>.mpr ⟨u, hu, ?_⟩
        intro hmem
        exact Finset.notMem_erase u S (Finset.mem_of_mem_erase hmem)
      rw [ih _ hsub]

/-! ### Locality and naturality

The matching sum over `S` sees only the edges inside `S`, and it commutes with
recolouring.  Neither fact needs the recursion — both are term-by-term — but
without them the sum could not be treated as an invariant of the induced
subgraph.
-/

/-- **Locality.**  The matching sum over `S` depends only on the weights of edges
with both endpoints in `S`.  Every edge of a matching of `S` is such an edge,
since a matching of `S` keeps `S` to itself. -/
theorem pmSum_congr (W W' : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    (h : ∀ x ∈ S, ∀ y ∈ S,
      W (Sym2.map (paint c) s(x, y)) = W' (Sym2.map (paint c) s(x, y))) :
    pmSum W c S = pmSum W' c S := by
  refine Finset.sum_congr rfl (fun σ hσ => Finset.prod_congr rfl (fun e he => ?_))
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  exact h x hx (σ x) (pairingsOn_closed hσ x hx)

/-- **Locality in the colouring.**  The matching sum over `S` depends only on the
colours of vertices in `S`. -/
theorem pmSum_congr_colour (W : Sym2 (V × C) → R) {c c' : V → C} {S : Finset V}
    (h : ∀ x ∈ S, c x = c' x) : pmSum W c S = pmSum W c' S := by
  refine Finset.sum_congr rfl (fun σ hσ => Finset.prod_congr rfl (fun e he => ?_))
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  have hσx : σ x ∈ S := pairingsOn_closed hσ x hx
  rw [show Sym2.map (paint c) s(x, σ x) = s((x, c x), (σ x, c (σ x))) from rfl,
    show Sym2.map (paint c') s(x, σ x) = s((x, c' x), (σ x, c' (σ x))) from rfl,
    h x hx, h _ hσx]

/-- **Naturality.**  Recolouring the weights and recolouring the colouring agree. -/
theorem pmSum_comp {C' : Type*} (f : C → C') (W : Sym2 (V × C') → R) (c : V → C)
    (S : Finset V) :
    pmSum (fun e => W (Sym2.map (Prod.map id f) e)) c S = pmSum W (f ∘ c) S :=
  Finset.sum_congr rfl (fun _ _ =>
    Finset.prod_congr rfl (fun e _ => congrArg W (map_paint f c e)))

/-- **An isolated vertex kills the matching sum.**  If a vertex of `S` has no
partner in `S` carrying a nonzero weight, nothing survives. -/
theorem pmSum_eq_zero_of_isolated (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    {u : V} (hu : u ∈ S) (h : ∀ v ∈ S.erase u, W (Sym2.map (paint c) s(u, v)) = 0) :
    pmSum W c S = 0 := by
  rw [pmSum_expand W c hu]
  exact Finset.sum_eq_zero (fun v hv => by rw [h v hv, zero_mul])

/-- **A forced edge factors out.**  If a vertex of `S` has just one partner
carrying a nonzero weight, that edge appears in every surviving matching. -/
theorem pmSum_of_forced (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V} {u v : V}
    (hu : u ∈ S) (hv : v ∈ S.erase u)
    (h : ∀ w ∈ S.erase u, w ≠ v → W (Sym2.map (paint c) s(u, w)) = 0) :
    pmSum W c S
      = W (Sym2.map (paint c) s(u, v)) * pmSum W c ((S.erase u).erase v) := by
  rw [pmSum_expand W c hu, Finset.sum_eq_single v]
  · intro w hw hne
    rw [h w hw hne, zero_mul]
  · intro hcon
    exact absurd hv hcon

/-- A chosen deletion term is the whole matching sum when every alternative
term vanishes, whether at its edge weight or in its complementary sum. -/
theorem pmSum_of_alternatives_zero (W : Sym2 (V × C) → R) (c : V → C)
    {S : Finset V} {u v : V} (hu : u ∈ S) (hv : v ∈ S.erase u)
    (h : ∀ w ∈ S.erase u, w ≠ v →
      W (Sym2.map (paint c) s(u, w)) * pmSum W c ((S.erase u).erase w) = 0) :
    pmSum W c S =
      W (Sym2.map (paint c) s(u, v)) * pmSum W c ((S.erase u).erase v) := by
  rw [pmSum_expand W c hu]
  exact Finset.sum_eq_single_of_mem v hv h

/-- A set whose internal edges all carry zero weight has vanishing matching sum,
unless it is empty. -/
theorem pmSum_eq_zero_of_forall_zero (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    (hS : S.Nonempty) (h : ∀ x ∈ S, ∀ y ∈ S, W (Sym2.map (paint c) s(x, y)) = 0) :
    pmSum W c S = 0 := by
  obtain ⟨u, hu⟩ := hS
  exact pmSum_eq_zero_of_isolated W c hu
    (fun v hv => h u hu v (Finset.mem_of_mem_erase hv))

/-! ### How many matchings a vertex set has

The deletion recursion counts as well as it sums.  Every matching of `S` pairs a
fixed vertex with one of the other `|S| - 1`, and deleting that pair leaves a
matching of a set two smaller — so the count satisfies the double-factorial
recursion, and an odd set has none at all.
-/

/-- The deletion recursion, counting. -/
theorem card_pairingsOn_expand {S : Finset V} {u : V} (hu : u ∈ S) :
    (pairingsOn S).card = ∑ v ∈ S.erase u, (pairingsOn ((S.erase u).erase v)).card := by
  have hmaps : ∀ σ ∈ pairingsOn S, σ u ∈ S.erase u := by
    intro σ hσ
    obtain ⟨-, hne, -⟩ := mem_pairingsOn.mp hσ
    exact Finset.mem_erase.mpr ⟨hne u hu, pairingsOn_closed hσ u hu⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  obtain ⟨hvu, hvS⟩ := Finset.mem_erase.mp hv
  rw [filter_eq_image_mul_swap hu hvS (Ne.symm hvu),
    Finset.card_image_of_injective _ (fun _ _ h => mul_right_cancel h)]

/-- **The number of perfect matchings of a vertex set**: the double factorial of
one less than its size.  Uniform in the vertex type. -/
theorem card_pairingsOn :
    ∀ S : Finset V, Even S.card → (pairingsOn S).card = Nat.doubleFactorial (S.card - 1) := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hS
    obtain ⟨k, hk⟩ := hS
    rcases S.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · rw [pairingsOn_empty]
      simp
    · have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨u, hu⟩
      have hge : 2 ≤ S.card := by omega
      rw [card_pairingsOn_expand hu]
      have hcard : ∀ v ∈ S.erase u, ((S.erase u).erase v).card = S.card - 2 := by
        intro v hv
        rw [Finset.card_erase_of_mem hv, Finset.card_erase_of_mem hu]
        omega
      have hstep : ∀ v ∈ S.erase u,
          (pairingsOn ((S.erase u).erase v)).card = Nat.doubleFactorial (S.card - 3) := by
        intro v hv
        have hsub : (S.erase u).erase v ⊂ S := by
          refine Finset.ssubset_iff_of_subset
            (fun y hy => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)) |>.mpr ⟨u, hu, ?_⟩
          intro hmem
          exact Finset.notMem_erase u S (Finset.mem_of_mem_erase hmem)
        have heven : Even ((S.erase u).erase v).card := by
          rw [hcard v hv]
          exact ⟨k - 1, by omega⟩
        have harith : S.card - 2 - 1 = S.card - 3 := by omega
        rw [ih _ hsub heven, hcard v hv, harith]
      rw [Finset.sum_congr rfl hstep, Finset.sum_const, Finset.card_erase_of_mem hu,
        smul_eq_mul]
      rcases Nat.eq_or_lt_of_le hge with h2 | h2
      · have h1 : S.card - 1 = 1 := by omega
        have h3 : S.card - 3 = 0 := by omega
        rw [h1, h3]
        simp
      · have hsplit : S.card - 1 = (S.card - 3) + 2 := by omega
        rw [hsplit, Nat.doubleFactorial_add_two]

/-! ### The vertex equations

Every structural restriction on a hypothetical solution has to come from somewhere
uniform in the vertex count.  This is the source: fix a vertex, expand the
amplitude along it, and the defining equations become a *linear* system whose
unknowns are the matching sums of the complements of that vertex's incident edges,
and whose coefficients are that vertex's own weights.

The system has one equation for each colour the vertex could wear — zero for the
colours that break monochromacy, one for the colour that preserves it — and its
size is the vertex's degree, not the vertex count.  That is what makes it usable
against an arbitrary counterexample.
-/

/-- **Expansion along a vertex.**  The amplitude is the sum, over the partners of a
fixed vertex, of that edge's weight times the matching sum of everything else. -/
theorem amplitude_eq_sum_pmSum (W : Sym2 (V × C) → R) (c : V → C) (u : V) :
    amplitude W c
      = ∑ v ∈ Finset.univ.erase u,
          W (Sym2.map (paint c) s(u, v)) * pmSum W c ((Finset.univ.erase u).erase v) := by
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u)]

/-- Recolouring a vertex does not change matching sums that avoid it. -/
theorem pmSum_update_of_notMem (W : Sym2 (V × C) → R) (c : V → C) (u : V) (j : C)
    {S : Finset V} (hu : u ∉ S) :
    pmSum W (Function.update c u j) S = pmSum W c S :=
  pmSum_congr_colour W (fun x hx => Function.update_of_ne (fun h => hu (by rw [← h]; exact hx)) _ _)

/-- Recolouring one vertex of a constant colouring exposes the incident edge
and leaves a constant matching sum on every complement. -/
theorem pmSum_single_vertex_recolour (W : Sym2 (V × C) → R) {S : Finset V}
    {w : V} (hw : w ∈ S) (k₀ k₁ : C) :
    pmSum W (Function.update (Amplitude.const (V := V) k₀) w k₁) S
      = ∑ z ∈ S.erase w, W s((w, k₁), (z, k₀))
          * pmSum W (Amplitude.const (V := V) k₀) ((S.erase w).erase z) := by
  rw [pmSum_expand W _ hw]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzw : z ≠ w := (Finset.mem_erase.mp hz).1
  have hc1 : Function.update (Amplitude.const (V := V) k₀) w k₁ w = k₁ := by simp
  have hc2 : Function.update (Amplitude.const (V := V) k₀) w k₁ z = k₀ := by
    rw [Function.update_of_ne hzw]
    rfl
  have hpaint :
      W (Sym2.map (paint (Function.update (Amplitude.const (V := V) k₀) w k₁)) s(w, z))
        = W s((w, k₁), (z, k₀)) := by
    rw [show Sym2.map (paint (Function.update (Amplitude.const (V := V) k₀) w k₁)) s(w, z)
      = s((w, Function.update (Amplitude.const (V := V) k₀) w k₁ w),
          (z, Function.update (Amplitude.const (V := V) k₀) w k₁ z)) from rfl, hc1, hc2]
  rw [hpaint]
  congr 1
  refine pmSum_congr_colour W fun x hx => ?_
  have hxw : x ≠ w := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
  rw [Function.update_of_ne hxw]

/-! ### Splitting a matching sum at a pair of vertices

Every matching either joins two chosen vertices to each other or sends them to two
distinct others.  Separating those cases splits the matching sum into a term
proportional to the sum over everything else, and a remainder in which the two
vertices reach into the rest.

This is the combinatorial content of contracting a pair of sites.  The first term is
the smaller system unchanged; the remainder is what a contraction adds, and it is a
first-order perturbation of that smaller system rather than another instance of it.
That asymmetry is the reason a contraction does not simply return an object of the
same kind, and it is what any reduction across two vertices must handle.
-/

/-- **Splitting at a pair.**  The term where the two chosen vertices are matched to
each other, plus everything else. -/
theorem pmSum_expand_pair (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V} {p q : V}
    (hp : p ∈ S) (hq : q ∈ S.erase p) :
    pmSum W c S
      = W (Sym2.map (paint c) s(p, q)) * pmSum W c ((S.erase p).erase q)
        + ∑ v ∈ (S.erase p).erase q,
            W (Sym2.map (paint c) s(p, v)) * pmSum W c ((S.erase p).erase v) := by
  rw [pmSum_expand W c hp, ← Finset.add_sum_erase _ _ hq]

/-- The remainder itself splits at the second vertex: expanding there turns it into a
sum over ordered pairs reaching out of the contracted pair. -/
theorem pmSum_pair_remainder (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    {p q : V} (hq : q ∈ S.erase p) (v : V) (hv : v ∈ (S.erase p).erase q) :
    pmSum W c ((S.erase p).erase v)
      = ∑ l ∈ ((S.erase p).erase v).erase q,
          W (Sym2.map (paint c) s(q, l)) *
            pmSum W c ((((S.erase p).erase v).erase q).erase l) := by
  exact pmSum_expand W c
    (Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hv).1 h.symm, hq⟩)

/-- **The matchings through one edge, with that edge removed, are the matchings of the
rest.**  Summing their weight products gives exactly the matching sum on the vertex set
with both endpoints deleted.

This identifies the cofactor that appears throughout the perturbation results: it is not
merely bounded by a smaller matching sum, it *is* one. -/
theorem pmSum_filter_edge (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V} {p q : V}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    (∑ σ ∈ (pairingsOn S).filter (fun σ => σ p = q),
      ∏ f ∈ (S.image (fun x => s(x, σ x))).erase s(p, q),
        W (Sym2.map (paint c) f))
      = pmSum W c ((S.erase p).erase q) := by
  classical
  rw [filter_eq_image_mul_swap hp hq hpq,
    Finset.sum_image (fun _ _ _ _ h => mul_right_cancel h), pmSum]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  rw [image_mul_swap hτ hp hq, Finset.erase_insert notMem_image_erase]

/-- Membership of an edge in a matching is the same as the matching sending one endpoint
to the other. -/
theorem mem_image_edge_iff {σ : Equiv.Perm V} (hσ : σ ∈ pairingsOn S) {p q : V}
    (hp : p ∈ S) :
    s(p, q) ∈ S.image (fun x => s(x, σ x)) ↔ σ p = q := by
  constructor
  · intro h
    obtain ⟨x, hx, hex⟩ := Finset.mem_image.mp h
    rw [Sym2.eq_iff] at hex
    rcases hex with ⟨rfl, hq⟩ | ⟨rfl, hq⟩
    · exact hq
    · obtain ⟨hinv, -, -⟩ := mem_pairingsOn.mp hσ
      rw [← hq, hinv]
  · intro h
    exact Finset.mem_image.mpr ⟨p, hp, by rw [h]⟩

/-- **The matchings through two disjoint edges, with both removed, are the matchings of
what is left.**  This identifies the double cofactor of the second-order expansion: it
is the matching sum over the four deleted sites' complement, exactly.

The two edges must be disjoint, which is what having matching number two means for the
defect support. -/
theorem pmSum_filter_two_edges (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    {p q r t : V} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    (hr : r ∈ (S.erase p).erase q) (ht : t ∈ (S.erase p).erase q) (hrt : r ≠ t) :
    (∑ σ ∈ (pairingsOn S).filter (fun σ => σ p = q ∧ σ r = t),
      ∏ f ∈ ((S.image (fun x => s(x, σ x))).erase s(p, q)).erase s(r, t),
        W (Sym2.map (paint c) f))
      = pmSum W c ((((S.erase p).erase q).erase r).erase t) := by
  classical
  have hrp : r ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)
  have hrq : r ≠ q := Finset.ne_of_mem_erase hr
  have hstep : (pairingsOn S).filter (fun σ => σ p = q ∧ σ r = t)
      = ((pairingsOn ((S.erase p).erase q)).filter (fun τ => τ r = t)).image
          (fun τ => τ * Equiv.swap p q) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hσ, h1, h2⟩
      have : σ ∈ (pairingsOn S).filter (fun σ => σ p = q) := Finset.mem_filter.mpr ⟨hσ, h1⟩
      rw [filter_eq_image_mul_swap hp hq hpq] at this
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp this
      refine ⟨τ, ⟨hτ, ?_⟩, rfl⟩
      rwa [mul_swap_apply_other hrp hrq] at h2
    · rintro ⟨τ, ⟨hτ, hτr⟩, rfl⟩
      have hmem : τ * Equiv.swap p q ∈ (pairingsOn S).filter (fun σ => σ p = q) := by
        rw [filter_eq_image_mul_swap hp hq hpq]
        exact Finset.mem_image.mpr ⟨τ, hτ, rfl⟩
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hmem
      exact ⟨h1, h2, by rwa [mul_swap_apply_other hrp hrq]⟩
  rw [hstep, Finset.sum_image (fun _ _ _ _ h => mul_right_cancel h)]
  rw [← pmSum_filter_edge W c hr ht hrt]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  obtain ⟨hτmem, -⟩ := Finset.mem_filter.mp hτ
  rw [image_mul_swap hτmem hp hq, Finset.erase_insert notMem_image_erase]

/-- **A live matching sum has a live edge at every site.**  If the sum does not vanish
then, at any chosen site, some edge from it carries nonzero weight and leaves a
nonvanishing sum behind.

Immediate from the expansion — a sum of products cannot be nonzero with every product
zero — and used wherever a nonvanishing sum has to be propagated to a smaller one. -/
theorem exists_edge_of_pmSum_ne_zero (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    {u : V} (hu : u ∈ S) (h : pmSum W c S ≠ 0) :
    ∃ v ∈ S.erase u, W (Sym2.map (paint c) s(u, v)) ≠ 0 ∧
      pmSum W c ((S.erase u).erase v) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  refine h ?_
  rw [pmSum_expand W c hu]
  refine Finset.sum_eq_zero fun v hv => ?_
  rcases eq_or_ne (W (Sym2.map (paint c) s(u, v))) 0 with h1 | h1
  · rw [h1, zero_mul]
  · rw [hcon v hv h1, mul_zero]

/-- **The two-site splitting.**  A matching sum splits, at any two of its sites, into
the term where those sites are matched to each other and a double sum over the ways of
sending them to distinct other partners.

Read with the colours at the two sites left free and every other colour fixed, this is
the decomposition that governs the block those sites carry: the first term is that
block scaled by the matching sum on everything else, and each summand of the double sum
is a product of something depending only on the first free colour with something
depending only on the second.  So the whole correction is built from rank-one pieces,
one for each admissible pair of partners. -/
theorem pmSum_split_two (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    {p q : V} (hp : p ∈ S) (hq : q ∈ S.erase p) :
    pmSum W c S
      = W (Sym2.map (paint c) s(p, q)) * pmSum W c ((S.erase p).erase q)
        + ∑ v ∈ (S.erase p).erase q,
            W (Sym2.map (paint c) s(p, v)) *
              ∑ l ∈ ((S.erase p).erase v).erase q,
                W (Sym2.map (paint c) s(q, l)) *
                  pmSum W c ((((S.erase p).erase v).erase q).erase l) := by
  rw [pmSum_expand_pair W c hp hq]
  congr 1
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [pmSum_pair_remainder W c hq v hv]

/-! ### A perturbation supported on one factor

If a perturbation is nonzero on at most one factor of a product, the perturbed
product is exactly linear in the parameter: there is no second-order term because
there is no second factor to supply one.

Combined with the fact that a matching uses at most one edge of a set with matching
number one, this is why perturbing a matching sum along such a set gives an exact
first-order identity rather than a series.  It is the algebraic half of absorbing a
first-order defect back into a flat object.
-/

/-- A perturbation vanishing on every factor leaves the product alone. -/
theorem prod_add_of_support_empty {α : Type*} {E : Finset α} (W A : α → R) (t : R)
    (h : ∀ e ∈ E, A e = 0) :
    (∏ e ∈ E, (W e + t * A e)) = ∏ e ∈ E, W e :=
  Finset.prod_congr rfl (fun e he => by rw [h e he, mul_zero, add_zero])

/-! ### Restricting to a subset of the sites

A matching sum over a subset is the matching sum of the system that subset carries, read
on the subtype.  Establishing this needs no correspondence between matchings: the two
sides satisfy the same deletion recursion and agree on the empty set, and the recursion
principle already proved does the rest.
-/

/-- The weights a subset of the sites carries, read on the subtype. -/
def restrictW (W : Sym2 (V × C) → R) (S : Finset V) : Sym2 (↥(S : Finset V) × C) → R :=
  fun e => W (Sym2.map (fun q => ((q.1 : V), q.2)) e)

/-- **A matching sum over a subset is a matching sum on the subtype.**  Both satisfy the
deletion recursion at any site and agree on the empty set. -/
theorem pmSum_restrict_map (W : Sym2 (V × C) → R) (S : Finset V) (c : V → C)
    (T : Finset ↥S) :
    pmSum W c (T.map (Function.Embedding.subtype _))
      = pmSum (restrictW W S) (fun u : ↥S => c (u : V)) T := by
  classical
  have hmap : ∀ (T' : Finset ↥S) (a : ↥S),
      (T'.map (Function.Embedding.subtype (· ∈ S))).erase (a : V)
        = (T'.erase a).map (Function.Embedding.subtype (· ∈ S)) :=
    fun T' a => (Finset.map_erase (Function.Embedding.subtype (· ∈ S)) T' a).symm
  refine eq_pmSum_of_rec (restrictW W S) (fun u : ↥S => c (u : V))
    (fun T => pmSum W c (T.map (Function.Embedding.subtype _))) ?_ ?_ T
  · simp [pmSum_empty]
  · intro T' hT'
    obtain ⟨u, hu⟩ := hT'
    refine ⟨u, hu, ?_⟩
    have hmem : (u : V) ∈ T'.map (Function.Embedding.subtype (· ∈ S)) :=
      Finset.mem_map_of_mem _ hu
    rw [pmSum_expand W c hmem, hmap T' u, Finset.sum_map]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Function.Embedding.coe_subtype]
    rw [hmap (T'.erase u) v]
    rfl

/-- **The restricted system's amplitude is the matching sum over the subset.**  Reading
the weights on the subtype and taking the amplitude there returns exactly what the
original system contributes over that subset. -/
theorem amplitude_restrictSites (W : Sym2 (V × C) → R) (S : Finset V) (c : V → C) :
    amplitude (restrictW W S) (fun u : ↥S => c (u : V)) = pmSum W c S := by
  classical
  rw [← pmSum_univ, ← pmSum_restrict_map W S c]
  congr 1
  ext v
  simp

/-! ### Relabelling the sites

Renaming the sites along a bijection carries a matching sum to a matching sum.  As with
restriction, no correspondence between matchings need be built: the recursion principle
identifies the two sides.
-/

/-- The weights read through a renaming of the sites. -/
def relabelW {V' : Type*} (W : Sym2 (V × C) → R) (e : V' ≃ V) : Sym2 (V' × C) → R :=
  fun z => W (Sym2.map (fun q => (e q.1, q.2)) z)

/-- **Renaming the sites carries a matching sum to a matching sum.** -/
theorem pmSum_relabel {V' : Type*} [Fintype V'] [DecidableEq V']
    (W : Sym2 (V × C) → R) (e : V' ≃ V) (c : V → C) (T : Finset V') :
    pmSum W c (T.map e.toEmbedding)
      = pmSum (relabelW W e) (fun u : V' => c (e u)) T := by
  classical
  have hmap : ∀ (T' : Finset V') (a : V'),
      (T'.map e.toEmbedding).erase (e a) = (T'.erase a).map e.toEmbedding :=
    fun T' a => (Finset.map_erase e.toEmbedding T' a).symm
  refine eq_pmSum_of_rec (relabelW W e) (fun u : V' => c (e u))
    (fun T => pmSum W c (T.map e.toEmbedding)) ?_ ?_ T
  · simp [pmSum_empty]
  · intro T' hT'
    obtain ⟨u, hu⟩ := hT'
    refine ⟨u, hu, ?_⟩
    have hmem : e u ∈ T'.map e.toEmbedding := Finset.mem_map_of_mem _ hu
    rw [pmSum_expand W c hmem, hmap T' u, Finset.sum_map]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Equiv.coe_toEmbedding]
    rw [hmap (T'.erase u) v]
    rfl

/-- **Renaming preserves the amplitude.** -/
theorem amplitude_relabel {V' : Type*} [Fintype V'] [DecidableEq V']
    (W : Sym2 (V × C) → R) (e : V' ≃ V) (c : V → C) :
    amplitude (relabelW W e) (fun u : V' => c (e u)) = amplitude W c := by
  classical
  rw [← pmSum_univ, ← pmSum_relabel W e c,
    show (Finset.univ : Finset V').map e.toEmbedding = Finset.univ from by ext v; simp]
  exact pmSum_univ W c

/-! ### Expansions bounded by the defect support

The empty, linear and quadratic expansions below are the first three cases of one
statement: a perturbation carried by a set `F` expands over the subsets of `F` that the
product actually meets, with the parameter's exponent counting them. Since a matching
meets a defect support in at most its matching number of edges, the expansion has that
degree and no more.
-/

/-- **The general expansion.**  A perturbation expands over the subsets of the factors
it touches, the parameter counting how many are taken. -/
theorem prod_add_expand {α : Type*} [DecidableEq α] (E : Finset α) (W A : α → R) (t : R) :
    (∏ e ∈ E, (W e + t * A e))
      = ∑ T ∈ E.powerset, (∏ e ∈ T, W e) * (t ^ (E \ T).card * ∏ e ∈ E \ T, A e) := by
  classical
  rw [Finset.prod_add W (fun e => t * A e) E]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- **The expansion truncates at the defect support.**  Only the factors where the
perturbation is nonzero contribute, so the terms are indexed by the subsets of the
product's intersection with that support.

A matching meets a defect support in at most its matching number of edges, so this is
where a bound on the matching number becomes a bound on the degree. -/
theorem prod_add_expand_supported {α : Type*} [DecidableEq α] (E F : Finset α)
    (W A : α → R) (t : R) (hA : ∀ e ∈ E, e ∉ F → A e = 0) :
    (∏ e ∈ E, (W e + t * A e))
      = ∑ T ∈ E.powerset.filter (fun T => E \ T ⊆ F),
          (∏ e ∈ T, W e) * (t ^ (E \ T).card * ∏ e ∈ E \ T, A e) := by
  classical
  rw [prod_add_expand E W A t]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro T hT hnT
  have : ¬ (E \ T ⊆ F) := by
    intro hsub
    exact hnT (Finset.mem_filter.mpr ⟨hT, hsub⟩)
  obtain ⟨e, heT, heF⟩ := Finset.not_subset.mp this
  have hzero : A e = 0 := hA e (Finset.mem_sdiff.mp heT).1 heF
  rw [Finset.prod_eq_zero heT hzero, mul_zero, mul_zero]

/-- **A perturbation on one factor is exactly linear.**  No second-order term
appears, because no second factor carries the perturbation. -/
theorem prod_add_of_support_le_one {α : Type*} [DecidableEq α] {E : Finset α}
    (W A : α → R) (t : R) {e₀ : α} (he₀ : e₀ ∈ E)
    (h : ∀ e ∈ E, e ≠ e₀ → A e = 0) :
    (∏ e ∈ E, (W e + t * A e))
      = (∏ e ∈ E, W e) + t * A e₀ * ∏ e ∈ E.erase e₀, W e := by
  rw [← Finset.mul_prod_erase E _ he₀, ← Finset.mul_prod_erase E W he₀,
    prod_add_of_support_empty W A t (fun e he => h e (Finset.mem_of_mem_erase he)
      (Finset.ne_of_mem_erase he))]
  ring

/-- **A perturbation on two factors is exactly quadratic.**  The expansion stops at
second order because no third factor carries the perturbation.

This is the second-order companion of the linear case, and it is what a defect
support of matching number two requires: such a support meets a matching in at most
two edges, so the perturbed product is a quadratic in the parameter — finite and
explicit, not a series. -/
theorem prod_add_of_support_le_two {α : Type*} [DecidableEq α] {E : Finset α}
    (W A : α → R) (t : R) {e₀ e₁ : α} (he₀ : e₀ ∈ E) (he₁ : e₁ ∈ E) (hne : e₀ ≠ e₁)
    (h : ∀ e ∈ E, e ≠ e₀ → e ≠ e₁ → A e = 0) :
    (∏ e ∈ E, (W e + t * A e))
      = (∏ e ∈ E, W e)
        + t * (A e₀ * ∏ e ∈ E.erase e₀, W e + A e₁ * ∏ e ∈ E.erase e₁, W e)
        + t ^ 2 * (A e₀ * A e₁ * ∏ e ∈ (E.erase e₀).erase e₁, W e) := by
  have he₁' : e₁ ∈ E.erase e₀ := Finset.mem_erase.2 ⟨hne.symm, he₁⟩
  have he₀' : e₀ ∈ E.erase e₁ := Finset.mem_erase.2 ⟨hne, he₀⟩
  have hzero : ∀ e ∈ (E.erase e₀).erase e₁, A e = 0 := fun e he =>
    h e (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he))
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase he))
      (Finset.ne_of_mem_erase he)
  have h1 : ∏ e ∈ E.erase e₀, W e = W e₁ * ∏ e ∈ (E.erase e₀).erase e₁, W e :=
    (Finset.mul_prod_erase _ W he₁').symm
  have h2 : ∏ e ∈ E.erase e₁, W e = W e₀ * ∏ e ∈ (E.erase e₀).erase e₁, W e := by
    rw [← Finset.mul_prod_erase _ W he₀', Finset.erase_right_comm]
  have h3 : ∏ e ∈ E, W e = W e₀ * (W e₁ * ∏ e ∈ (E.erase e₀).erase e₁, W e) := by
    rw [← Finset.mul_prod_erase E W he₀, ← Finset.mul_prod_erase _ W he₁']
  have h4 : ∏ e ∈ E, (W e + t * A e)
      = (W e₀ + t * A e₀) *
          ((W e₁ + t * A e₁) * ∏ e ∈ (E.erase e₀).erase e₁, W e) := by
    rw [← Finset.mul_prod_erase E _ he₀, ← Finset.mul_prod_erase _ _ he₁',
      prod_add_of_support_empty W A t hzero]
  rw [h1, h2, h3, h4]
  ring

/-! ### Matching number one, and why an expansion truncates

A set of edges has *matching number at most one* when no two of its members are
vertex-disjoint — a star or a triangle, and nothing else on a simple graph.

The classification is not needed here.  The truncation below is proved from pairwise
intersection directly, so it covers the triangle as readily as the star, and the
shape of the support never enters.

The consequence below is the load-bearing combinatorial fact behind reductions that
absorb a first-order defect.  Perturbing the weights along such a set,
`W + t·A`, the matching sum is *exactly* linear in `t`: no perfect matching can use
two edges of the set, so every term of order two or higher is empty.  A contraction
of two sites produces a flat tensor plus a tangent vector, and this is the condition
under which the tangent vector can be absorbed back into a flat one.
-/

omit [Fintype V] [DecidableEq V] in
/-- Distinct edges of a matching share no vertex. -/
theorem edges_disjoint_of_ne {σ : Equiv.Perm V} (hinv : ∀ x, σ (σ x) = x)
    {x y : V} (hne : s(x, σ x) ≠ s(y, σ y)) :
    x ≠ y ∧ x ≠ σ y ∧ σ x ≠ y ∧ σ x ≠ σ y := by
  refine ⟨fun h => hne (by rw [h]), fun h => hne ?_, fun h => hne ?_, fun h => hne ?_⟩
  · rw [h, hinv]
    exact Sym2.eq_swap
  · rw [← h, hinv]
    exact Sym2.eq_swap
  · have hxy : x = y := by rw [← hinv x, h, hinv]
    rw [hxy]

/-- **A matching uses at most one edge of a set with matching number one.**  If no
two members of `A` are vertex-disjoint, no perfect matching contains two of them. -/
theorem card_inter_le_one_of_pairwise_meeting
    {σ : Equiv.Perm V} (hσ : σ ∈ pairings V) (A : Finset (Sym2 V))
    (hA : ∀ e ∈ A, ∀ f ∈ A, e ≠ f →
      ∃ z : V, z ∈ e ∧ z ∈ f) :
    ((edges σ) ∩ A).card ≤ 1 := by
  classical
  obtain ⟨hinv, -⟩ := (Finset.mem_filter.mp hσ).2
  by_contra hcon
  push Not at hcon
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp hcon
  obtain ⟨heσ, heA⟩ := Finset.mem_inter.mp he
  obtain ⟨hfσ, hfA⟩ := Finset.mem_inter.mp hf
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp heσ
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hfσ
  obtain ⟨z, hze, hzf⟩ := hA _ heA _ hfA hef
  obtain ⟨hxy, hxσy, hσxy, hσxσy⟩ := edges_disjoint_of_ne hinv hef
  rw [Sym2.mem_iff] at hze hzf
  rcases hze with rfl | rfl <;> rcases hzf with h | h
  · exact hxy h
  · exact hxσy h
  · exact hσxy h
  · exact hσxσy h

/-! ### Perturbing along a single edge

The simplest defect with matching number one is supported on one edge.  Perturbing
the weights there changes the matching sum by exactly one term: the perturbation
times the matching sum of everything the edge does not touch.  No higher order
appears, because no matching can use that edge twice.

This is the reduction's absorption step in its smallest instance, and it is exact
rather than approximate.
-/

/-- The matchings using a given edge contribute the smaller matching sum. -/
theorem sum_over_using_edge (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    {p q : V} (hp : p ∈ S) (hq : q ∈ S.erase p) :
    (∑ σ ∈ (pairingsOn S).filter (fun σ => σ p = q),
        ∏ e ∈ ((S.erase p).erase q).image (fun x => s(x, σ x)),
          W (Sym2.map (paint c) e))
      = pmSum W c ((S.erase p).erase q) := by
  classical
  obtain ⟨hqp, hqS⟩ := Finset.mem_erase.mp hq
  rw [filter_eq_image_mul_swap hp hqS (Ne.symm hqp),
    Finset.sum_image (fun _ _ _ _ h => mul_right_cancel h), pmSum]
  refine Finset.sum_congr rfl (fun τ hτ => ?_)
  refine Finset.prod_congr (Finset.image_congr (fun x hx => ?_)) (fun _ _ => rfl)
  obtain ⟨hxq, hx'⟩ := Finset.mem_erase.mp hx
  obtain ⟨hxp, -⟩ := Finset.mem_erase.mp hx'
  rw [mul_swap_apply_other hxp hxq]

omit [Fintype V] in
/-- A matching not joining two vertices does not carry the edge between them. -/
theorem notMem_image_of_ne {σ : Equiv.Perm V} (hinv : ∀ x, σ (σ x) = x) {S : Finset V}
    {p q : V} (hpq : σ p ≠ q) :
    s(p, q) ∉ S.image (fun x => s(x, σ x)) := by
  intro h
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp h
  rw [Sym2.eq_iff] at hx
  rcases hx with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · exact hpq h2
  · exact hpq (by rw [← h2, hinv])

omit [Fintype V] in
/-- A matching joining two vertices carries their edge, and deleting it leaves the
edges of everything else. -/
theorem image_erase_of_eq {σ : Equiv.Perm V} (hinv : ∀ x, σ (σ x) = x) {S : Finset V}
    {p q : V} (hpq : σ p = q) :
    (S.image (fun x => s(x, σ x))).erase s(p, q)
      = ((S.erase p).erase q).image (fun x => s(x, σ x)) := by
  have hqp : σ q = p := by rw [← hpq, hinv]
  ext e
  constructor
  · intro he
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp he
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hmem
    refine Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨?_,
      Finset.mem_erase.mpr ⟨?_, hxS⟩⟩, rfl⟩
    · rintro rfl
      exact hne (by rw [hqp]; exact Sym2.eq_swap)
    · rintro rfl
      exact hne (by rw [hpq])
  · intro he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hxq, hx'⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxp, hxS⟩ := Finset.mem_erase.mp hx'
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hxp rfl
    · exact hxq rfl

/-- **Perturbing along a single edge.**  Changing the weights on one edge changes the
matching sum by exactly one term: the change times the matching sum of everything
that edge does not touch.  Exact, with no higher order, because no matching uses the
edge twice. -/
theorem pmSum_perturb_single_edge (W A : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    {p q : V} (hp : p ∈ S) (hq : q ∈ S.erase p) (t : R)
    (hA : ∀ x y : V, s(x, y) ≠ s(p, q) → A (Sym2.map (paint c) s(x, y)) = 0) :
    pmSum (fun e => W e + t * A e) c S
      = pmSum W c S
        + t * A (Sym2.map (paint c) s(p, q)) * pmSum W c ((S.erase p).erase q) := by
  classical
  have hterm : ∀ σ ∈ pairingsOn S,
      (∏ e ∈ S.image (fun x => s(x, σ x)),
          (W (Sym2.map (paint c) e) + t * A (Sym2.map (paint c) e)))
        = (∏ e ∈ S.image (fun x => s(x, σ x)), W (Sym2.map (paint c) e))
          + (if σ p = q then
              t * A (Sym2.map (paint c) s(p, q)) *
                ∏ e ∈ ((S.erase p).erase q).image (fun x => s(x, σ x)),
                  W (Sym2.map (paint c) e)
            else 0) := by
    intro σ hσ
    obtain ⟨hinv, -, -⟩ := mem_pairingsOn.mp hσ
    by_cases h : σ p = q
    · rw [if_pos h]
      have hmem : s(p, q) ∈ S.image (fun x => s(x, σ x)) :=
        Finset.mem_image.mpr ⟨p, hp, by rw [h]⟩
      rw [prod_add_of_support_le_one
        (fun e => W (Sym2.map (paint c) e)) (fun e => A (Sym2.map (paint c) e)) t hmem
        (fun e he hne => by
          obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
          exact hA x (σ x) hne),
        image_erase_of_eq hinv h]
    · rw [if_neg h, add_zero]
      refine prod_add_of_support_empty _ _ t (fun e he => ?_)
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
      exact hA _ _ (fun hh => notMem_image_of_ne hinv h (hh ▸ he))
  rw [pmSum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← pmSum,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.mul_sum,
    sum_over_using_edge W c hp hq]

/-- A perturbation confined to the edges at one vertex is invisible to any vertex set
avoiding that vertex. -/
theorem pmSum_perturb_of_avoiding (W A : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    {u : V} (t : R) (hu : u ∉ S)
    (hA : ∀ x y : V, x ≠ u → y ≠ u → A (Sym2.map (paint c) s(x, y)) = 0) :
    pmSum (fun e => W e + t * A e) c S = pmSum W c S := by
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  refine prod_add_of_support_empty _ _ t (fun e he => ?_)
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  exact hA x (σ x) (fun h => hu (h ▸ hx)) (fun h => hu (h ▸ pairingsOn_closed hσ x hx))

/-- **Perturbing along a star.**  A perturbation confined to the edges at one vertex
changes the matching sum by exactly its first-order term — one contribution per
partner of that vertex, and nothing further.

A star is the main shape a defect of matching number one can take: no two of its
edges are disjoint, since they all meet at the centre.  The proof needs nothing new,
only that the perturbation is invisible once its centre is deleted, so expanding at
that centre separates it completely.

What a general support still lacks is not the truncation — that holds for any
pairwise-intersecting family — but the reorganisation of the resulting sum into one
term per defect edge, which here uses the centre. -/
theorem pmSum_perturb_star (W A : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    {u : V} (hu : u ∈ S) (t : R)
    (hA : ∀ x y : V, x ≠ u → y ≠ u → A (Sym2.map (paint c) s(x, y)) = 0) :
    pmSum (fun e => W e + t * A e) c S
      = pmSum W c S
        + t * ∑ v ∈ S.erase u,
            A (Sym2.map (paint c) s(u, v)) * pmSum W c ((S.erase u).erase v) := by
  rw [pmSum_expand (fun e => W e + t * A e) c hu, pmSum_expand W c hu,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [pmSum_perturb_of_avoiding W A c t
    (fun h => Finset.notMem_erase u S (Finset.mem_of_mem_erase h)) hA]
  ring

/-- **Each matching belongs to at most one defect class.**  Classifying matchings by
which edge of a pairwise-intersecting family they use gives disjoint classes, since
no matching can carry two such edges.

This is what a general reorganisation of the perturbed sum needs: first-order
contributions can be gathered edge by edge without double counting.  For a star the
centre supplies this directly; in general it comes from the bound on how many defect
edges a matching carries. -/
theorem disjoint_using_edge {S : Finset V} {σ : Equiv.Perm V} (hσ : σ ∈ pairingsOn S)
    {e f : Sym2 V} (hmeet : ∃ z : V, z ∈ e ∧ z ∈ f) (hef : e ≠ f)
    (he : e ∈ S.image (fun x => s(x, σ x)))
    (hf : f ∈ S.image (fun x => s(x, σ x))) : False := by
  obtain ⟨hinv, -, -⟩ := mem_pairingsOn.mp hσ
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨z, hze, hzf⟩ := hmeet
  obtain ⟨hxy, hxσy, hσxy, hσxσy⟩ := edges_disjoint_of_ne hinv hef
  rw [Sym2.mem_iff] at hze hzf
  rcases hze with rfl | rfl <;> rcases hzf with h | h
  · exact hxy h
  · exact hxσy h
  · exact hσxy h
  · exact hσxσy h

/-- **The perturbed product, edge by edge.**  For a defect supported on a
pairwise-intersecting family, one matching's perturbed edge product is its flat
product plus a single sum over the family — at most one of whose terms is ever
nonzero, since the matching carries at most one defect edge. -/
theorem prod_add_eq_sum_over_family (W A : Sym2 (V × C) → R) (c : V → C) (t : R)
    {S : Finset V} {σ : Equiv.Perm V} (hσ : σ ∈ pairingsOn S) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∃ z : V, z ∈ e ∧ z ∈ f)
    (hA : ∀ e : Sym2 V, e ∉ E → A (Sym2.map (paint c) e) = 0) :
    (∏ e ∈ S.image (fun x => s(x, σ x)),
        (W (Sym2.map (paint c) e) + t * A (Sym2.map (paint c) e)))
      = (∏ e ∈ S.image (fun x => s(x, σ x)), W (Sym2.map (paint c) e))
        + t * ∑ e ∈ E,
            (if e ∈ S.image (fun x => s(x, σ x)) then
              A (Sym2.map (paint c) e) *
                ∏ f ∈ (S.image (fun x => s(x, σ x))).erase e, W (Sym2.map (paint c) f)
             else 0) := by
  classical
  by_cases hex : ∃ e₀ ∈ E, e₀ ∈ S.image (fun x => s(x, σ x))
  · obtain ⟨e₀, he₀E, he₀σ⟩ := hex
    have hsingle : ∀ e ∈ E, e ≠ e₀ → e ∉ S.image (fun x => s(x, σ x)) := by
      intro e heE hne hmem
      exact disjoint_using_edge hσ (hE e heE e₀ he₀E hne) hne hmem he₀σ
    rw [prod_add_of_support_le_one
      (fun e => W (Sym2.map (paint c) e)) (fun e => A (Sym2.map (paint c) e)) t he₀σ
      (fun e he hne => by
        by_cases hEmem : e ∈ E
        · exact absurd he (hsingle e hEmem hne)
        · exact hA e hEmem),
      Finset.sum_eq_single e₀ (fun e heE hne => if_neg (hsingle e heE hne))
        (fun h => absurd he₀E h), if_pos he₀σ]
    ring
  · push Not at hex
    rw [prod_add_of_support_empty _ _ t (fun e he => by
        by_cases hEmem : e ∈ E
        · exact absurd he (hex e hEmem)
        · exact hA e hEmem),
      Finset.sum_eq_zero (fun e heE => if_neg (hex e heE)), mul_zero, add_zero]

/-- **Perturbing along any defect of matching number one.**  The matching sum changes
by exactly its first-order term, gathered edge by edge over the defect family.

Every shape the condition permits is covered — star, triangle, or any
pairwise-intersecting family — and the identity is exact, with no higher order,
because no matching carries two defect edges.  This is the general form of the
absorption on which a contraction-based reduction rests. -/
theorem pmSum_perturb_family (W A : Sym2 (V × C) → R) (c : V → C) (t : R)
    {S : Finset V} (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∃ z : V, z ∈ e ∧ z ∈ f)
    (hA : ∀ e : Sym2 V, e ∉ E → A (Sym2.map (paint c) e) = 0) :
    pmSum (fun e => W e + t * A e) c S
      = pmSum W c S
        + t * ∑ e ∈ E, A (Sym2.map (paint c) e) *
            ∑ σ ∈ (pairingsOn S).filter (fun σ => e ∈ S.image (fun x => s(x, σ x))),
              ∏ f ∈ (S.image (fun x => s(x, σ x))).erase e, W (Sym2.map (paint c) f) := by
  classical
  have hstep : ∀ e ∈ E,
      (∑ σ ∈ pairingsOn S,
        (if e ∈ S.image (fun x => s(x, σ x)) then
          A (Sym2.map (paint c) e) *
            ∏ f ∈ (S.image (fun x => s(x, σ x))).erase e, W (Sym2.map (paint c) f)
         else 0))
        = A (Sym2.map (paint c) e) *
            ∑ σ ∈ (pairingsOn S).filter (fun σ => e ∈ S.image (fun x => s(x, σ x))),
              ∏ f ∈ (S.image (fun x => s(x, σ x))).erase e, W (Sym2.map (paint c) f) := by
    intro e _
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    by_cases h : e ∈ S.image (fun x => s(x, σ x))
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [pmSum,
    Finset.sum_congr rfl (fun σ hσ => prod_add_eq_sum_over_family W A c t hσ E hE hA),
    Finset.sum_add_distrib, ← pmSum, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl hstep]

/-- **The perturbed matching sum terminates at second order.**  When the defect is
carried by two edges, the matching sum is an exact quadratic in the parameter: a flat
term, a first-order term, and a second-order term, with nothing beyond.

This is what a defect support of matching number two forces.  The first-order theory
represents its correction as a tangent vector, and a tangent vector cannot carry the
cross term produced when a single matching uses both defect edges.  The statement
below is the honest replacement: the correction is quadratic, and — because no
matching can use a third defect edge — the expansion stops there rather than running
away into a series. -/
theorem pmSum_perturb_two (W A : Sym2 (V × C) → R) (c : V → C)
    {S : Finset V} {e₀ e₁ : Sym2 V} (hne : e₀ ≠ e₁)
    (hA : ∀ e : Sym2 V, e ≠ e₀ → e ≠ e₁ → A (Sym2.map (paint c) e) = 0) :
    ∃ L Q : R, ∀ t : R,
      pmSum (fun e => W e + t * A e) c S
        = pmSum W c S + t * L + t ^ 2 * Q := by
  classical
  refine ⟨∑ σ ∈ pairingsOn S,
      ((if e₀ ∈ S.image (fun x => s(x, σ x)) then
          A (Sym2.map (paint c) e₀) *
            ∏ e ∈ (S.image (fun x => s(x, σ x))).erase e₀, W (Sym2.map (paint c) e)
        else 0)
      + (if e₁ ∈ S.image (fun x => s(x, σ x)) then
          A (Sym2.map (paint c) e₁) *
            ∏ e ∈ (S.image (fun x => s(x, σ x))).erase e₁, W (Sym2.map (paint c) e)
        else 0)),
    ∑ σ ∈ pairingsOn S,
      (if e₀ ∈ S.image (fun x => s(x, σ x)) ∧ e₁ ∈ S.image (fun x => s(x, σ x)) then
          A (Sym2.map (paint c) e₀) * A (Sym2.map (paint c) e₁) *
            ∏ e ∈ ((S.image (fun x => s(x, σ x))).erase e₀).erase e₁,
              W (Sym2.map (paint c) e)
        else 0), ?_⟩
  intro t
  unfold pmSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h0 : e₀ ∈ S.image (fun x => s(x, σ x)) <;>
    by_cases h1 : e₁ ∈ S.image (fun x => s(x, σ x))
  · rw [prod_add_of_support_le_two (fun e => W (Sym2.map (paint c) e))
        (fun e => A (Sym2.map (paint c) e)) t h0 h1 hne
        (fun e _ hx hy => hA e hx hy), if_pos h0, if_pos h1, if_pos ⟨h0, h1⟩]
  · rw [prod_add_of_support_le_one (fun e => W (Sym2.map (paint c) e))
        (fun e => A (Sym2.map (paint c) e)) t h0
        (fun e he hx => hA e hx (fun hy => h1 (hy ▸ he))), if_pos h0, if_neg h1,
      if_neg (fun hc => h1 hc.2)]
    ring
  · rw [prod_add_of_support_le_one (fun e => W (Sym2.map (paint c) e))
        (fun e => A (Sym2.map (paint c) e)) t h1
        (fun e he hx => hA e (fun hy => h0 (hy ▸ he)) hx), if_neg h0, if_pos h1,
      if_neg (fun hc => h0 hc.1)]
    ring
  · rw [prod_add_of_support_empty (fun e => W (Sym2.map (paint c) e))
        (fun e => A (Sym2.map (paint c) e)) t
        (fun e he => hA e (fun hy => h0 (hy ▸ he)) (fun hy => h1 (hy ▸ he))),
      if_neg h0, if_neg h1, if_neg (fun hc => h0 hc.1)]
    ring

/-- **The second-order coefficient factors through the defect values.**  It is the
product of the defect at the two edges with a *double cofactor* depending only on the
weights: the matching sum restricted to those matchings that use both defect edges,
with the two edges removed.

The consequence is the sharp one.  The coefficient vanishes exactly when the defect
dies at one of its two edges — in which case the defect was carried by a single edge
and the theory was first-order all along — or when the double cofactor vanishes.  So
second order buys nothing unless that cofactor is zero, and whether it is zero is a
question about the matchings using both edges and about nothing else. -/
theorem second_order_factors (W A : Sym2 (V × C) → R) (c : V → C)
    (S : Finset V) (e₀ e₁ : Sym2 V) :
    (∑ σ ∈ pairingsOn S,
      (if e₀ ∈ S.image (fun x => s(x, σ x)) ∧ e₁ ∈ S.image (fun x => s(x, σ x)) then
          A (Sym2.map (paint c) e₀) * A (Sym2.map (paint c) e₁) *
            ∏ e ∈ ((S.image (fun x => s(x, σ x))).erase e₀).erase e₁,
              W (Sym2.map (paint c) e)
        else 0))
      = A (Sym2.map (paint c) e₀) * A (Sym2.map (paint c) e₁) *
        ∑ σ ∈ pairingsOn S,
          (if e₀ ∈ S.image (fun x => s(x, σ x)) ∧
              e₁ ∈ S.image (fun x => s(x, σ x)) then
              ∏ e ∈ ((S.image (fun x => s(x, σ x))).erase e₀).erase e₁,
                W (Sym2.map (paint c) e)
            else 0) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : e₀ ∈ S.image (fun x => s(x, σ x)) ∧ e₁ ∈ S.image (fun x => s(x, σ x))
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

section Absorb

variable {K : Type*} [Field K]

/-- **Absorbing a defect.**  A flat matching sum plus a defect on one edge *is* a
flat matching sum at perturbed weights, provided the flat term's coefficient does not
vanish.

This is the step that makes a contraction into a reduction.  Contracting a pair of
sites leaves a flat object plus a first-order defect, which is not itself a flat
object; when the defect sits on a single edge, this identity folds it back in, and
what remains is a matching sum of the same kind on two fewer vertices. -/
theorem absorb_defect_single_edge (W A : Sym2 (V × C) → K) (c : V → C) {S : Finset V}
    {p q : V} (hp : p ∈ S) (hq : q ∈ S.erase p) (s : K) (hs : s ≠ 0)
    (hA : ∀ x y : V, s(x, y) ≠ s(p, q) → A (Sym2.map (paint c) s(x, y)) = 0) :
    s * pmSum W c S
        + A (Sym2.map (paint c) s(p, q)) * pmSum W c ((S.erase p).erase q)
      = s * pmSum (fun e => W e + s⁻¹ * A e) c S := by
  rw [pmSum_perturb_single_edge W A c hp hq s⁻¹ hA]
  field_simp

/-- **Absorbing a defect of matching number one, in general.**  A flat matching sum
with nonvanishing coefficient, plus a first-order defect of matching number one, *is*
a flat matching sum at perturbed weights.

This is the reduction's absorption step in the generality the framework asks for.
Contracting a pair of sites leaves a flat object plus a defect that is not itself
flat; whenever the defect's edges pairwise meet, this identity folds it back in, and
what remains is an object of the same kind on two fewer vertices. -/
theorem absorb_defect_family (W A : Sym2 (V × C) → K) (c : V → C) {R : Finset V}
    (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∃ z : V, z ∈ e ∧ z ∈ f)
    (hA : ∀ e : Sym2 V, e ∉ E → A (Sym2.map (paint c) e) = 0)
    (s : K) (hs : s ≠ 0) :
    s * pmSum W c R
        + ∑ e ∈ E, A (Sym2.map (paint c) e) *
            ∑ σ ∈ (pairingsOn R).filter (fun σ => e ∈ R.image (fun x => s(x, σ x))),
              ∏ f ∈ (R.image (fun x => s(x, σ x))).erase e, W (Sym2.map (paint c) f)
      = s * pmSum (fun e => W e + s⁻¹ * A e) c R := by
  rw [pmSum_perturb_family W A c s⁻¹ E hE hA]
  field_simp

/-- **Absorbing a second-order defect, with its price made explicit.**  A flat
matching sum with nonvanishing coefficient, plus the first-order part of a
two-edge defect, is a flat matching sum at perturbed weights *less a single
residual term* carrying the second-order coefficient.

At first order the corresponding identity is exact, which is what lets the
reduction return an object of the same kind on two fewer vertices.  Here the
rewriting still goes through, but it does not close: the residue is the price of a
defect whose edges can both be used by one matching. -/
theorem absorb_defect_two (W A : Sym2 (V × C) → K) (c : V → C) {S : Finset V}
    {L Q : K}
    (hexp : ∀ t : K,
      pmSum (fun e => W e + t * A e) c S = pmSum W c S + t * L + t ^ 2 * Q)
    (s : K) (hs : s ≠ 0) :
    s * pmSum W c S + L
      = s * pmSum (fun e => W e + s⁻¹ * A e) c S - s⁻¹ * Q := by
  rw [hexp s⁻¹]
  field_simp
  ring

/-- **The defect absorbs exactly when its second-order coefficient vanishes.**

This is the precise condition under which the second-order theory recovers the
first-order conclusion.  The coefficient is carried by the matchings using both
defect edges, so it is a statement about those matchings and nothing else. -/
theorem absorb_defect_two_of_second_vanishes (W A : Sym2 (V × C) → K) (c : V → C)
    {S : Finset V} {L Q : K}
    (hexp : ∀ t : K,
      pmSum (fun e => W e + t * A e) c S = pmSum W c S + t * L + t ^ 2 * Q)
    (s : K) (hs : s ≠ 0) (hQ : Q = 0) :
    s * pmSum W c S + L = s * pmSum (fun e => W e + s⁻¹ * A e) c S := by
  rw [absorb_defect_two W A c hexp s hs, hQ, mul_zero, sub_zero]

end Absorb

/-! ### Factorization across a cut -/

/-- A weighted matching sum factors when every edge crossing a cut has zero
weight.  The statement is uniform in the colour type, coefficient semiring, and
ambient finite vertex type. -/
theorem pmSum_factor_of_no_crossing (W : Sym2 (V × C) → R) (c : V → C) :
    ∀ (n : ℕ) (S T : Finset V), S.card = n → S ⊆ T →
      (∀ x ∈ S, ∀ y ∈ T \ S, W s((x, c x), (y, c y)) = 0) →
      pmSum W c T = pmSum W c S * pmSum W c (T \ S) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S T hcard hsub hcut
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hS : S = ∅ := Finset.card_eq_zero.mp hcard
      subst hS
      rw [pmSum_empty, one_mul, Finset.sdiff_empty]
    · obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
      have hxT : x ∈ T := hsub hx
      rw [pmSum_expand W c hxT, pmSum_expand W c hx]
      have hsub' : S.erase x ⊆ T.erase x := Finset.erase_subset_erase _ hsub
      rw [← Finset.sum_subset hsub', Finset.sum_mul]
      · refine Finset.sum_congr rfl fun y hy => ?_
        have hyS : y ∈ S := Finset.mem_of_mem_erase hy
        have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
        have hcard' : ((S.erase x).erase y).card = n - 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hyx, hyS⟩),
            Finset.card_erase_of_mem hx, hcard]
          omega
        have hsub'' : (S.erase x).erase y ⊆ (T.erase x).erase y :=
          Finset.erase_subset_erase _ hsub'
        have hsdiff : (T.erase x).erase y \ ((S.erase x).erase y) = T \ S := by
          ext z
          simp only [Finset.mem_sdiff, Finset.mem_erase]
          constructor
          · rintro ⟨⟨hz1, hz2, hz3⟩, hz4⟩
            refine ⟨hz3, fun hzS => hz4 ⟨hz1, hz2, hzS⟩⟩
          · rintro ⟨hz1, hz2⟩
            refine ⟨⟨fun h => hz2 (h ▸ hyS), fun h => hz2 (h ▸ hx), hz1⟩, ?_⟩
            rintro ⟨-, -, hzS⟩
            exact hz2 hzS
        have hcut'' : ∀ p ∈ (S.erase x).erase y, ∀ q ∈ (T.erase x).erase y \
            ((S.erase x).erase y), W s((p, c p), (q, c q)) = 0 := by
          intro p hp q hq
          rw [hsdiff] at hq
          exact hcut p (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)) q hq
        have := ih (n - 2) (by omega) ((S.erase x).erase y) ((T.erase x).erase y)
          hcard' hsub'' hcut''
        rw [this, hsdiff, mul_assoc]
      · intro y hy hyn
        have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
        have hyS : y ∉ S := fun h => hyn (Finset.mem_erase.mpr ⟨hyx, h⟩)
        have hmem : y ∈ T \ S := Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hy).2, hyS⟩
        have : W (Sym2.map (paint c) s(x, y)) = 0 := hcut x hx y hmem
        rw [this, zero_mul]

/-- The vertices carrying one chosen colour. -/
def colourFiber [DecidableEq C] (c : V → C) (k : C) : Finset V :=
  Finset.univ.filter (fun x => c x = k)

omit [DecidableEq V] in
@[simp] lemma mem_colourFiber [DecidableEq C] {c : V → C} {k : C} {x : V} :
    x ∈ colourFiber c k ↔ c x = k := by
  simp [colourFiber]

/-- A colouring whose chosen colour class has no live crossing to its complement
splits its amplitude into the matching sums on the two sides. -/
theorem pmSum_colourFiber_split [DecidableEq C]
    (W : Sym2 (V × C) → R) (c : V → C)
    (hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0)
    (k : C) :
    amplitude W c =
      pmSum W c (colourFiber c k) * pmSum W c (Finset.univ \ colourFiber c k) := by
  rw [← pmSum_univ]
  refine pmSum_factor_of_no_crossing W c (colourFiber c k).card
    (colourFiber c k) Finset.univ rfl (Finset.subset_univ _) ?_
  intro x hx y hy
  rw [mem_colourFiber] at hx
  have hy' : c y ≠ k := by
    intro h
    exact (Finset.mem_sdiff.mp hy).2 (mem_colourFiber.mpr h)
  exact hcut x y (by rw [hx]; exact fun h => hy' h.symm)

end MatchingSum
