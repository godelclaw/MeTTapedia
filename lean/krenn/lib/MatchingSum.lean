import Mathlib
import MatchingParity
import Amplitude

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
  push_neg at hcon
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
