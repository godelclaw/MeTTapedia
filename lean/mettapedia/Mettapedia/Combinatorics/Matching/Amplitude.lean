import Mathlib

/-!
# The inherited-colouring amplitude, uniform in vertices and colours

For a finite vertex type `V`, a colour type `C`, and weights on unordered pairs
of coloured incidences, the amplitude of a colouring sums, over every perfect
matching, the product of the weights its edges carry under that colouring.

Both parameters are free.  Nothing here mentions six vertices or three colours,
and the naturality statement below is what makes the colour parameter collapse:
restricting the colours of a solution restricts the amplitude on the nose,
because the amplitude is a natural transformation in the colour type.

The vertex parameter has no such property, and that asymmetry is the reason the
conjecture is hard.  A colouring restricts along `C' → C`; a perfect matching of
`V` does not restrict to a perfect matching of a proper subtype of `V`.
-/

namespace Amplitude

variable {V C C' : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommSemiring R]

/-- The perfect matchings of `V`, as the fixed-point-free involutions. -/
def pairings (V : Type*) [Fintype V] [DecidableEq V] : Finset (Equiv.Perm V) :=
  Finset.univ.filter (fun σ => (∀ x, σ (σ x) = x) ∧ ∀ x, σ x ≠ x)

/-- The edges of a matching, as unordered vertex pairs. -/
def edges (σ : Equiv.Perm V) : Finset (Sym2 V) :=
  Finset.univ.image (fun x => s(x, σ x))

/-- Attach to each vertex its colour, giving a coloured incidence. -/
def paint (c : V → C) : V → V × C := fun v => (v, c v)

/-- **The amplitude.**  Sum over perfect matchings of the product of the weights
of their edges, read with the given colouring. -/
def amplitude (W : Sym2 (V × C) → R) (c : V → C) : R :=
  ∑ σ ∈ pairings V, ∏ e ∈ edges σ, W (Sym2.map (paint c) e)

omit [Fintype V] [DecidableEq V] in
/-- Recolouring commutes with painting. -/
lemma map_paint (f : C → C') (c : V → C) (e : Sym2 V) :
    Sym2.map (Prod.map id f) (Sym2.map (paint c) e) = Sym2.map (paint (f ∘ c)) e := by
  rw [Sym2.map_map]
  rfl

/-- **Naturality in the colour type.**  Pushing weights forward along a
recolouring and evaluating at `c` is the same as evaluating the original weights
at the recoloured `f ∘ c`.  This holds for every vertex type and every pair of
colour types. -/
theorem amplitude_comp (f : C → C') (W : Sym2 (V × C') → R) (c : V → C) :
    amplitude (fun e => W (Sym2.map (Prod.map id f) e)) c = amplitude W (f ∘ c) := by
  unfold amplitude
  refine Finset.sum_congr rfl (fun σ _ => Finset.prod_congr rfl (fun e _ => ?_))
  exact congrArg W (map_paint f c e)

/-- Restricting weights along a colour inclusion. -/
def restrict (f : C → C') (W : Sym2 (V × C') → R) : Sym2 (V × C) → R :=
  fun e => W (Sym2.map (Prod.map id f) e)

/-- **Colour restriction.**  Every amplitude of the restricted weights is an
amplitude of the original weights.  A solution over the larger colour type
therefore restricts to one over the smaller, which is exactly why the colour
parameter of the conjecture collapses to three and needs no induction. -/
theorem amplitude_restrict (f : C → C') (W : Sym2 (V × C') → R) (c : V → C) :
    amplitude (restrict f W) c = amplitude W (f ∘ c) :=
  amplitude_comp f W c

/-- A colouring is monochromatic when it uses a single colour. -/
def Monochromatic (c : V → C) : Prop := ∃ k, ∀ v, c v = k

omit [Fintype V] [DecidableEq V] in
/-- Recolouring along an injection preserves and reflects monochromaticity, so
the two sides of `amplitude_restrict` classify the same equations. -/
theorem monochromatic_comp_iff {f : C → C'} (hf : Function.Injective f)
    [Nonempty V] (c : V → C) :
    Monochromatic (f ∘ c) ↔ Monochromatic c := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨v₀⟩ := ‹Nonempty V›
    refine ⟨c v₀, fun v => hf ?_⟩
    simpa using (hk v).trans (hk v₀).symm
  · rintro ⟨k, hk⟩
    exact ⟨f k, fun v => by simp [hk v]⟩

/-! ### Computing with matchings -/

variable {σ : Equiv.Perm V}

lemma mem_pairings_iff :
    σ ∈ pairings V ↔ (∀ x, σ (σ x) = x) ∧ ∀ x, σ x ≠ x := by
  simp [pairings]

/-- The edges of a matching are exactly the matched pairs. -/
lemma mem_edges_iff (hσ : σ ∈ pairings V) (a b : V) :
    s(a, b) ∈ edges σ ↔ σ a = b := by
  rw [mem_pairings_iff] at hσ
  constructor
  · intro h
    simp only [edges, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨x, hx⟩ := h
    rw [Sym2.eq_iff] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, h2]
    · rw [← h2, ← h1, hσ.1]
  · rintro rfl
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

/-- The fibre of the edge map over a matched pair is exactly that pair. -/
lemma fibre_eq (hσ : σ ∈ pairings V) (a : V) :
    (Finset.univ.filter (fun x => s(x, σ x) = s(a, σ a))) = {a, σ a} := by
  have hinv := (mem_pairings_iff.mp hσ).1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Sym2.eq_iff]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, h2⟩)
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, hinv a⟩

/-- **A perfect matching has half as many edges as vertices.** -/
theorem two_mul_card_edges (hσ : σ ∈ pairings V) :
    2 * (edges σ).card = Fintype.card V := by
  have hne := (mem_pairings_iff.mp hσ).2
  have hmaps : ∀ x ∈ (Finset.univ : Finset V), s(x, σ x) ∈ edges σ :=
    fun x _ => Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hcount := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ e ∈ edges σ,
      (Finset.univ.filter (fun x => s(x, σ x) = e)).card = 2 := by
    intro e he
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp he
    rw [fibre_eq hσ a, Finset.card_insert_of_notMem (by simpa using (hne a).symm),
      Finset.card_singleton]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_univ] at hcount
  omega


/-- Relabelling vertices carries a matching to a matching. -/
lemma conj_mem_pairings (hσ : σ ∈ pairings V) (τ : Equiv.Perm V) :
    τ * σ * τ⁻¹ ∈ pairings V := by
  rw [mem_pairings_iff] at hσ ⊢
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [hσ.1]
    simp
  · simp only [Equiv.Perm.mul_apply] at hx
    refine hσ.2 (τ⁻¹ x) ?_
    calc σ (τ⁻¹ x) = τ⁻¹ (τ (σ (τ⁻¹ x))) := by
          simp [Equiv.Perm.inv_def]
      _ = τ⁻¹ x := by rw [hx]

/-- **Vertex equivariance of the edge set.**  Relabelling the vertices relabels
the edges, so the matching structure transports along any permutation. -/
theorem edges_conj (τ : Equiv.Perm V) :
    edges (τ * σ * τ⁻¹) = (edges σ).image (Sym2.map τ) := by
  ext e
  simp only [edges, Finset.mem_image, Finset.mem_univ, true_and, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_def]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨s(τ.symm x, σ (τ.symm x)), ⟨τ.symm x, rfl⟩, ?_⟩
    simp
  · rintro ⟨f, ⟨x, rfl⟩, rfl⟩
    refine ⟨τ x, ?_⟩
    simp

/-! ### Extracting a matching from a nonvanishing amplitude -/

/-- **Extraction.**  If the amplitude of a colouring does not vanish, some
perfect matching carries a nonzero weight product under it.  This is the step
that turns a hypothetical solution into concrete combinatorial data. -/
theorem exists_matching_of_amplitude_ne_zero
    (W : Sym2 (V × C) → R) (c : V → C) (h : amplitude W c ≠ 0) :
    ∃ σ ∈ pairings V, (∏ e ∈ edges σ, W (Sym2.map (paint c) e)) ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (Finset.sum_eq_zero hc)

/-- A colouring using the single colour `k`. -/
def const (k : C) : V → C := fun _ => k

omit [Fintype V] [DecidableEq V] in
@[simp] lemma monochromatic_const (k : C) : Monochromatic (const (V := V) k) := ⟨k, fun _ => rfl⟩

/-- **The matching triple.**  If all three monochromatic amplitudes are nonzero,
the solution supplies one perfect matching per colour — the triple whose orbit
classification is the combinatorial heart of the argument. -/
theorem exists_matching_triple (W : Sym2 (V × C) → R) (k : Fin 3 → C)
    (h : ∀ i, amplitude W (const (V := V) (k i)) ≠ 0) :
    ∃ σ : Fin 3 → Equiv.Perm V, (∀ i, σ i ∈ pairings V) ∧
      ∀ i, (∏ e ∈ edges (σ i), W (Sym2.map (paint (const (V := V) (k i))) e)) ≠ 0 := by
  choose σ hσ hne using fun i => exists_matching_of_amplitude_ne_zero W _ (h i)
  exact ⟨σ, hσ, hne⟩


/-! ### Which edges a solution forces to be nonzero -/

/-- Over a ring without zero divisors, a matching whose weight product is nonzero
has every one of its edge weights nonzero. -/
theorem edge_weight_ne_zero_of_prod_ne_zero [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R) (c : V → C) {σ : Equiv.Perm V}
    (h : (∏ e ∈ edges σ, W (Sym2.map (paint c) e)) ≠ 0) :
    ∀ e ∈ edges σ, W (Sym2.map (paint c) e) ≠ 0 :=
  fun e he => (Finset.prod_ne_zero_iff.mp h) e he

/-- **The skeleton carries nonzero monochromatic weights.**  A solution whose
three monochromatic amplitudes are nonzero supplies, for each colour, a perfect
matching every one of whose edges has nonzero weight in that colour.  This is the
orbit hypothesis of the six-vertex analysis, stated for an arbitrary vertex
count. -/
theorem skeleton_edges_ne_zero [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R) (k : Fin 3 → C)
    (h : ∀ i, amplitude W (const (V := V) (k i)) ≠ 0) :
    ∃ σ : Fin 3 → Equiv.Perm V, (∀ i, σ i ∈ pairings V) ∧
      ∀ i, ∀ e ∈ edges (σ i),
        W (Sym2.map (paint (const (V := V) (k i))) e) ≠ 0 := by
  obtain ⟨σ, hmem, hne⟩ := exists_matching_triple W k h
  exact ⟨σ, hmem, fun i => edge_weight_ne_zero_of_prod_ne_zero W _ (hne i)⟩

/-! ### A unique surviving matching -/

/-- If every matching other than `σ` carries a zero-weight edge under `c`, the
amplitude is exactly `σ`'s weight product. -/
theorem amplitude_eq_of_unique_survivor (W : Sym2 (V × C) → R) (c : V → C)
    {σ : Equiv.Perm V} (hσ : σ ∈ pairings V)
    (h : ∀ τ ∈ pairings V, τ ≠ σ → ∃ e ∈ edges τ, W (Sym2.map (paint c) e) = 0) :
    amplitude W c = ∏ e ∈ edges σ, W (Sym2.map (paint c) e) := by
  refine Finset.sum_eq_single σ (fun τ hτ hne => ?_) (fun hns => absurd hσ hns)
  obtain ⟨e, he, hz⟩ := h τ hτ hne
  exact Finset.prod_eq_zero he hz

/-- **One survivor cannot vanish.**  A colouring whose amplitude is zero cannot
have exactly one matching of nonzero weight.  At six vertices this was the whole
content of the support abstraction; it holds at every vertex count, and it is the
only support-level obstruction there is. -/
theorem not_unique_survivor_of_amplitude_zero (W : Sym2 (V × C) → R) (c : V → C)
    {σ : Equiv.Perm V} (hσ : σ ∈ pairings V)
    (hzero : amplitude W c = 0)
    (hne : (∏ e ∈ edges σ, W (Sym2.map (paint c) e)) ≠ 0) :
    ∃ τ ∈ pairings V, τ ≠ σ ∧ ∀ e ∈ edges τ, W (Sym2.map (paint c) e) ≠ 0 := by
  by_contra hc
  push Not at hc
  refine hne ?_
  rw [← amplitude_eq_of_unique_survivor W c hσ (fun τ hτ hτσ => ?_), hzero]
  obtain ⟨e, he, hz⟩ := hc τ hτ hτσ
  exact ⟨e, he, hz⟩

/-! ### Restricting a matching away from one of its edges

The combinatorial half of a two-vertex descent: a matching that uses `{u, v}`
restricts to a matching of the remaining vertices.  Nothing here fixes how many
vertices there are.
-/

/-- The vertices other than `u` and `v`. -/
abbrev Rest (u v : V) := {x : V // x ≠ u ∧ x ≠ v}

variable {u v : V}

/-- A matching using `{u, v}` maps the remaining vertices among themselves. -/
theorem partner_mem_rest {σ : Equiv.Perm V} (hσ : σ ∈ pairings V) (h : σ u = v)
    {x : V} (hx : x ≠ u ∧ x ≠ v) : σ x ≠ u ∧ σ x ≠ v := by
  obtain ⟨hinv, _⟩ := mem_pairings_iff.mp hσ
  constructor
  · intro hc
    exact hx.2 (by rw [← h, ← hc, hinv])
  · intro hc
    exact hx.1 (by
      have : σ x = σ u := by rw [hc, h]
      exact σ.injective this)

/-- The restriction of a matching to the vertices it does not match through
`{u, v}`. -/
def restrictPairing (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (h : σ u = v) :
    Equiv.Perm (Rest u v) where
  toFun x := ⟨σ x.1, partner_mem_rest hσ h x.2⟩
  invFun x := ⟨σ x.1, partner_mem_rest hσ h x.2⟩
  left_inv x := by
    obtain ⟨hinv, _⟩ := mem_pairings_iff.mp hσ
    exact Subtype.ext (hinv x.1)
  right_inv x := by
    obtain ⟨hinv, _⟩ := mem_pairings_iff.mp hσ
    exact Subtype.ext (hinv x.1)

/-- **The restriction is again a perfect matching.**  So a skeleton with an edge
shared by all three colours restricts to a skeleton on two fewer vertices — the
combinatorial step a descent argument needs, available at every vertex count. -/
theorem restrictPairing_mem_pairings [DecidableEq (Rest u v)] [Fintype (Rest u v)]
    (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (h : σ u = v) :
    restrictPairing σ hσ h ∈ pairings (Rest u v) := by
  obtain ⟨hinv, hnf⟩ := mem_pairings_iff.mp hσ
  refine mem_pairings_iff.mpr ⟨fun x => Subtype.ext (hinv x.1), fun x hc => ?_⟩
  exact hnf x.1 (congrArg Subtype.val hc)

/-- The edges of a restricted matching, mapped back up, are exactly the original
matching's edges other than the one it was restricted away from.  This is the
bridge that lets a weight product on the smaller vertex set be compared with the
original. -/
theorem edges_restrictPairing [DecidableEq (Rest u v)] [Fintype (Rest u v)]
    (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (h : σ u = v) :
    (edges (restrictPairing σ hσ h)).image (Sym2.map Subtype.val)
      = (edges σ).erase s(u, v) := by
  obtain ⟨hinv, hnf⟩ := mem_pairings_iff.mp hσ
  ext e
  simp only [edges, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase,
    restrictPairing, Equiv.coe_fn_mk]
  constructor
  · rintro ⟨f, ⟨x, rfl⟩, rfl⟩
    simp only [Sym2.map_mk]
    refine ⟨?_, ⟨x.1, rfl⟩⟩
    intro hc
    rw [Sym2.eq_iff] at hc
    rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact x.2.1 h1
    · exact x.2.2 h1
  · rintro ⟨hne, ⟨x, rfl⟩⟩
    have hx : x ≠ u ∧ x ≠ v := by
      constructor
      · rintro rfl; exact hne (by rw [h])
      · rintro rfl
        refine hne ?_
        rw [Sym2.eq_iff]
        right
        exact ⟨rfl, by rw [← h, hinv]⟩
    exact ⟨s(⟨x, hx⟩, ⟨σ x, partner_mem_rest hσ h hx⟩), ⟨⟨x, hx⟩, rfl⟩, by
      simp only [Sym2.map_mk]⟩

/-! ### Factoring the amplitude along an edge

Descent removes two matched vertices, so the algebra it needs is how the
amplitude decomposes according to whether a matching uses a given edge.  Both
statements below hold for an arbitrary vertex type.
-/

/-- If a matching uses the edge `{u, v}`, its weight product factors as that
edge's weight times the product over its remaining edges. -/
theorem prod_edges_factor (W : Sym2 (V × C) → R) (c : V → C) {σ : Equiv.Perm V}
    (hσ : σ ∈ pairings V) {u v : V} (h : σ u = v) :
    (∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      = W (Sym2.map (paint c) s(u, v)) *
        ∏ e ∈ (edges σ).erase s(u, v), W (Sym2.map (paint c) e) :=
  (Finset.mul_prod_erase _ _ ((mem_edges_iff hσ u v).mpr h)).symm

/-- **Splitting the amplitude along an edge.**  The matchings that use `{u, v}`
contribute a term carrying that edge's weight as a factor; the rest contribute
separately.  This is the decomposition any two-vertex descent must control. -/
theorem amplitude_split (W : Sym2 (V × C) → R) (c : V → C) (u v : V) :
    amplitude W c
      = (∑ σ ∈ (pairings V).filter (fun σ => σ u = v),
          W (Sym2.map (paint c) s(u, v)) *
            ∏ e ∈ (edges σ).erase s(u, v), W (Sym2.map (paint c) e))
        + ∑ σ ∈ (pairings V).filter (fun σ => ¬ σ u = v),
            ∏ e ∈ edges σ, W (Sym2.map (paint c) e) := by
  unfold amplitude
  rw [← Finset.sum_filter_add_sum_filter_not (pairings V) (fun σ => σ u = v)]
  congr 1
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [Finset.mem_filter] at hσ
  exact prod_edges_factor W c hσ.1 hσ.2

/-- The edge weight factors out of the whole first sum. -/
theorem amplitude_split_factor (W : Sym2 (V × C) → R) (c : V → C) (u v : V) :
    amplitude W c
      = W (Sym2.map (paint c) s(u, v)) *
          (∑ σ ∈ (pairings V).filter (fun σ => σ u = v),
            ∏ e ∈ (edges σ).erase s(u, v), W (Sym2.map (paint c) e))
        + ∑ σ ∈ (pairings V).filter (fun σ => ¬ σ u = v),
            ∏ e ∈ edges σ, W (Sym2.map (paint c) e) := by
  rw [amplitude_split W c u v, Finset.mul_sum]


/-- Weights pushed down to the remaining vertices. -/
def restrictWeight (W : Sym2 (V × C) → R) : Sym2 (Rest u v × C) → R :=
  fun e => W (Sym2.map (Prod.map Subtype.val id) e)

/-- A colouring restricted to the remaining vertices. -/
def restrictColouring (c : V → C) : Rest u v → C := fun x => c x.1

/-- **The per-matching descent identity.**  A matching using `{u, v}` has weight
product equal to that edge's weight times the weight product of its restriction,
computed with the restricted weights and colouring.  This is what makes a descent
step an identity rather than an approximation. -/
theorem prod_edges_restrictPairing [DecidableEq (Rest u v)] [Fintype (Rest u v)]
    (W : Sym2 (V × C) → R) (c : V → C) (σ : Equiv.Perm V)
    (hσ : σ ∈ pairings V) (h : σ u = v) :
    (∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      = W (Sym2.map (paint c) s(u, v)) *
          ∏ e ∈ edges (restrictPairing σ hσ h),
            restrictWeight (u := u) (v := v) W (Sym2.map (paint (restrictColouring (u := u) (v := v) c)) e) := by
  rw [prod_edges_factor W c hσ h, ← edges_restrictPairing σ hσ h]
  congr 1
  rw [Finset.prod_image (fun x _ y _ hxy => Sym2.map.injective Subtype.val_injective hxy)]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  unfold restrictWeight
  congr 1
  rw [Sym2.map_map, Sym2.map_map]
  rfl

/-- A matching using `{u, v}` is determined by its restriction: the removed edge
accounts for the only two vertices the restriction does not see. -/
theorem restrictPairing_injective {u v : V} [DecidableEq (Rest u v)] [Fintype (Rest u v)]
    {σ τ : Equiv.Perm V} (hσ : σ ∈ pairings V) (hτ : τ ∈ pairings V)
    (hs : σ u = v) (ht : τ u = v)
    (heq : restrictPairing σ hσ hs = restrictPairing τ hτ ht) : σ = τ := by
  obtain ⟨hinvσ, -⟩ := mem_pairings_iff.mp hσ
  obtain ⟨hinvτ, -⟩ := mem_pairings_iff.mp hτ
  ext x
  by_cases hxu : x = u
  · rw [hxu, hs, ht]
  · by_cases hxv : x = v
    · rw [hxv, show σ v = u from by rw [← hs, hinvσ],
        show τ v = u from by rw [← ht, hinvτ]]
    · have := congrArg (fun f => (f ⟨x, ⟨hxu, hxv⟩⟩).1) heq
      simpa [restrictPairing] using this

/-- Extend a matching of the remaining vertices across the removed edge. -/
def extendPairing {u v : V} (huv : u ≠ v) (ρ : Equiv.Perm (Rest u v))
    (hρ : ∀ x, ρ (ρ x) = x) : Equiv.Perm V where
  toFun x := if h : x = u then v else if h2 : x = v then u else (ρ ⟨x, ⟨h, h2⟩⟩).1
  invFun x := if h : x = u then v else if h2 : x = v then u else (ρ ⟨x, ⟨h, h2⟩⟩).1
  left_inv x := by
    by_cases h : x = u
    · subst h; simp [Ne.symm huv]
    · by_cases h2 : x = v
      · subst h2; simp [h]
      · have hm := (ρ ⟨x, ⟨h, h2⟩⟩).2
        simp only [dif_neg h, dif_neg h2, dif_neg hm.1, dif_neg hm.2]
        have : (⟨(ρ ⟨x, ⟨h, h2⟩⟩).1, hm⟩ : Rest u v) = ρ ⟨x, ⟨h, h2⟩⟩ := rfl
        rw [this, hρ]
  right_inv x := by
    by_cases h : x = u
    · subst h; simp [Ne.symm huv]
    · by_cases h2 : x = v
      · subst h2; simp [h]
      · have hm := (ρ ⟨x, ⟨h, h2⟩⟩).2
        simp only [dif_neg h, dif_neg h2, dif_neg hm.1, dif_neg hm.2]
        have : (⟨(ρ ⟨x, ⟨h, h2⟩⟩).1, hm⟩ : Rest u v) = ρ ⟨x, ⟨h, h2⟩⟩ := rfl
        rw [this, hρ]

omit [Fintype V] in
@[simp] theorem extendPairing_u {u v : V} (huv : u ≠ v) (ρ : Equiv.Perm (Rest u v))
    (hρ : ∀ x, ρ (ρ x) = x) : extendPairing huv ρ hρ u = v := by
  simp [extendPairing]

/-- The extension is a perfect matching whenever the original is. -/
theorem extendPairing_mem_pairings {u v : V} (huv : u ≠ v) (ρ : Equiv.Perm (Rest u v))
    (hρ : ∀ x, ρ (ρ x) = x) (hnf : ∀ x, ρ x ≠ x) :
    extendPairing huv ρ hρ ∈ pairings V := by
  refine mem_pairings_iff.mpr ⟨fun x => (extendPairing huv ρ hρ).left_inv x, fun x hc => ?_⟩
  by_cases h : x = u
  · subst h; rw [extendPairing_u] at hc; exact huv hc.symm
  · by_cases h2 : x = v
    · subst h2
      simp only [extendPairing, Equiv.coe_fn_mk, dif_neg h] at hc
      exact huv hc
    · simp only [extendPairing, Equiv.coe_fn_mk, dif_neg h, dif_neg h2] at hc
      exact hnf ⟨x, ⟨h, h2⟩⟩ (Subtype.ext hc)

/-- Restricting an extension recovers the original matching: the two
constructions are mutually inverse. -/
theorem restrictPairing_extendPairing {u v : V} [DecidableEq (Rest u v)]
    [Fintype (Rest u v)] (huv : u ≠ v) (ρ : Equiv.Perm (Rest u v))
    (hρ : ∀ x, ρ (ρ x) = x) (hnf : ∀ x, ρ x ≠ x) :
    restrictPairing (extendPairing huv ρ hρ)
      (extendPairing_mem_pairings huv ρ hρ hnf) (extendPairing_u huv ρ hρ) = ρ := by
  ext x
  show ((extendPairing huv ρ hρ) x.1) = (ρ x).1
  simp only [extendPairing, Equiv.coe_fn_mk, dif_neg x.2.1, dif_neg x.2.2]

/-- **The matchings that use a given edge correspond exactly to the matchings of
the remaining vertices.**  Both directions are constructive, so a descent step
re-indexes a sum rather than estimating it. -/
theorem restrictPairing_surjective {u v : V} [DecidableEq (Rest u v)]
    [Fintype (Rest u v)] (huv : u ≠ v) (ρ : Equiv.Perm (Rest u v))
    (hρ : ρ ∈ pairings (Rest u v)) :
    ∃ (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (h : σ u = v),
      restrictPairing σ hσ h = ρ := by
  obtain ⟨hinv, hnf⟩ := mem_pairings_iff.mp hρ
  exact ⟨extendPairing huv ρ hinv, extendPairing_mem_pairings huv ρ hinv hnf,
    extendPairing_u huv ρ hinv, restrictPairing_extendPairing huv ρ hinv hnf⟩

/-- **The descent identity at the level of amplitudes.**  The matchings that use
`{u, v}` contribute exactly that edge's weight times the amplitude on the
remaining vertices.  This is an exact re-indexing, not an estimate. -/
theorem sum_using_eq_amplitude_restrict {u v : V} [DecidableEq (Rest u v)]
    [Fintype (Rest u v)] (huv : u ≠ v) (W : Sym2 (V × C) → R) (c : V → C) :
    (∑ σ ∈ (pairings V).filter (fun σ => σ u = v),
        ∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      = W (Sym2.map (paint c) s(u, v)) *
          amplitude (restrictWeight (u := u) (v := v) W)
            (restrictColouring (u := u) (v := v) c) := by
  unfold amplitude
  rw [Finset.mul_sum]
  refine Finset.sum_bij
    (fun σ hσ => restrictPairing σ (Finset.mem_filter.mp hσ).1 (Finset.mem_filter.mp hσ).2)
    (fun σ hσ => restrictPairing_mem_pairings σ (Finset.mem_filter.mp hσ).1
      (Finset.mem_filter.mp hσ).2)
    (fun σ hσ τ hτ heq => restrictPairing_injective
      (Finset.mem_filter.mp hσ).1 (Finset.mem_filter.mp hτ).1
      (Finset.mem_filter.mp hσ).2 (Finset.mem_filter.mp hτ).2 heq)
    (fun ρ hρ => ?_) (fun σ hσ => ?_)
  · obtain ⟨σ, hσ, h, hres⟩ := restrictPairing_surjective huv ρ hρ
    exact ⟨σ, Finset.mem_filter.mpr ⟨hσ, h⟩, hres⟩
  · exact prod_edges_restrictPairing W c σ (Finset.mem_filter.mp hσ).1
      (Finset.mem_filter.mp hσ).2

/-- **The descent equation.**  When every matching avoiding `{u, v}` carries a
zero-weight edge, the amplitude on the whole vertex set is exactly the removed
edge's weight times the amplitude on the remaining vertices.  This is the
identity a two-vertex descent runs on, and it holds at every vertex count. -/
theorem amplitude_eq_mul_amplitude_restrict {u v : V} [DecidableEq (Rest u v)]
    [Fintype (Rest u v)] (huv : u ≠ v) (W : Sym2 (V × C) → R) (c : V → C)
    (h : ∀ σ ∈ pairings V, σ u ≠ v → ∃ e ∈ edges σ, W (Sym2.map (paint c) e) = 0) :
    amplitude W c
      = W (Sym2.map (paint c) s(u, v)) *
          amplitude (restrictWeight (u := u) (v := v) W)
            (restrictColouring (u := u) (v := v) c) := by
  rw [← sum_using_eq_amplitude_restrict huv W c]
  unfold amplitude
  rw [← Finset.sum_filter_add_sum_filter_not (pairings V) (fun σ => σ u = v)]
  have : (∑ σ ∈ (pairings V).filter (fun σ => ¬ σ u = v),
            ∏ e ∈ edges σ, W (Sym2.map (paint c) e)) = 0 := by
    refine Finset.sum_eq_zero (fun σ hσ => ?_)
    rw [Finset.mem_filter] at hσ
    obtain ⟨e, he, hz⟩ := h σ hσ.1 hσ.2
    exact Finset.prod_eq_zero he hz
  rw [this, add_zero]

/-! ### The vanishing condition is a forced-edge condition -/

/-- `{u, v}` is *forced* at the colouring `c` when every perfect matching whose
weights are all nonzero uses it.  Equivalently, the edge lies in every perfect
matching of the graph of nonvanishing weights. -/
def ForcedEdge (W : Sym2 (V × C) → R) (c : V → C) (u v : V) : Prop :=
  ∀ σ ∈ pairings V, (∀ e ∈ edges σ, W (Sym2.map (paint c) e) ≠ 0) → σ u = v

/-- **The condition descent needs is exactly that the edge is forced.**  This
recasts the crux in the language of matching theory: a descent step is available
at a shared skeleton edge precisely when that edge lies in every perfect matching
of the nonvanishing-weight graph, at every colouring. -/
theorem forcedEdge_iff (W : Sym2 (V × C) → R) (c : V → C) (u v : V) :
    ForcedEdge W c u v ↔
      ∀ σ ∈ pairings V, σ u ≠ v → ∃ e ∈ edges σ, W (Sym2.map (paint c) e) = 0 := by
  constructor
  · intro hf σ hσ hne
    by_contra hc
    push Not at hc
    exact hne (hf σ hσ hc)
  · intro h σ hσ hall
    by_contra hne
    obtain ⟨e, he, hz⟩ := h σ hσ hne
    exact hall e he hz

/-- The descent equation, stated with the forced-edge hypothesis. -/
theorem amplitude_eq_of_forcedEdge {u v : V} [DecidableEq (Rest u v)]
    [Fintype (Rest u v)] (huv : u ≠ v) (W : Sym2 (V × C) → R) (c : V → C)
    (hf : ForcedEdge W c u v) :
    amplitude W c
      = W (Sym2.map (paint c) s(u, v)) *
          amplitude (restrictWeight (u := u) (v := v) W)
            (restrictColouring (u := u) (v := v) c) :=
  amplitude_eq_mul_amplitude_restrict huv W c ((forcedEdge_iff W c u v).mp hf)

/-! ### The descent step -/

/-- Extend a colouring of the remaining vertices, using a chosen colour on the
removed edge. -/
def extendColouring {u v : V} (c : Rest u v → C) (k : C) : V → C :=
  fun x => if h : x = u then k else if h2 : x = v then k else c ⟨x, ⟨h, h2⟩⟩

omit [Fintype V] in
@[simp] theorem restrictColouring_extendColouring {u v : V} (c : Rest u v → C) (k : C) :
    restrictColouring (u := u) (v := v) (extendColouring c k) = c := by
  funext x
  simp [restrictColouring, extendColouring, x.2.1, x.2.2]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem restrictColouring_const {u v : V} (k : C) :
    restrictColouring (u := u) (v := v) (const (V := V) k) = const k := rfl

omit [Fintype V] in
/-- A mixed colouring stays mixed when extended. -/
theorem not_monochromatic_extendColouring {u v : V} {c : Rest u v → C} (k : C)
    (h : ¬ Monochromatic c) : ¬ Monochromatic (extendColouring c k) := by
  rintro ⟨m, hm⟩
  refine h ⟨m, fun x => ?_⟩
  have := hm x.1
  simpa [extendColouring, x.2.1, x.2.2] using this

/-- **The descent step.**  If the removed edge is forced at every colouring and
never carries weight zero, then a GHZ configuration restricts to a GHZ
configuration on two fewer vertices.  This is `Descent`, for an arbitrary vertex
type, with its hypotheses made explicit. -/
theorem descent_step {u v : V} [DecidableEq (Rest u v)] [Fintype (Rest u v)]
    [Nonempty C] [NoZeroDivisors R] (huv : u ≠ v) (W : Sym2 (V × C) → R)
    (hf : ∀ c : V → C, ForcedEdge W c u v)
    (hnz : ∀ c : V → C, W (Sym2.map (paint c) s(u, v)) ≠ 0)
    (hmono : ∀ k : C, amplitude W (const (V := V) k) ≠ 0)
    (hmix : ∀ c : V → C, ¬ Monochromatic c → amplitude W c = 0) :
    (∀ k : C, amplitude (restrictWeight (u := u) (v := v) W)
        (const (V := Rest u v) k) ≠ 0) ∧
      (∀ c : Rest u v → C, ¬ Monochromatic c →
        amplitude (restrictWeight (u := u) (v := v) W) c = 0) := by
  constructor
  · intro k hzero
    refine hmono k ?_
    rw [amplitude_eq_of_forcedEdge huv W _ (hf _), restrictColouring_const, hzero, mul_zero]
  · intro c hc
    have hext := hmix (extendColouring c (Classical.arbitrary C))
      (not_monochromatic_extendColouring _ hc)
    rw [amplitude_eq_of_forcedEdge huv W _ (hf _), restrictColouring_extendColouring] at hext
    exact (mul_eq_zero.mp hext).resolve_left (hnz _)

/-- **Forcedness at the monochromatic colourings makes the edge shared.**  If
`{u, v}` is forced at each colour's monochromatic colouring, then every one of
the three skeleton matchings uses it.  So the descent hypothesis does not merely
coexist with a shared skeleton edge -- it produces one. -/
theorem forced_mono_imp_shared {u v : V} (W : Sym2 (V × C) → R) (k : Fin 3 → C)
    (σ : Fin 3 → Equiv.Perm V) (hmem : ∀ i, σ i ∈ pairings V)
    (hnz : ∀ i, ∀ e ∈ edges (σ i),
      W (Sym2.map (paint (const (V := V) (k i))) e) ≠ 0)
    (hf : ∀ i, ForcedEdge W (const (V := V) (k i)) u v) :
    ∀ i, σ i u = v :=
  fun i => hf i (σ i) (hmem i) (hnz i)

/-- The same conclusion straight from a solution: if the edge is forced at the
monochromatic colourings, a GHZ configuration's skeleton shares it. -/
theorem forced_mono_imp_shared_of_solution [NoZeroDivisors R] [Nontrivial R]
    {u v : V} (W : Sym2 (V × C) → R) (k : Fin 3 → C)
    (hmono : ∀ i, amplitude W (const (V := V) (k i)) ≠ 0)
    (hf : ∀ i, ForcedEdge W (const (V := V) (k i)) u v) :
    ∃ σ : Fin 3 → Equiv.Perm V, (∀ i, σ i ∈ pairings V) ∧ ∀ i, σ i u = v := by
  obtain ⟨σ, hmem, hnz⟩ := skeleton_edges_ne_zero W k hmono
  exact ⟨σ, hmem, forced_mono_imp_shared W k σ hmem hnz hf⟩

/-! ### Splitting the amplitude along a vertex set

The forced-edge step deletes one edge, and forcedness is only ever supplied by a
separator of size at most two.  To pass beyond that regime the split must be
taken along an arbitrary vertex set, classifying matchings by which vertices of
the set are matched outside it.  That classification is the boundary state, and
the inner sums are the boundary signature.
-/

/-- The vertices of `A` that a matching sends outside `A`: the boundary state. -/
def crossingSet (σ : Equiv.Perm V) (A : Finset V) : Finset V := A.filter (fun x => σ x ∉ A)

/-- **The amplitude splits by boundary state.**  Grouping matchings according to
which vertices of `A` they match outside `A` decomposes the amplitude into
boundary signatures.  The single-edge split is the case `A = {u, v}`. -/
theorem amplitude_split_set (W : Sym2 (V × C) → R) (c : V → C) (A : Finset V) :
    amplitude W c
      = ∑ T ∈ A.powerset,
          ∑ σ ∈ (pairings V).filter (fun σ => crossingSet σ A = T),
            ∏ e ∈ edges σ, W (Sym2.map (paint c) e) := by
  unfold amplitude
  refine (Finset.sum_fiberwise_of_maps_to (fun σ _ => ?_) _).symm
  exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)

omit [Fintype V] in
/-- Boundary states are constrained by parity: a matching crosses an odd set an
odd number of times.  That statement lives with the matching-parity results, in
the same generality; `crossingSet` is its boundary-state form. -/
theorem crossingSet_eq_filter (σ : Equiv.Perm V) (A : Finset V) :
    crossingSet σ A = A.filter (fun x => σ x ∉ A) := rfl

/-- The vertices of `A` a matching keeps inside `A` pair up, so there are evenly
many of them. -/
theorem even_card_internal {σ : Equiv.Perm V} (hσ : σ ∈ pairings V) (A : Finset V) :
    2 * ((A.filter (fun x => σ x ∈ A)).image (fun x => s(x, σ x))).card
      = (A.filter (fun x => σ x ∈ A)).card := by
  obtain ⟨hinv, hnf⟩ := mem_pairings_iff.mp hσ
  set S := A.filter (fun x => σ x ∈ A) with hS
  have hclosed : ∀ x ∈ S, σ x ∈ S := by
    intro x hx
    rw [hS, Finset.mem_filter] at hx ⊢
    exact ⟨hx.2, by rw [hinv]; exact hx.1⟩
  have hmaps : ∀ x ∈ S, s(x, σ x) ∈ S.image (fun x => s(x, σ x)) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  have hcount := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ e ∈ S.image (fun x => s(x, σ x)),
      (S.filter (fun x => s(x, σ x) = e)).card = 2 := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have : S.filter (fun x => s(x, σ x) = s(a, σ a)) = {a, σ a} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · rintro ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩
        · exact Or.inl h1
        · exact Or.inr h1
      · rintro (rfl | rfl)
        · exact ⟨ha, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨hclosed a ha, Or.inr ⟨rfl, hinv a⟩⟩
    rw [this, Finset.card_insert_of_notMem (by simpa using (hnf a).symm), Finset.card_singleton]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hcount
  omega

/-- **Boundary states have the parity of their set.**  A matching crosses `A` an
odd number of times exactly when `A` is odd, so only half the subsets of `A` can
occur as boundary states. -/
theorem card_crossingSet_parity {σ : Equiv.Perm V} (hσ : σ ∈ pairings V) (A : Finset V) :
    (crossingSet σ A).card % 2 = A.card % 2 := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun x => σ x ∈ A)
  have := even_card_internal hσ A
  simp only [crossingSet]
  omega

/-- The vertices of `A` a matching keeps inside `A`. -/
def internalSet (σ : Equiv.Perm V) (A : Finset V) : Finset V := A.filter (fun x => σ x ∈ A)

omit [Fintype V] in
theorem internalSet_union_crossingSet (σ : Equiv.Perm V) (A : Finset V) :
    internalSet σ A ∪ crossingSet σ A = A := by
  unfold internalSet crossingSet
  exact Finset.filter_union_filter_not_eq _ _

/-- A matching maps the vertices it keeps inside `A` among themselves. -/
theorem internalSet_closed {σ : Equiv.Perm V} (hσ : σ ∈ pairings V) (A : Finset V)
    {x : V} (hx : x ∈ internalSet σ A) : σ x ∈ internalSet σ A := by
  obtain ⟨hinv, -⟩ := mem_pairings_iff.mp hσ
  rw [internalSet, Finset.mem_filter] at hx ⊢
  exact ⟨hx.2, by rw [hinv]; exact hx.1⟩

/-- **The internal part of a matching is a matching.**  Restricted to the
vertices it does not send across the boundary, a perfect matching of the whole
vertex set is a perfect matching of that subset.  This is what makes a boundary
signature well defined: for each boundary state, the inner sum runs over genuine
matchings of the non-crossing vertices. -/
def restrictToSet (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (A : Finset V) :
    Equiv.Perm {x : V // x ∈ internalSet σ A} where
  toFun x := ⟨σ x.1, internalSet_closed hσ A x.2⟩
  invFun x := ⟨σ x.1, internalSet_closed hσ A x.2⟩
  left_inv x := Subtype.ext ((mem_pairings_iff.mp hσ).1 x.1)
  right_inv x := Subtype.ext ((mem_pairings_iff.mp hσ).1 x.1)

theorem restrictToSet_mem_pairings (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (A : Finset V)
    [Fintype {x : V // x ∈ internalSet σ A}] [DecidableEq {x : V // x ∈ internalSet σ A}] :
    restrictToSet σ hσ A ∈ pairings {x : V // x ∈ internalSet σ A} := by
  obtain ⟨hinv, hnf⟩ := mem_pairings_iff.mp hσ
  exact mem_pairings_iff.mpr
    ⟨fun x => Subtype.ext (hinv x.1), fun x hc => hnf x.1 (congrArg Subtype.val hc)⟩

/-! ### Boundary signatures

A boundary signature is not a new construction: it is the amplitude of the
weights restricted to a sub-vertex-set.  Stating it that way makes every result
about amplitudes available to it directly.
-/

/-- Weights carried over to a subset of the vertices. -/
def weightOn (W : Sym2 (V × C) → R) (S : Finset V) :
    Sym2 ({x : V // x ∈ S} × C) → R :=
  fun e => W (Sym2.map (Prod.map Subtype.val id) e)

/-- A colouring carried over to a subset of the vertices. -/
def colouringOn (c : V → C) (S : Finset V) : {x : V // x ∈ S} → C := fun x => c x.1

/-- **The boundary signature** of a fragment `A` at boundary state `T`: the
amplitude of the fragment's interior, the vertices of `A` not sent across the
boundary.  The forced-edge step is the case where `A` is a single edge and `T` is
empty. -/
def signature (W : Sym2 (V × C) → R) (c : V → C) (A T : Finset V) : R :=
  amplitude (weightOn W (A \ T)) (colouringOn c (A \ T))

omit [Fintype V] [DecidableEq V] [CommSemiring R] in
/-- Restricting weights to a subset is compatible with recolouring, so
signatures inherit naturality in the colour type from the amplitude. -/
theorem weightOn_restrict (f : C → C') (W : Sym2 (V × C') → R) (S : Finset V) :
    weightOn (restrict f W) S = restrict f (weightOn W S) := by
  funext e
  unfold weightOn restrict
  congr 1
  rw [Sym2.map_map, Sym2.map_map]
  rfl

omit [Fintype V] [DecidableEq V] in
/-- A signature over the whole vertex set with empty boundary state is the
amplitude itself, up to the canonical identification of `V` with its own
universal subset. -/
theorem colouringOn_comp (f : C → C') (c : V → C) (S : Finset V) :
    colouringOn (f ∘ c) S = f ∘ colouringOn c S := rfl

/-- **The internal edges of a matching are the edges of its restriction.**  So
the internal factor of a boundary decomposition is exactly the fragment's own
matching product, which is what lets a signature stand in for it. -/
theorem edges_restrictToSet (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (A : Finset V)
    [Fintype {x : V // x ∈ internalSet σ A}] [DecidableEq {x : V // x ∈ internalSet σ A}] :
    (edges (restrictToSet σ hσ A)).image (Sym2.map Subtype.val)
      = (internalSet σ A).image (fun x => s(x, σ x)) := by
  ext e
  simp only [edges, Finset.mem_image, Finset.mem_univ, true_and, restrictToSet,
    Equiv.coe_fn_mk]
  constructor
  · rintro ⟨f, ⟨x, rfl⟩, rfl⟩
    exact ⟨x.1, x.2, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨s(⟨x, hx⟩, ⟨σ x, internalSet_closed hσ A hx⟩), ⟨⟨x, hx⟩, rfl⟩, by simp⟩

/-- The edges a matching keeps inside a set are among its edges. -/
theorem internal_edges_subset (σ : Equiv.Perm V) (A : Finset V) :
    (internalSet σ A).image (fun x => s(x, σ x)) ⊆ edges σ := by
  intro e he
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

/-- **The weight product factors through the boundary.**  A matching's weight
product is its fragment-internal product times the product over everything else:
the crossing edges and the edges lying outside the fragment.  With
`edges_restrictToSet`, the first factor is literally the signature's summand. -/
theorem prod_edges_factor_internal (W : Sym2 (V × C) → R) (c : V → C)
    (σ : Equiv.Perm V) (A : Finset V) :
    (∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      = (∏ e ∈ (internalSet σ A).image (fun x => s(x, σ x)), W (Sym2.map (paint c) e))
        * ∏ e ∈ (edges σ) \ ((internalSet σ A).image (fun x => s(x, σ x))),
            W (Sym2.map (paint c) e) := by
  rw [mul_comm]
  exact (Finset.prod_sdiff (internal_edges_subset σ A)).symm

/-- The internal factor computed with restricted weights agrees with the
internal factor computed upstairs. -/
theorem prod_internal_eq_restricted (W : Sym2 (V × C) → R) (c : V → C)
    (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (A : Finset V)
    [Fintype {x : V // x ∈ internalSet σ A}] [DecidableEq {x : V // x ∈ internalSet σ A}] :
    (∏ e ∈ edges (restrictToSet σ hσ A),
        weightOn W (internalSet σ A)
          (Sym2.map (paint (colouringOn c (internalSet σ A))) e))
      = ∏ e ∈ (internalSet σ A).image (fun x => s(x, σ x)), W (Sym2.map (paint c) e) := by
  rw [← edges_restrictToSet σ hσ A,
    Finset.prod_image (fun x _ y _ hxy => Sym2.map.injective Subtype.val_injective hxy)]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  unfold weightOn
  congr 1
  rw [Sym2.map_map, Sym2.map_map]
  rfl

/-- A matching maps the complement of its internal set to itself. -/
theorem compl_internalSet_closed {σ : Equiv.Perm V} (hσ : σ ∈ pairings V) (A : Finset V)
    {x : V} (hx : x ∉ internalSet σ A) : σ x ∉ internalSet σ A := by
  intro hc
  exact hx (by
    have := internalSet_closed hσ A hc
    rwa [(mem_pairings_iff.mp hσ).1 x] at this)

/-- **Both sides of a boundary are matched internally.**  A matching splits into
its restriction to a fragment's interior and its restriction to everything else,
and both are perfect matchings of their own vertex sets.  So the outside factor
of a boundary decomposition is itself a matching product, determined by the
matching only through its behaviour off the fragment. -/
def restrictToCompl (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (A : Finset V) :
    Equiv.Perm {x : V // x ∉ internalSet σ A} where
  toFun x := ⟨σ x.1, compl_internalSet_closed hσ A x.2⟩
  invFun x := ⟨σ x.1, compl_internalSet_closed hσ A x.2⟩
  left_inv x := Subtype.ext ((mem_pairings_iff.mp hσ).1 x.1)
  right_inv x := Subtype.ext ((mem_pairings_iff.mp hσ).1 x.1)

theorem restrictToCompl_mem_pairings (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (A : Finset V)
    [Fintype {x : V // x ∉ internalSet σ A}] [DecidableEq {x : V // x ∉ internalSet σ A}] :
    restrictToCompl σ hσ A ∈ pairings {x : V // x ∉ internalSet σ A} := by
  obtain ⟨hinv, hnf⟩ := mem_pairings_iff.mp hσ
  exact mem_pairings_iff.mpr
    ⟨fun x => Subtype.ext (hinv x.1), fun x hc => hnf x.1 (congrArg Subtype.val hc)⟩

/-- The two restrictions cover the vertex set between them. -/
theorem internalSet_union_compl (σ : Equiv.Perm V) (A : Finset V) :
    internalSet σ A ∪ (Finset.univ \ internalSet σ A) = Finset.univ :=
  Finset.union_sdiff_of_subset (Finset.subset_univ _)

/-- Edges inside a fragment and edges outside it are distinct edges. -/
theorem internal_compl_edges_disjoint {σ : Equiv.Perm V} (hσ : σ ∈ pairings V)
    (A : Finset V) :
    Disjoint ((internalSet σ A).image (fun x => s(x, σ x)))
      ((Finset.univ \ internalSet σ A).image (fun x => s(x, σ x))) := by
  rw [Finset.disjoint_left]
  rintro e he hf
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hf
  rw [Finset.mem_sdiff] at hy
  rw [Sym2.eq_iff] at hxy
  rcases hxy with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hy.2 (by rw [h1]; exact hx)
  · have hmem : σ x ∈ internalSet σ A := internalSet_closed hσ A hx
    exact hy.2 (by rw [h1]; exact hmem)

/-- The edges of a matching are those inside a fragment together with those
outside it. -/
theorem edges_eq_internal_union_compl (σ : Equiv.Perm V) (A : Finset V) :
    edges σ = (internalSet σ A).image (fun x => s(x, σ x))
      ∪ (Finset.univ \ internalSet σ A).image (fun x => s(x, σ x)) := by
  rw [← Finset.image_union, internalSet_union_compl]
  rfl

/-- **A matching's weight product is the product of its two sides.**  The
fragment-internal product times the product over everything else, with no term
counted twice and none omitted.  This is the quantitative form of the
composition law at the level of a single matching. -/
theorem prod_edges_split_two (W : Sym2 (V × C) → R) (c : V → C)
    {σ : Equiv.Perm V} (hσ : σ ∈ pairings V) (A : Finset V) :
    (∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      = (∏ e ∈ (internalSet σ A).image (fun x => s(x, σ x)), W (Sym2.map (paint c) e))
        * ∏ e ∈ (Finset.univ \ internalSet σ A).image (fun x => s(x, σ x)),
            W (Sym2.map (paint c) e) := by
  rw [edges_eq_internal_union_compl σ A,
    Finset.prod_union (internal_compl_edges_disjoint hσ A)]

/-! ### Gluing two matchings across a boundary -/

/-- Glue a matching of `S` to a matching of its complement. -/
def glue (S : Finset V) (ρ : Equiv.Perm {x : V // x ∈ S})
    (τ : Equiv.Perm {x : V // x ∉ S}) : Equiv.Perm V where
  toFun x := if h : x ∈ S then (ρ ⟨x, h⟩).1 else (τ ⟨x, h⟩).1
  invFun x := if h : x ∈ S then (ρ.symm ⟨x, h⟩).1 else (τ.symm ⟨x, h⟩).1
  left_inv x := by
    by_cases h : x ∈ S
    · simp only [dif_pos h, dif_pos (ρ ⟨x, h⟩).2]
      have : (⟨(ρ ⟨x, h⟩).1, (ρ ⟨x, h⟩).2⟩ : {y : V // y ∈ S}) = ρ ⟨x, h⟩ := rfl
      rw [this, Equiv.symm_apply_apply]
    · simp only [dif_neg h, dif_neg (τ ⟨x, h⟩).2]
      have : (⟨(τ ⟨x, h⟩).1, (τ ⟨x, h⟩).2⟩ : {y : V // y ∉ S}) = τ ⟨x, h⟩ := rfl
      rw [this, Equiv.symm_apply_apply]
  right_inv x := by
    by_cases h : x ∈ S
    · simp only [dif_pos h, dif_pos (ρ.symm ⟨x, h⟩).2]
      have : (⟨(ρ.symm ⟨x, h⟩).1, (ρ.symm ⟨x, h⟩).2⟩ : {y : V // y ∈ S}) = ρ.symm ⟨x, h⟩ := rfl
      rw [this, Equiv.apply_symm_apply]
    · simp only [dif_neg h, dif_neg (τ.symm ⟨x, h⟩).2]
      have : (⟨(τ.symm ⟨x, h⟩).1, (τ.symm ⟨x, h⟩).2⟩ : {y : V // y ∉ S}) = τ.symm ⟨x, h⟩ := rfl
      rw [this, Equiv.apply_symm_apply]

/-- **Gluing two perfect matchings gives a perfect matching.**  A matching of a
vertex set and a matching of its complement combine into a matching of
everything, which is the converse of splitting a matching along a boundary. -/
theorem glue_mem_pairings (S : Finset V) [Fintype {x : V // x ∈ S}]
    [DecidableEq {x : V // x ∈ S}] [Fintype {x : V // x ∉ S}]
    [DecidableEq {x : V // x ∉ S}]
    (ρ : Equiv.Perm {x : V // x ∈ S}) (τ : Equiv.Perm {x : V // x ∉ S})
    (hρ : ρ ∈ pairings {x : V // x ∈ S}) (hτ : τ ∈ pairings {x : V // x ∉ S}) :
    glue S ρ τ ∈ pairings V := by
  obtain ⟨hρi, hρn⟩ := mem_pairings_iff.mp hρ
  obtain ⟨hτi, hτn⟩ := mem_pairings_iff.mp hτ
  refine mem_pairings_iff.mpr ⟨fun x => ?_, fun x hc => ?_⟩
  · by_cases h : x ∈ S
    · simp only [glue, Equiv.coe_fn_mk, dif_pos h, dif_pos (ρ ⟨x, h⟩).2]
      have : (⟨(ρ ⟨x, h⟩).1, (ρ ⟨x, h⟩).2⟩ : {y : V // y ∈ S}) = ρ ⟨x, h⟩ := rfl
      rw [this, hρi]
    · simp only [glue, Equiv.coe_fn_mk, dif_neg h, dif_neg (τ ⟨x, h⟩).2]
      have : (⟨(τ ⟨x, h⟩).1, (τ ⟨x, h⟩).2⟩ : {y : V // y ∉ S}) = τ ⟨x, h⟩ := rfl
      rw [this, hτi]
  · by_cases h : x ∈ S
    · exact hρn ⟨x, h⟩ (Subtype.ext (by simpa [glue, dif_pos h] using hc))
    · exact hτn ⟨x, h⟩ (Subtype.ext (by simpa [glue, dif_neg h] using hc))

omit [Fintype V] in
@[simp] theorem glue_apply_mem (S : Finset V) (ρ : Equiv.Perm {x : V // x ∈ S})
    (τ : Equiv.Perm {x : V // x ∉ S}) {x : V} (h : x ∈ S) :
    glue S ρ τ x = (ρ ⟨x, h⟩).1 := by
  simp [glue, dif_pos h]

omit [Fintype V] in
@[simp] theorem glue_apply_not_mem (S : Finset V) (ρ : Equiv.Perm {x : V // x ∈ S})
    (τ : Equiv.Perm {x : V // x ∉ S}) {x : V} (h : x ∉ S) :
    glue S ρ τ x = (τ ⟨x, h⟩).1 := by
  simp [glue, dif_neg h]

omit [Fintype V] in
/-- A glued matching keeps exactly the glued set inside itself. -/
theorem internalSet_glue (S : Finset V) (ρ : Equiv.Perm {x : V // x ∈ S})
    (τ : Equiv.Perm {x : V // x ∉ S}) : internalSet (glue S ρ τ) S = S := by
  ext x
  simp only [internalSet, Finset.mem_filter, and_iff_left_iff_imp]
  intro hx
  rw [glue_apply_mem S ρ τ hx]
  exact (ρ ⟨x, hx⟩).2

/-- **Gluing then restricting recovers the original.**  So the split and glue
constructions are mutually inverse, and matchings of the whole vertex set that
keep a set inside itself correspond exactly to pairs of matchings of that set and
its complement. -/
theorem restrictToSet_glue (S : Finset V) [Fintype {x : V // x ∈ S}]
    [DecidableEq {x : V // x ∈ S}] [Fintype {x : V // x ∉ S}]
    [DecidableEq {x : V // x ∉ S}]
    (ρ : Equiv.Perm {x : V // x ∈ S}) (τ : Equiv.Perm {x : V // x ∉ S})
    (hρ : ρ ∈ pairings {x : V // x ∈ S}) (hτ : τ ∈ pairings {x : V // x ∉ S})
    {x : V} (hx : x ∈ internalSet (glue S ρ τ) S) :
    (restrictToSet (glue S ρ τ) (glue_mem_pairings S ρ τ hρ hτ) S ⟨x, hx⟩).1
      = (ρ ⟨x, by rwa [internalSet_glue] at hx⟩).1 := by
  show glue S ρ τ x = _
  rw [glue_apply_mem S ρ τ (by rwa [internalSet_glue] at hx)]

/-! ### Restriction to a closed set

`restrictToSet` lands in `Perm {x // x ∈ internalSet σ A}`, a type that is only
propositionally equal to `Perm {x // x ∈ A}` even when the two sets coincide.
For a set the matching already keeps to itself, restricting directly avoids that
mismatch and makes the composition law statable.
-/

/-- A matching keeps the complement of a closed set to itself. -/
theorem compl_closed_of_closed {σ : Equiv.Perm V} (hσ : σ ∈ pairings V) {S : Finset V}
    (h : ∀ x ∈ S, σ x ∈ S) {x : V} (hx : x ∉ S) : σ x ∉ S := by
  intro hc
  exact hx (by
    have := h _ hc
    rwa [(mem_pairings_iff.mp hσ).1 x] at this)

/-- The restriction of a matching to a set it keeps to itself. -/
def restrictClosed (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (S : Finset V)
    (h : ∀ x ∈ S, σ x ∈ S) : Equiv.Perm {x : V // x ∈ S} where
  toFun x := ⟨σ x.1, h x.1 x.2⟩
  invFun x := ⟨σ x.1, h x.1 x.2⟩
  left_inv x := Subtype.ext ((mem_pairings_iff.mp hσ).1 x.1)
  right_inv x := Subtype.ext ((mem_pairings_iff.mp hσ).1 x.1)

/-- The restriction of a matching to the complement of a set it keeps. -/
def restrictClosedCompl (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (S : Finset V)
    (h : ∀ x ∈ S, σ x ∈ S) : Equiv.Perm {x : V // x ∉ S} where
  toFun x := ⟨σ x.1, compl_closed_of_closed hσ h x.2⟩
  invFun x := ⟨σ x.1, compl_closed_of_closed hσ h x.2⟩
  left_inv x := Subtype.ext ((mem_pairings_iff.mp hσ).1 x.1)
  right_inv x := Subtype.ext ((mem_pairings_iff.mp hσ).1 x.1)

theorem restrictClosed_mem_pairings (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (S : Finset V)
    (h : ∀ x ∈ S, σ x ∈ S) [Fintype {x : V // x ∈ S}] [DecidableEq {x : V // x ∈ S}] :
    restrictClosed σ hσ S h ∈ pairings {x : V // x ∈ S} := by
  obtain ⟨hinv, hnf⟩ := mem_pairings_iff.mp hσ
  exact mem_pairings_iff.mpr
    ⟨fun x => Subtype.ext (hinv x.1), fun x hc => hnf x.1 (congrArg Subtype.val hc)⟩

theorem restrictClosedCompl_mem_pairings (σ : Equiv.Perm V) (hσ : σ ∈ pairings V)
    (S : Finset V) (h : ∀ x ∈ S, σ x ∈ S)
    [Fintype {x : V // x ∉ S}] [DecidableEq {x : V // x ∉ S}] :
    restrictClosedCompl σ hσ S h ∈ pairings {x : V // x ∉ S} := by
  obtain ⟨hinv, hnf⟩ := mem_pairings_iff.mp hσ
  exact mem_pairings_iff.mpr
    ⟨fun x => Subtype.ext (hinv x.1), fun x hc => hnf x.1 (congrArg Subtype.val hc)⟩

omit [Fintype V] in
/-- A glued matching keeps the glued set to itself. -/
theorem glue_closed (S : Finset V) (ρ : Equiv.Perm {x : V // x ∈ S})
    (τ : Equiv.Perm {x : V // x ∉ S}) : ∀ x ∈ S, glue S ρ τ x ∈ S := by
  intro x hx
  rw [glue_apply_mem S ρ τ hx]
  exact (ρ ⟨x, hx⟩).2

/-- **Gluing then restricting is the identity, in matching types.**  With the
mismatch removed, the correspondence between matchings of the whole vertex set
that keep a set to itself and pairs of matchings of the two sides is an
equality of the relevant permutations. -/
theorem restrictClosed_glue (S : Finset V) (ρ : Equiv.Perm {x : V // x ∈ S})
    (τ : Equiv.Perm {x : V // x ∉ S}) (hg : glue S ρ τ ∈ pairings V) :
    restrictClosed (glue S ρ τ) hg S (glue_closed S ρ τ) = ρ := by
  ext x
  show glue S ρ τ x.1 = (ρ x).1
  rw [glue_apply_mem S ρ τ x.2]

omit [Fintype V] in
/-- A set the matching keeps to itself is its own internal set. -/
theorem internalSet_eq_of_closed {σ : Equiv.Perm V} {S : Finset V}
    (h : ∀ x ∈ S, σ x ∈ S) : internalSet σ S = S := by
  ext x
  simp only [internalSet, Finset.mem_filter, and_iff_left_iff_imp]
  exact h x

/-- The edges of a closed-set restriction, mapped back up, are the matching's
edges at that set. -/
theorem edges_restrictClosed (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (S : Finset V)
    (h : ∀ x ∈ S, σ x ∈ S) [Fintype {x : V // x ∈ S}] [DecidableEq {x : V // x ∈ S}] :
    (edges (restrictClosed σ hσ S h)).image (Sym2.map Subtype.val)
      = S.image (fun x => s(x, σ x)) := by
  ext e
  simp only [edges, Finset.mem_image, Finset.mem_univ, true_and, restrictClosed,
    Equiv.coe_fn_mk]
  constructor
  · rintro ⟨f, ⟨x, rfl⟩, rfl⟩
    exact ⟨x.1, x.2, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨s(⟨x, hx⟩, ⟨σ x, h x hx⟩), ⟨⟨x, hx⟩, rfl⟩, by simp⟩

/-- The internal factor of a closed-set split, computed with restricted weights,
is the same number as computed upstairs. -/
theorem prod_restrictClosed_eq (W : Sym2 (V × C) → R) (c : V → C)
    (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (S : Finset V) (h : ∀ x ∈ S, σ x ∈ S)
    [Fintype {x : V // x ∈ S}] [DecidableEq {x : V // x ∈ S}] :
    (∏ e ∈ edges (restrictClosed σ hσ S h),
        weightOn W S (Sym2.map (paint (colouringOn c S)) e))
      = ∏ e ∈ S.image (fun x => s(x, σ x)), W (Sym2.map (paint c) e) := by
  rw [← edges_restrictClosed σ hσ S h,
    Finset.prod_image (fun x _ y _ hxy => Sym2.map.injective Subtype.val_injective hxy)]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  unfold weightOn
  congr 1
  rw [Sym2.map_map, Sym2.map_map]
  rfl

/-- Weights carried over to the complement of a set. -/
def weightOff (W : Sym2 (V × C) → R) (S : Finset V) :
    Sym2 ({x : V // x ∉ S} × C) → R :=
  fun e => W (Sym2.map (Prod.map Subtype.val id) e)

/-- A colouring carried over to the complement of a set. -/
def colouringOff (c : V → C) (S : Finset V) : {x : V // x ∉ S} → C := fun x => c x.1

/-- The edges of a complement restriction, mapped back up, are the matching's
edges off the set. -/
theorem edges_restrictClosedCompl (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (S : Finset V)
    (h : ∀ x ∈ S, σ x ∈ S)
    [Fintype {x : V // x ∉ S}] [DecidableEq {x : V // x ∉ S}] :
    (edges (restrictClosedCompl σ hσ S h)).image (Sym2.map Subtype.val)
      = (Finset.univ \ S).image (fun x => s(x, σ x)) := by
  ext e
  simp only [edges, Finset.mem_image, Finset.mem_univ, true_and, restrictClosedCompl,
    Equiv.coe_fn_mk, Finset.mem_sdiff]
  constructor
  · rintro ⟨f, ⟨x, rfl⟩, rfl⟩
    exact ⟨x.1, x.2, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨s(⟨x, hx⟩, ⟨σ x, compl_closed_of_closed hσ h hx⟩), ⟨⟨x, hx⟩, rfl⟩, by simp⟩

/-- The outside factor computed with complement weights is the same number as
computed upstairs. -/
theorem prod_restrictClosedCompl_eq (W : Sym2 (V × C) → R) (c : V → C)
    (σ : Equiv.Perm V) (hσ : σ ∈ pairings V) (S : Finset V) (h : ∀ x ∈ S, σ x ∈ S)
    [Fintype {x : V // x ∉ S}] [DecidableEq {x : V // x ∉ S}] :
    (∏ e ∈ edges (restrictClosedCompl σ hσ S h),
        weightOff W S (Sym2.map (paint (colouringOff c S)) e))
      = ∏ e ∈ (Finset.univ \ S).image (fun x => s(x, σ x)), W (Sym2.map (paint c) e) := by
  rw [← edges_restrictClosedCompl σ hσ S h,
    Finset.prod_image (fun x _ y _ hxy => Sym2.map.injective Subtype.val_injective hxy)]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  unfold weightOff
  congr 1
  rw [Sym2.map_map, Sym2.map_map]
  rfl

/-- **The composition law.**  Summing the weight products of all matchings that
keep a set to itself gives the product of the two sides' amplitudes.  A fragment
may therefore be replaced by its boundary signature, across a separator of any
size. -/
theorem sum_closed_eq_mul (W : Sym2 (V × C) → R) (c : V → C) (S : Finset V)
    [Fintype {x : V // x ∈ S}] [DecidableEq {x : V // x ∈ S}]
    [Fintype {x : V // x ∉ S}] [DecidableEq {x : V // x ∉ S}] :
    (∑ σ ∈ (pairings V).filter (fun σ => ∀ x ∈ S, σ x ∈ S),
        ∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      = (∑ ρ ∈ pairings {x : V // x ∈ S},
          ∏ e ∈ edges ρ, weightOn W S (Sym2.map (paint (colouringOn c S)) e))
        * ∑ τ ∈ pairings {x : V // x ∉ S},
            ∏ e ∈ edges τ, weightOff W S (Sym2.map (paint (colouringOff c S)) e) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij
    (fun σ hσ => (restrictClosed σ (Finset.mem_filter.mp hσ).1 S (Finset.mem_filter.mp hσ).2,
      restrictClosedCompl σ (Finset.mem_filter.mp hσ).1 S (Finset.mem_filter.mp hσ).2))
    (fun σ hσ => Finset.mem_product.mpr
      ⟨restrictClosed_mem_pairings σ (Finset.mem_filter.mp hσ).1 S (Finset.mem_filter.mp hσ).2,
       restrictClosedCompl_mem_pairings σ (Finset.mem_filter.mp hσ).1 S (Finset.mem_filter.mp hσ).2⟩)
    (fun σ hσ τ hτ heq => ?_) (fun p hp => ?_) (fun σ hσ => ?_)
  · ext x
    by_cases hx : x ∈ S
    · exact congrArg Subtype.val (congrFun (congrArg (fun f => (f : Equiv.Perm _).toFun)
        (Prod.mk.injEq _ _ _ _ ▸ heq).1) ⟨x, hx⟩)
    · exact congrArg Subtype.val (congrFun (congrArg (fun f => (f : Equiv.Perm _).toFun)
        (Prod.mk.injEq _ _ _ _ ▸ heq).2) ⟨x, hx⟩)
  · obtain ⟨hρ, hτ⟩ := Finset.mem_product.mp hp
    refine ⟨glue S p.1 p.2, Finset.mem_filter.mpr
      ⟨glue_mem_pairings S p.1 p.2 hρ hτ, glue_closed S p.1 p.2⟩, ?_⟩
    refine Prod.ext ?_ ?_
    · exact restrictClosed_glue S p.1 p.2 (glue_mem_pairings S p.1 p.2 hρ hτ)
    · ext x
      show glue S p.1 p.2 x.1 = (p.2 x).1
      rw [glue_apply_not_mem S p.1 p.2 x.2]
  · simp only
    rw [prod_edges_split_two W c (Finset.mem_filter.mp hσ).1 S,
      internalSet_eq_of_closed (Finset.mem_filter.mp hσ).2,
      prod_restrictClosed_eq W c σ (Finset.mem_filter.mp hσ).1 S (Finset.mem_filter.mp hσ).2,
      prod_restrictClosedCompl_eq W c σ (Finset.mem_filter.mp hσ).1 S (Finset.mem_filter.mp hσ).2]

/-- **Fragment collapse.**  If every matching that sends a vertex of `S` across
the boundary carries a zero-weight edge, the amplitude is exactly the product of
the two sides' amplitudes.  This is the set-level replacement for the forced-edge
condition, and it applies at a separator of any size. -/
theorem amplitude_eq_mul_of_boundary_vanishes (W : Sym2 (V × C) → R) (c : V → C)
    (S : Finset V)
    [Fintype {x : V // x ∈ S}] [DecidableEq {x : V // x ∈ S}]
    [Fintype {x : V // x ∉ S}] [DecidableEq {x : V // x ∉ S}]
    (h : ∀ σ ∈ pairings V, (∃ x ∈ S, σ x ∉ S) →
      ∃ e ∈ edges σ, W (Sym2.map (paint c) e) = 0) :
    amplitude W c
      = (∑ ρ ∈ pairings {x : V // x ∈ S},
          ∏ e ∈ edges ρ, weightOn W S (Sym2.map (paint (colouringOn c S)) e))
        * ∑ τ ∈ pairings {x : V // x ∉ S},
            ∏ e ∈ edges τ, weightOff W S (Sym2.map (paint (colouringOff c S)) e) := by
  rw [← sum_closed_eq_mul W c S]
  unfold amplitude
  rw [← Finset.sum_filter_add_sum_filter_not (pairings V) (fun σ => ∀ x ∈ S, σ x ∈ S)]
  have hzero : (∑ σ ∈ (pairings V).filter (fun σ => ¬ ∀ x ∈ S, σ x ∈ S),
      ∏ e ∈ edges σ, W (Sym2.map (paint c) e)) = 0 := by
    refine Finset.sum_eq_zero (fun σ hσ => ?_)
    rw [Finset.mem_filter] at hσ
    obtain ⟨e, he, hz⟩ := h σ hσ.1 (by
      by_contra hc
      push Not at hc
      exact hσ.2 hc)
    exact Finset.prod_eq_zero he hz
  rw [hzero, add_zero]

/-- The composition law, stated with amplitudes on both sides. -/
theorem sum_closed_eq_amplitude_mul (W : Sym2 (V × C) → R) (c : V → C) (S : Finset V)
    [Fintype {x : V // x ∈ S}] [DecidableEq {x : V // x ∈ S}]
    [Fintype {x : V // x ∉ S}] [DecidableEq {x : V // x ∉ S}] :
    (∑ σ ∈ (pairings V).filter (fun σ => ∀ x ∈ S, σ x ∈ S),
        ∏ e ∈ edges σ, W (Sym2.map (paint c) e))
      = amplitude (weightOn W S) (colouringOn c S)
        * amplitude (weightOff W S) (colouringOff c S) :=
  sum_closed_eq_mul W c S

/-- **Fragment collapse, with amplitudes.**  Under the boundary-vanishing
condition the amplitude factors as the product of the two sides' amplitudes. -/
theorem amplitude_eq_amplitude_mul (W : Sym2 (V × C) → R) (c : V → C) (S : Finset V)
    [Fintype {x : V // x ∈ S}] [DecidableEq {x : V // x ∈ S}]
    [Fintype {x : V // x ∉ S}] [DecidableEq {x : V // x ∉ S}]
    (h : ∀ σ ∈ pairings V, (∃ x ∈ S, σ x ∉ S) →
      ∃ e ∈ edges σ, W (Sym2.map (paint c) e) = 0) :
    amplitude W c
      = amplitude (weightOn W S) (colouringOn c S)
        * amplitude (weightOff W S) (colouringOff c S) :=
  amplitude_eq_mul_of_boundary_vanishes W c S h

/-- **The fragment descent step.**  If the boundary vanishing holds at every
colouring and the outside amplitude never vanishes, a GHZ configuration
restricts to a GHZ configuration on the fragment.  This is descent across a
separator of any size, replacing the two-vertex step whose forcedness condition
only low connectivity can supply. -/
theorem fragment_descent [NoZeroDivisors R] [Nonempty C] (W : Sym2 (V × C) → R)
    (S : Finset V)
    [Fintype {x : V // x ∈ S}] [DecidableEq {x : V // x ∈ S}]
    [Fintype {x : V // x ∉ S}] [DecidableEq {x : V // x ∉ S}]
    (hb : ∀ c : V → C, ∀ σ ∈ pairings V, (∃ x ∈ S, σ x ∉ S) →
      ∃ e ∈ edges σ, W (Sym2.map (paint c) e) = 0)
    (hout : ∀ c : V → C, amplitude (weightOff W S) (colouringOff c S) ≠ 0)
    (hmono : ∀ k : C, amplitude W (const (V := V) k) ≠ 0)
    (hmix : ∀ c : V → C, ¬ Monochromatic c → amplitude W c = 0) :
    (∀ k : C, amplitude (weightOn W S) (colouringOn (const (V := V) k) S) ≠ 0) ∧
      (∀ c : V → C, ¬ Monochromatic c →
        amplitude (weightOn W S) (colouringOn c S) = 0) := by
  constructor
  · intro k hzero
    refine hmono k ?_
    rw [amplitude_eq_amplitude_mul W _ S (hb _), hzero, zero_mul]
  · intro c hc
    have := hmix c hc
    rw [amplitude_eq_amplitude_mul W c S (hb c)] at this
    exact (mul_eq_zero.mp this).resolve_right (hout c)

/-! ### The reach of factorisation

`fragment_descent` needs no perfect matching of the nonvanishing-weight graph to
cross the fragment's boundary.  The characterisation below says what that
demands: every boundary-crossing edge must lie in no perfect matching at all.

In a graph where every edge lies in some perfect matching — which includes every
sufficiently connected graph carrying one — that forces the fragment to have no
boundary edges, so it is a union of connected components and the factorisation is
trivial.  An exhaustive search over all supports of the six-vertex complete graph
found no support of vertex connectivity three or more, out of 1768 candidates
reaching connectivity five, admitting the condition on any even fragment.

Both descent steps in this file therefore reach only vertex connectivity at most
two, which is the regime already settled in the literature.  They are correct and
their hypotheses are exactly stated; what is absent is instances above that
threshold.  A proof of the general conjecture will not come from factorising the
amplitude across a boundary.
-/

omit [Fintype V] in
/-- **Keeping a set is exactly using no crossing edge.**  A matching keeps `S` to
itself precisely when it pairs no vertex of `S` with a vertex outside it. -/
theorem closed_iff_no_crossing_edge (S : Finset V) (σ : Equiv.Perm V) :
    (∀ x ∈ S, σ x ∈ S) ↔ ¬ ∃ x ∈ S, ∃ y ∉ S, σ x = y := by
  constructor
  · rintro h ⟨x, hx, y, hy, hxy⟩
    exact hy (hxy ▸ h x hx)
  · intro h x hx
    by_contra hc
    exact h ⟨x, hx, σ x, hc, rfl⟩

/-- Boundary vanishing for a whole family of matchings, in the same form. -/
theorem boundary_vanishing_iff (S : Finset V) :
    (∀ σ ∈ pairings V, ∀ x ∈ S, σ x ∈ S)
      ↔ ∀ σ ∈ pairings V, ¬ ∃ x ∈ S, ∃ y ∉ S, σ x = y :=
  ⟨fun h σ hσ => (closed_iff_no_crossing_edge S σ).mp (h σ hσ),
   fun h σ hσ => (closed_iff_no_crossing_edge S σ).mpr (h σ hσ)⟩

/-! ### Alternating-cycle exchange

Factorisation across a boundary is out of reach above connectivity two, so the
surviving mechanism acts on the skeleton instead: given two matchings, mixing
them on a region closed under both produces a further matching.  The regions
closed under both are exactly the unions of alternating cycles, so this is the
exchange operation, and it stays inside the matchings of the same vertex set
rather than splitting them across a boundary.
-/

/-- Mix two matchings: follow `σ` inside `A` and `τ` outside it. -/
def mix (f g : V → V) (A : Finset V) : V → V :=
  fun x => if x ∈ A then f x else g x

/-- **Exchange.**  On a region closed under both matchings, mixing them gives a
perfect matching again.  Taking `A` to be a union of alternating cycles of `σ`
and `τ` recovers the classical cycle-exchange operation. -/
theorem mix_mem_pairings {σ τ : Equiv.Perm V} (hσ : σ ∈ pairings V)
    (hτ : τ ∈ pairings V) (A : Finset V)
    (hσA : ∀ x ∈ A, σ x ∈ A) (hτA : ∀ x, x ∉ A → τ x ∉ A) :
    ∃ π ∈ pairings V, ∀ x, π x = mix σ τ A x := by
  obtain ⟨hσi, hσn⟩ := mem_pairings_iff.mp hσ
  obtain ⟨hτi, hτn⟩ := mem_pairings_iff.mp hτ
  have hinv : ∀ x, mix σ τ A (mix σ τ A x) = x := by
    intro x
    by_cases h : x ∈ A
    · simp only [mix, if_pos h, if_pos (hσA x h), hσi]
    · simp only [mix, if_neg h, if_neg (hτA x h), hτi]
  refine ⟨⟨mix σ τ A, mix σ τ A, hinv, hinv⟩, ?_, fun _ => rfl⟩
  refine mem_pairings_iff.mpr ⟨hinv, fun x hx => ?_⟩
  by_cases h : x ∈ A
  · exact hσn x (by simpa [mix, if_pos h] using hx)
  · exact hτn x (by simpa [mix, if_neg h] using hx)

/-- The mixture of two matchings on a region closed under both, as a
permutation. -/
def mixPerm {σ τ : Equiv.Perm V} (hσ : σ ∈ pairings V) (hτ : τ ∈ pairings V)
    (A : Finset V) (hσA : ∀ x ∈ A, σ x ∈ A) (hτA : ∀ x, x ∉ A → τ x ∉ A) :
    Equiv.Perm V :=
  ⟨mix σ τ A, mix σ τ A,
    fun x => by
      by_cases h : x ∈ A
      · simp only [mix, if_pos h, if_pos (hσA x h), (mem_pairings_iff.mp hσ).1]
      · simp only [mix, if_neg h, if_neg (hτA x h), (mem_pairings_iff.mp hτ).1],
    fun x => by
      by_cases h : x ∈ A
      · simp only [mix, if_pos h, if_pos (hσA x h), (mem_pairings_iff.mp hσ).1]
      · simp only [mix, if_neg h, if_neg (hτA x h), (mem_pairings_iff.mp hτ).1]⟩

@[simp] theorem mixPerm_apply_mem {σ τ : Equiv.Perm V} (hσ : σ ∈ pairings V)
    (hτ : τ ∈ pairings V) (A : Finset V) (hσA : ∀ x ∈ A, σ x ∈ A)
    (hτA : ∀ x, x ∉ A → τ x ∉ A) {x : V} (h : x ∈ A) :
    mixPerm hσ hτ A hσA hτA x = σ x := by
  simp [mixPerm, mix, if_pos h]

@[simp] theorem mixPerm_apply_not_mem {σ τ : Equiv.Perm V} (hσ : σ ∈ pairings V)
    (hτ : τ ∈ pairings V) (A : Finset V) (hσA : ∀ x ∈ A, σ x ∈ A)
    (hτA : ∀ x, x ∉ A → τ x ∉ A) {x : V} (h : x ∉ A) :
    mixPerm hσ hτ A hσA hτA x = τ x := by
  simp [mixPerm, mix, if_neg h]

/-- **The exchange identity.**  A mixture's weight product is the first
matching's product inside the region times the second's outside it.  Two
matchings related by an alternating-cycle swap therefore have weight products
differing only along the swapped cycles. -/
theorem prod_edges_mixPerm (W : Sym2 (V × C) → R) (c : V → C)
    {σ τ : Equiv.Perm V} (hσ : σ ∈ pairings V) (hτ : τ ∈ pairings V)
    (A : Finset V) (hσA : ∀ x ∈ A, σ x ∈ A) (hτA : ∀ x, x ∉ A → τ x ∉ A) :
    (∏ e ∈ edges (mixPerm hσ hτ A hσA hτA), W (Sym2.map (paint c) e))
      = (∏ e ∈ A.image (fun x => s(x, σ x)), W (Sym2.map (paint c) e))
        * ∏ e ∈ (Finset.univ \ A).image (fun x => s(x, τ x)), W (Sym2.map (paint c) e) := by
  set π := mixPerm hσ hτ A hσA hτA with hπ
  have hclosed : ∀ x ∈ A, π x ∈ A := by
    intro x hx; rw [hπ, mixPerm_apply_mem hσ hτ A hσA hτA hx]; exact hσA x hx
  have hin : internalSet π A = A := internalSet_eq_of_closed hclosed
  have hmem : π ∈ pairings V := by
    obtain ⟨p, hp, heq⟩ := mix_mem_pairings hσ hτ A hσA hτA
    have : p = π := Equiv.ext (fun x => by rw [heq]; rfl)
    exact this ▸ hp
  rw [prod_edges_split_two W c hmem A, hin]
  congr 1
  · exact Finset.prod_congr (by
      refine Finset.image_congr (fun x hx => ?_)
      rw [hπ, mixPerm_apply_mem hσ hτ A hσA hτA hx]) (fun _ _ => rfl)
  · refine Finset.prod_congr (Finset.image_congr (fun x hx => ?_)) (fun _ _ => rfl)
    rw [hπ, mixPerm_apply_not_mem hσ hτ A hσA hτA (Finset.mem_sdiff.mp hx).2]

/-- **Exchange preserves nonvanishing.**  If two matchings have all their edge
weights nonzero at a colouring, so does every mixture of them.  The surviving
matchings at a colouring are therefore closed under alternating-cycle exchange.

This is why the support abstraction is weak: survivors come in exchange-closed
families, so a colouring with two survivors generally has many, and the only
support-level obstruction — that a vanishing amplitude cannot have exactly one
survivor — is rarely triggered. -/
theorem mixPerm_edges_ne_zero (W : Sym2 (V × C) → R) (c : V → C)
    {σ τ : Equiv.Perm V} (hσ : σ ∈ pairings V) (hτ : τ ∈ pairings V)
    (A : Finset V) (hσA : ∀ x ∈ A, σ x ∈ A) (hτA : ∀ x, x ∉ A → τ x ∉ A)
    (hσnz : ∀ e ∈ edges σ, W (Sym2.map (paint c) e) ≠ 0)
    (hτnz : ∀ e ∈ edges τ, W (Sym2.map (paint c) e) ≠ 0) :
    ∀ e ∈ edges (mixPerm hσ hτ A hσA hτA), W (Sym2.map (paint c) e) ≠ 0 := by
  intro e he
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
  by_cases hx : x ∈ A
  · rw [mixPerm_apply_mem hσ hτ A hσA hτA hx]
    exact hσnz _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  · rw [mixPerm_apply_not_mem hσ hτ A hσA hτA hx]
    exact hτnz _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)

omit [Fintype V] in
/-- **Exchange is reversible.**  The two mixtures of `σ` and `τ` along a region
recombine, along the same region, to `σ` itself; symmetrically for `τ`.  So
exchange pairs matchings up rather than losing information, which is what a
pairing argument on the amplitude sum requires. -/
theorem mix_mix (σ τ : V → V) (A : Finset V) :
    mix (mix σ τ A) (mix τ σ A) A = σ := by
  funext x
  by_cases h : x ∈ A <;> simp [mix, h]

omit [Fintype V] in
theorem mix_mix' (σ τ : V → V) (A : Finset V) :
    mix (mix τ σ A) (mix σ τ A) A = τ := by
  funext x
  by_cases h : x ∈ A <;> simp [mix, h]

/-- Mixing along the whole vertex set is the first matching; along none of it,
the second. -/
@[simp] theorem mix_univ (σ τ : V → V) : mix σ τ Finset.univ = σ := by
  funext x; simp [mix]

omit [Fintype V] in
@[simp] theorem mix_empty (σ τ : V → V) : mix σ τ ∅ = τ := by
  funext x; simp [mix]

/-- If a matching keeps the complement of `A` to itself, it keeps `A` too. -/
theorem closed_of_compl_closed {τ : Equiv.Perm V} (hτ : τ ∈ pairings V) {A : Finset V}
    (hτA : ∀ x, x ∉ A → τ x ∉ A) : ∀ x ∈ A, τ x ∈ A := by
  intro x hx
  by_contra hc
  have := hτA _ hc
  rw [(mem_pairings_iff.mp hτ).1 x] at this
  exact this hx

/-- **Exchange preserves the product of a pair.**  The weight products of the two
mixtures of `σ` and `τ` along a region multiply to the same value as the weight
products of `σ` and `τ` themselves.

This is the exchange constraint in its cleanest form: a swap redistributes weight
between the two matchings of a pair without changing their product.  Unlike the
factorisation identities it never splits the vertex set, so it is untouched by the
connectivity ceiling that confines those to separators of size at most two. -/
theorem prod_mixPerm_mul_prod_mixPerm (W : Sym2 (V × C) → R) (c : V → C)
    {σ τ : Equiv.Perm V} (hσ : σ ∈ pairings V) (hτ : τ ∈ pairings V)
    (A : Finset V) (hσA : ∀ x ∈ A, σ x ∈ A) (hτA : ∀ x, x ∉ A → τ x ∉ A)
    (hσA' : ∀ x, x ∉ A → σ x ∉ A) (hτA' : ∀ x ∈ A, τ x ∈ A) :
    (∏ e ∈ edges (mixPerm hσ hτ A hσA hτA), W (Sym2.map (paint c) e))
      * ∏ e ∈ edges (mixPerm hτ hσ A hτA' hσA'), W (Sym2.map (paint c) e)
      = (∏ e ∈ edges σ, W (Sym2.map (paint c) e))
        * ∏ e ∈ edges τ, W (Sym2.map (paint c) e) := by
  rw [prod_edges_mixPerm W c hσ hτ A hσA hτA, prod_edges_mixPerm W c hτ hσ A hτA' hσA',
    prod_edges_split_two W c hσ A, prod_edges_split_two W c hτ A,
    internalSet_eq_of_closed hσA, internalSet_eq_of_closed hτA']
  ring

/-- **A nontrivial exchange produces a third survivor.**  If two matchings both
have all their edge weights nonzero at a colouring, and mixing them along some
region gives neither of them back, then that mixture is a third such matching.

So a colouring with exactly two surviving matchings admits no nontrivial
exchange between them: they must differ by a single alternating cycle, since two
cycles would allow a mixture along one of them to produce a third survivor.  An
exhaustive check at six vertices found 591 such pairs and every one differed by
exactly one cycle. -/
theorem exists_third_survivor (W : Sym2 (V × C) → R) (c : V → C)
    {σ τ : Equiv.Perm V} (hσ : σ ∈ pairings V) (hτ : τ ∈ pairings V)
    (A : Finset V) (hσA : ∀ x ∈ A, σ x ∈ A) (hτA : ∀ x, x ∉ A → τ x ∉ A)
    (hσnz : ∀ e ∈ edges σ, W (Sym2.map (paint c) e) ≠ 0)
    (hτnz : ∀ e ∈ edges τ, W (Sym2.map (paint c) e) ≠ 0)
    (h1 : mixPerm hσ hτ A hσA hτA ≠ σ) (h2 : mixPerm hσ hτ A hσA hτA ≠ τ) :
    ∃ π ∈ pairings V, π ≠ σ ∧ π ≠ τ ∧
      ∀ e ∈ edges π, W (Sym2.map (paint c) e) ≠ 0 := by
  refine ⟨mixPerm hσ hτ A hσA hτA, ?_, h1, h2,
    mixPerm_edges_ne_zero W c hσ hτ A hσA hτA hσnz hτnz⟩
  obtain ⟨p, hp, heq⟩ := mix_mem_pairings hσ hτ A hσA hτA
  have : p = mixPerm hσ hτ A hσA hτA := Equiv.ext (fun x => by rw [heq]; rfl)
  exact this ▸ hp

/-! ### The alternating-cycle constraint

When a colouring's amplitude vanishes and exactly two matchings survive, the two
must agree outside a single alternating cycle.  Their weight products then share
the factor outside that cycle, and the equation forces the two cycle factors to
be negatives of each other.  This is the constraint the equations place on the
skeleton, and it needs no separator.
-/

section Ring
variable {R : Type*} [CommRing R]

/-- **The cycle constraint.**  Two weight products that share a nonzero factor
and sum to zero have their remaining factors negatives of each other. -/
theorem cycle_factor_eq_neg [NoZeroDivisors R] {x y z : R} (hy : y ≠ 0)
    (h : x * y + z * y = 0) : x = -z := by
  have hsum : (x + z) * y = 0 := by linear_combination h
  rcases mul_eq_zero.mp hsum with h' | h'
  · exact eq_neg_of_add_eq_zero_left h'
  · exact absurd h' hy

end Ring

/-! ### Expansion along a vertex

Every perfect matching pairs a chosen vertex with exactly one other, so the
amplitude splits into one group per partner.  This is the analogue of Laplace
expansion for the matching sum, and unlike the boundary decompositions it needs
no hypothesis whatsoever: it holds at every support density, including the full
support where every matching survives every colouring and no support-level
structure exists.
-/

/-- **Expansion along a vertex.**  Grouping matchings by the partner of `u`
decomposes the amplitude into one term per partner, each carrying that edge's
weight. -/
theorem amplitude_expand_vertex (W : Sym2 (V × C) → R) (c : V → C) (u : V) :
    amplitude W c
      = ∑ v ∈ Finset.univ,
          ∑ σ ∈ (pairings V).filter (fun σ => σ u = v),
            ∏ e ∈ edges σ, W (Sym2.map (paint c) e) := by
  unfold amplitude
  exact (Finset.sum_fiberwise_of_maps_to (fun σ _ => Finset.mem_univ (σ u)) _).symm

/-- Each term of the expansion carries the weight of the edge joining `u` to that
partner. -/
theorem amplitude_expand_vertex_factor (W : Sym2 (V × C) → R) (c : V → C) (u : V) :
    amplitude W c
      = ∑ v ∈ Finset.univ,
          W (Sym2.map (paint c) s(u, v)) *
            ∑ σ ∈ (pairings V).filter (fun σ => σ u = v),
              ∏ e ∈ (edges σ).erase s(u, v), W (Sym2.map (paint c) e) := by
  rw [amplitude_expand_vertex W c u]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [Finset.mem_filter] at hσ
  exact prod_edges_factor W c hσ.1 hσ.2

/-- The matchings whose every edge weight is nonzero at a colouring: the
survivors. -/
def survivors (W : Sym2 (V × C) → R) (c : V → C) : Set (Equiv.Perm V) :=
  {σ | σ ∈ pairings V ∧ ∀ e ∈ edges σ, W (Sym2.map (paint c) e) ≠ 0}

/-- **The survivor set is closed under alternating-cycle exchange.**  Mixing two
survivors along any region closed under both yields a survivor.

The consequence is that any pair of survivors at alternating-cycle distance two
or more would let a mixture escape the set and force an extra survivor.

A caution about testing this at six vertices: it cannot be tested there.  An
alternating cycle is even and of length at least four, and `4 + 4 > 6`, so *any*
two perfect matchings of `K6` differ by exactly one cycle — all 105 pairs, 45 of
length four and 60 of length six.  Measurements at six vertices showing survivor
pairs to be single-cycle are therefore forced by the vertex count and confirm
nothing about exchange.  The first vertex count where the statement has content
is eight. -/
theorem survivors_closed_under_exchange (W : Sym2 (V × C) → R) (c : V → C)
    {σ τ : Equiv.Perm V} (hσ : σ ∈ survivors W c) (hτ : τ ∈ survivors W c)
    (A : Finset V) (hσA : ∀ x ∈ A, σ x ∈ A) (hτA : ∀ x, x ∉ A → τ x ∉ A) :
    mixPerm hσ.1 hτ.1 A hσA hτA ∈ survivors W c := by
  refine ⟨?_, mixPerm_edges_ne_zero W c hσ.1 hτ.1 A hσA hτA hσ.2 hτ.2⟩
  obtain ⟨p, hp, heq⟩ := mix_mem_pairings hσ.1 hτ.1 A hσA hτA
  have : p = mixPerm hσ.1 hτ.1 A hσA hτA := Equiv.ext (fun x => by rw [heq]; rfl)
  exact this ▸ hp

/-- **The sharp collapse condition.**  The obstructing sum vanishes as soon as
every matching avoiding `{u, v}` carries at least one zero-weight edge.  This is
exactly what a descent step needs, and it is weaker than requiring the vanishing
edge to sit at `u`. -/
theorem amplitude_of_avoiding_has_zero (W : Sym2 (V × C) → R) (c : V → C) (u v : V)
    (h : ∀ σ ∈ pairings V, σ u ≠ v →
      ∃ e ∈ edges σ, W (Sym2.map (paint c) e) = 0) :
    amplitude W c
      = W (Sym2.map (paint c) s(u, v)) *
          ∑ σ ∈ (pairings V).filter (fun σ => σ u = v),
            ∏ e ∈ (edges σ).erase s(u, v), W (Sym2.map (paint c) e) := by
  rw [amplitude_split_factor W c u v]
  have : (∑ σ ∈ (pairings V).filter (fun σ => ¬ σ u = v),
            ∏ e ∈ edges σ, W (Sym2.map (paint c) e)) = 0 := by
    refine Finset.sum_eq_zero (fun σ hσ => ?_)
    rw [Finset.mem_filter] at hσ
    obtain ⟨e, he, hz⟩ := h σ hσ.1 hσ.2
    exact Finset.prod_eq_zero he hz
  rw [this, add_zero]

/-- **Pendant reduction.**  If every edge at `u` other than `{u, v}` carries
weight zero under the colouring `c`, then every matching avoiding `{u, v}` must
match `u` through a zero weight, so the obstructing sum vanishes and the
amplitude collapses to a single edge weight times an amplitude on the remaining
vertices.  This is the mechanism behind every separator reduction, stated for an
arbitrary vertex type. -/
theorem amplitude_of_pendant (W : Sym2 (V × C) → R) (c : V → C) (u v : V)
    (h : ∀ w, w ≠ v → W (Sym2.map (paint c) s(u, w)) = 0) :
    amplitude W c
      = W (Sym2.map (paint c) s(u, v)) *
          ∑ σ ∈ (pairings V).filter (fun σ => σ u = v),
            ∏ e ∈ (edges σ).erase s(u, v), W (Sym2.map (paint c) e) := by
  refine amplitude_of_avoiding_has_zero W c u v (fun σ hσ hne => ?_)
  exact ⟨s(u, σ u), (mem_edges_iff hσ u (σ u)).mpr rfl, h (σ u) hne⟩


/-! ### The involution principle

If the perfect matchings can be paired off by a fixed-point-free involution that
reverses the sign of the edge product, the amplitude vanishes identically.  This
is the mechanism behind every cancellation argument in the subject: one exhibits
the pairing, and the sum dies without a single one of its terms being evaluated.

It is stated over an arbitrary commutative ring and an arbitrary vertex set, so
it applies at every vertex count the conjecture ranges over.
-/

section SignReversing

variable {S : Type*} [CommRing S]

/-- **Partial cancellation.**  A sign-reversing involution defined only on part of
the matchings kills exactly that part, leaving the amplitude equal to the sum over
what is left.  This is how cancellation is used in practice: a family of matchings
pairs off and drops out, and the argument continues with the survivors. -/
theorem amplitude_eq_sum_sdiff_of_sign_reversing_on (W : Sym2 (V × C) → S) (c : V → C)
    (T : Finset (Equiv.Perm V)) (hT : T ⊆ pairings V)
    (Φ : Equiv.Perm V → Equiv.Perm V)
    (hmem : ∀ σ ∈ T, Φ σ ∈ T)
    (hinv : ∀ σ ∈ T, Φ (Φ σ) = σ)
    (hne : ∀ σ ∈ T, Φ σ ≠ σ)
    (hsign : ∀ σ ∈ T,
        (∏ e ∈ edges (Φ σ), W (Sym2.map (paint c) e))
          = -∏ e ∈ edges σ, W (Sym2.map (paint c) e)) :
    amplitude W c = ∑ σ ∈ pairings V \ T, ∏ e ∈ edges σ, W (Sym2.map (paint c) e) := by
  have hzero : ∑ σ ∈ T, ∏ e ∈ edges σ, W (Sym2.map (paint c) e) = 0 := by
    refine Finset.sum_involution (fun σ _ => Φ σ) (fun σ hσ => ?_)
      (fun σ hσ _ => hne σ hσ) (fun σ hσ => hmem σ hσ) (fun σ hσ => hinv σ hσ)
    rw [hsign σ hσ]
    ring
  have hsplit :=
    Finset.sum_sdiff (f := fun σ => ∏ e ∈ edges σ, W (Sym2.map (paint c) e)) hT
  simp only [amplitude]
  rw [← hsplit, hzero, add_zero]

/-- **The involution principle for the amplitude.**  A fixed-point-free
involution on the perfect matchings which reverses the sign of the edge product
forces the amplitude to zero.  Nothing about the weights is used beyond the
pairing itself, and no term is computed.

The contrapositive is the shape an impossibility argument takes: show the
equations force the amplitude to be a nonzero constant, and no such pairing can
exist. -/
theorem amplitude_eq_zero_of_sign_reversing (W : Sym2 (V × C) → S) (c : V → C)
    (Φ : Equiv.Perm V → Equiv.Perm V)
    (hmem : ∀ σ ∈ pairings V, Φ σ ∈ pairings V)
    (hinv : ∀ σ ∈ pairings V, Φ (Φ σ) = σ)
    (hne : ∀ σ ∈ pairings V, Φ σ ≠ σ)
    (hsign : ∀ σ ∈ pairings V,
        (∏ e ∈ edges (Φ σ), W (Sym2.map (paint c) e))
          = -∏ e ∈ edges σ, W (Sym2.map (paint c) e)) :
    amplitude W c = 0 := by
  rw [amplitude_eq_sum_sdiff_of_sign_reversing_on W c (pairings V) (Finset.Subset.refl _) Φ hmem hinv hne hsign,
    Finset.sdiff_self]
  simp

/-- The involution principle read against a nonvanishing requirement.  If the
amplitude of a colouring is required to be nonzero -- as the defining equations
require of the monochromatic colourings -- then the matchings admit no
sign-reversing involution at all. -/
theorem no_sign_reversing_of_amplitude_ne_zero (W : Sym2 (V × C) → S) (c : V → C)
    (h : amplitude W c ≠ 0) (Φ : Equiv.Perm V → Equiv.Perm V)
    (hmem : ∀ σ ∈ pairings V, Φ σ ∈ pairings V)
    (hinv : ∀ σ ∈ pairings V, Φ (Φ σ) = σ)
    (hne : ∀ σ ∈ pairings V, Φ σ ≠ σ) :
    ¬ ∀ σ ∈ pairings V,
        (∏ e ∈ edges (Φ σ), W (Sym2.map (paint c) e))
          = -∏ e ∈ edges σ, W (Sym2.map (paint c) e) :=
  fun hsign => h (amplitude_eq_zero_of_sign_reversing W c Φ hmem hinv hne hsign)

end SignReversing

/-! ### Restricting the number of colours

A solution in many colours restricts to a solution in fewer: keep any injective
selection of colours and read the weights only at those.  Since the conjecture is
about *some* dimension exceeding two being impossible, this collapses the whole
family to the three-colour case, and every later argument may assume three colours
without loss.

The proof is naturality.  Reading the weights through an injection of colours is the
same as recolouring the colouring, so the amplitudes agree; and an injection neither
creates nor destroys monochromacy.
-/

/-- The weights of a system read only at a selected set of colours. -/
def restrictColours (f : C → C') (W : Sym2 (V × C') → R) : Sym2 (V × C) → R :=
  fun e => W (Sym2.map (Prod.map id f) e)

/-- **A solution restricts to fewer colours.**  Selecting colours by any injection
carries a solution to a solution. -/
theorem isGHZ_restrictColours [Nonempty V] {C' : Type*} {f : C → C'}
    (hf : Function.Injective f) (W : Sym2 (V × C') → ℂ)
    (hone : ∀ k : C', amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → C', ¬ Monochromatic c → amplitude W c = 0) :
    (∀ k : C, amplitude (restrictColours f W) (Amplitude.const k) = 1) ∧
      (∀ c : V → C, ¬ Monochromatic c →
        amplitude (restrictColours f W) c = 0) := by
  constructor
  · intro k
    show amplitude (fun e => W (Sym2.map (Prod.map id f) e)) (Amplitude.const k) = 1
    rw [amplitude_comp f W (Amplitude.const k)]
    have : f ∘ (Amplitude.const k : V → C) = Amplitude.const (f k) := rfl
    rw [this]
    exact hone (f k)
  · intro c hc
    show amplitude (fun e => W (Sym2.map (Prod.map id f) e)) c = 0
    rw [amplitude_comp f W c]
    exact hzero (f ∘ c) (fun h => hc ((monochromatic_comp_iff hf c).mp h))

end Amplitude
