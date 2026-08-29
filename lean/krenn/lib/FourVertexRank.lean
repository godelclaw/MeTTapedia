import Mathlib
import Amplitude
import MatchingSum
import ColourPerMatching
import Mettapedia.Combinatorics.Matching.BlockRank

/-!
# What the equations force on the weight blocks

The defining equations are usually read colouring by colouring.  Read instead as
statements about the *blocks* — the matrix a pair of sites carries, indexed by the
colours at its two ends — they say something sharper: certain blocks cannot have full
rank.

On four vertices the mechanism is exact and visible.  Fix the colours at two sites so
that they already disagree; the colouring is non-constant whatever the other two
sites wear, so the amplitude vanishes identically in them.  As a matrix in those two
free colours, the amplitude is the block of the complementary pair scaled by one
entry, plus one rank-one term for each way of splitting the free sites between the
fixed ones.  With four vertices there are exactly two such ways, so the complementary
block is pinned to a span of two vectors as soon as the scaling entry is nonzero.

This is a constraint derived from the equations rather than observed on examples, and
it is the first step toward asking whether the solution variety meets the locus where
a block degenerates.
-/

namespace FourVertexRank

open Amplitude
open MatchingBlockRank

/-- The three ways to pair four sites. -/
theorem pairings_four : pairings (Fin 4) =
    {Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
      Equiv.swap 0 3 * Equiv.swap 1 2} := by decide

/-- The amplitude on four sites, written out over its three matchings. -/
theorem amplitude_four (W : Sym2 (Fin 4 × Fin 3) → ℂ) (c : Fin 4 → Fin 3) :
    amplitude W c
      = W s((0, c 0), (1, c 1)) * W s((2, c 2), (3, c 3))
        + W s((0, c 0), (2, c 2)) * W s((1, c 1), (3, c 3))
        + W s((0, c 0), (3, c 3)) * W s((1, c 1), (2, c 2)) := by
  rw [amplitude, pairings_four]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have e₁ : edges (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) = {s(0, 1), s(2, 3)} := by decide
  have e₂ : edges (Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3) = {s(0, 2), s(1, 3)} := by decide
  have e₃ : edges (Equiv.swap (0 : Fin 4) 3 * Equiv.swap 1 2) = {s(0, 3), s(1, 2)} := by decide
  rw [e₁, e₂, e₃]
  rw [Finset.prod_insert (by decide), Finset.prod_singleton,
    Finset.prod_insert (by decide), Finset.prod_singleton,
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [Sym2.map_pair_eq, paint]
  ring


/-- **A nonzero block entry pins the complementary block to a plane.**

Fix colours at the first two sites that already disagree.  Whatever the other two
sites wear, the colouring is non-constant, so the amplitude vanishes; and the
amplitude, read as a matrix in those two free colours, is the complementary block
scaled by the chosen entry plus exactly two rank-one terms.  Dividing by the entry
expresses every row of the complementary block in the same two vectors.

The complementary block therefore has rank at most two, so with three colours it is
singular.  This is forced by the defining equations alone. -/
theorem block_factors (W : Sym2 (Fin 4 × Fin 3) → ℂ) (hW : KrennGu.IsGHZ W)
    {a b : Fin 3} (hab : a ≠ b) (hP : W s((0, a), (1, b)) ≠ 0) (d e : Fin 3) :
    W s((2, d), (3, e))
      = (-W s((0, a), (2, d)) / W s((0, a), (1, b))) * W s((1, b), (3, e))
        + (-W s((1, b), (2, d)) / W s((0, a), (1, b))) * W s((0, a), (3, e)) := by
  have hc : ¬ Monochromatic (![a, b, d, e] : Fin 4 → Fin 3) := by
    rintro ⟨k, hk⟩
    exact hab ((hk 0).trans (hk 1).symm)
  have h0 := hW.2 _ hc
  rw [amplitude_four] at h0
  have c0 : (![a, b, d, e] : Fin 4 → Fin 3) 0 = a := rfl
  have c1 : (![a, b, d, e] : Fin 4 → Fin 3) 1 = b := rfl
  have c2 : (![a, b, d, e] : Fin 4 → Fin 3) 2 = d := rfl
  have c3 : (![a, b, d, e] : Fin 4 → Fin 3) 3 = e := rfl
  rw [c0, c1, c2, c3] at h0
  field_simp
  linear_combination h0

/-- The rows of the complementary block lie in the span of two fixed vectors: the
plane is the same for every row, being cut out by the two sites whose colours were
fixed. -/
theorem block_rows_in_plane (W : Sym2 (Fin 4 × Fin 3) → ℂ) (hW : KrennGu.IsGHZ W)
    {a b : Fin 3} (hab : a ≠ b) (hP : W s((0, a), (1, b)) ≠ 0) :
    ∃ α β : Fin 3 → ℂ, ∀ d e : Fin 3,
      W s((2, d), (3, e))
        = α d * W s((1, b), (3, e)) + β d * W s((0, a), (3, e)) :=
  ⟨fun d => -W s((0, a), (2, d)) / W s((0, a), (1, b)),
   fun d => -W s((1, b), (2, d)) / W s((0, a), (1, b)),
   fun d e => block_factors W hW hab hP d e⟩






/-! ### The dichotomy

Either some colouring non-constant away from two sites leaves the remaining sites a
nonvanishing matching sum — and then the block those two sites carry degenerates, as
soon as they reach few enough partners — or every such colouring leaves a vanishing
one, which is exactly the vanishing half of the defining conditions on two fewer
sites.
-/

section Dichotomy

open Amplitude MatchingSum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A colouring already disagrees somewhere away from two given sites. -/
def NonConstOff (c₀ : V → Fin 3) (p q : V) : Prop :=
  ∃ x y : V, x ≠ p ∧ x ≠ q ∧ y ≠ p ∧ y ≠ q ∧ c₀ x ≠ c₀ y

/-- Painting two sites freely over a colouring that already disagrees elsewhere leaves
a non-constant colouring, so a solution's matching sum vanishes there whatever those
two sites wear. -/
theorem vanish_of_nonConstOff {W : Sym2 (V × Fin 3) → ℂ} (hW : KrennGu.IsGHZ W)
    {c₀ : V → Fin 3} {p q : V} (h : NonConstOff c₀ p q) (α β : Fin 3) :
    pmSum W (paintTwo c₀ p q α β) Finset.univ = 0 := by
  obtain ⟨x, y, hxp, hxq, hyp, hyq, hxy⟩ := h
  rw [pmSum_univ]
  refine hW.2 _ ?_
  rintro ⟨k, hk⟩
  refine hxy ?_
  rw [← paintTwo_other c₀ hxp hxq α β, ← paintTwo_other c₀ hyp hyq α β, hk x, hk y]

/-- **Either a block degenerates, or the equations descend.**

The hypothesis is that, for every colouring, the correction at the two sites is built
from fewer than three rank-one pieces — the statement that they reach few partners in
the support.

The first alternative says the block those sites carry has dependent rows.  The second
says every colouring disagreeing away from them annihilates the matching sum on the
rest, which is the vanishing half of the defining conditions two sites down. -/
theorem block_degenerates_or_descends (W : Sym2 (V × Fin 3) → ℂ) (hW : KrennGu.IsGHZ W)
    {p q : V} (hq : q ∈ (Finset.univ : Finset V).erase p) {m : ℕ} (hm : m < 3)
    (hfew : ∀ c₀ : V → Fin 3, ∃ u v : Fin m → Fin 3 → ℂ, ∀ α β : Fin 3,
      (∑ x ∈ ((Finset.univ : Finset V).erase p).erase q,
        W s((p, α), (x, c₀ x)) *
          ∑ l ∈ (((Finset.univ : Finset V).erase p).erase x).erase q,
            W s((q, β), (l, c₀ l)) *
              pmSum W c₀ (((((Finset.univ : Finset V).erase p).erase x).erase q).erase l))
        = ∑ i, u i α * v i β) :
    (∃ lam : Fin 3 → ℂ, lam ≠ 0 ∧ ∀ β : Fin 3, ∑ α, lam α * W s((p, α), (q, β)) = 0)
      ∨ (∀ c₀ : V → Fin 3, NonConstOff c₀ p q →
          pmSum W c₀ (((Finset.univ : Finset V).erase p).erase q) = 0) := by
  classical
  by_cases h : ∃ c₀ : V → Fin 3, NonConstOff c₀ p q ∧
      pmSum W c₀ (((Finset.univ : Finset V).erase p).erase q) ≠ 0
  · obtain ⟨c₀, hnc, hK⟩ := h
    obtain ⟨u, v, hcorr⟩ := hfew c₀
    exact Or.inl (block_rows_dependent W c₀ (Finset.mem_univ p) hq
      (vanish_of_nonConstOff hW hnc) hK u v (by simpa using hm) hcorr)
  · push_neg at h
    exact Or.inr h


/-- **The dichotomy, with the partner count supplied by the support.**

`T` collects the sites the first of the pair can reach: outside it the whole weight
block vanishes, so those terms contribute nothing whatever the colouring.  When `T`
has fewer members than there are colours — a site of degree at most three, counting
its partner — the hypothesis of the dichotomy is met unconditionally.

So on such a support a solution must either carry a degenerate block at that pair, or
satisfy the vanishing conditions two sites down. -/
theorem degenerates_or_descends_of_few_neighbours (W : Sym2 (V × Fin 3) → ℂ)
    (hW : KrennGu.IsGHZ W) {p q : V} (hq : q ∈ (Finset.univ : Finset V).erase p)
    (T : Finset V) (hT : T ⊆ ((Finset.univ : Finset V).erase p).erase q)
    (hout : ∀ x ∈ ((Finset.univ : Finset V).erase p).erase q, x ∉ T →
      ∀ i j : Fin 3, W s((p, i), (x, j)) = 0)
    (hcard : T.card < 3) :
    (∃ lam : Fin 3 → ℂ, lam ≠ 0 ∧ ∀ β : Fin 3, ∑ α, lam α * W s((p, α), (q, β)) = 0)
      ∨ (∀ c₀ : V → Fin 3, NonConstOff c₀ p q →
          pmSum W c₀ (((Finset.univ : Finset V).erase p).erase q) = 0) :=
  block_degenerates_or_descends W hW hq hcard
    (fun c₀ => few_terms_of_support W c₀ T hT
      (fun x hx hnx α => hout x hx hnx α (c₀ x)))


/-- **Every site has a partner whose removal leaves a live monochromatic sum.**

The vertex equation at a site, read at equal colours, sums to one.  A sum equal to one
cannot have every summand vanish, so some partner contributes: its block entry is
nonzero *and* the monochromatic matching sum on everything else is nonzero.

This is what supplies the second alternative of the dichotomy with the nonvanishing it
needs.  It is proved from the equations, not chosen. -/
theorem exists_partner_live [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (k : Fin 3) (hV : 2 ≤ Fintype.card V) :
    ∃ v ∈ Finset.univ.erase u,
      W s((u, k), (v, k)) ≠ 0 ∧
        pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsum := vertex_equations W hone hzero u k k hV
  rw [if_pos rfl] at hsum
  have hz : (∑ v ∈ Finset.univ.erase u,
      W s((u, k), (v, k)) *
        pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v)) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    rcases eq_or_ne (W s((u, k), (v, k))) 0 with h1 | h1
    · rw [h1, zero_mul]
    · rw [hcon v hv h1, mul_zero]
  rw [hz] at hsum
  exact zero_ne_one hsum


/-- **The second-order coefficient is not always zero.**

The coefficient of the quadratic term is the matching sum over the complement of the
four sites the defect touches.  The equations do not merely fail to make it vanish;
they force it to survive somewhere.

Some partner leaves a live monochromatic sum on the remaining sites, and a live sum has
a live edge at any site of it, so two further sites can be removed and the sum still
does not vanish.  Four sites removed, and the coefficient is nonzero. -/
theorem exists_four_removed_live [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (k : Fin 3) (hV : 2 ≤ Fintype.card V) :
    ∃ v ∈ Finset.univ.erase u,
      ∀ r ∈ (Finset.univ.erase u).erase v,
        ∃ t ∈ ((Finset.univ.erase u).erase v).erase r,
          pmSum W (Amplitude.const k)
              ((((Finset.univ.erase u).erase v).erase r).erase t) ≠ 0 := by
  obtain ⟨v, hv, -, hlive⟩ := exists_partner_live W hone hzero u k hV
  refine ⟨v, hv, fun r hr => ?_⟩
  obtain ⟨t, ht, -, hne⟩ := exists_edge_of_pmSum_ne_zero W (Amplitude.const k) hr hlive
  exact ⟨t, ht, hne⟩


/-- **No vector annihilates all the blocks at a site.**

The vertex equation at a site says that, for each colour, a combination of the blocks'
columns in that colour reproduces the corresponding basis vector.  So those columns span
everything, and only the zero vector kills them all.

The consequence is that a cap built as an outer product can never be flat: its first
factor would have to annihilate every block at the site, hence be zero.  This is why the
four-vertex solution admits no flat cap, and the reason is not peculiar to four
vertices — it is the vertex equation, which every solution satisfies. -/
theorem eq_zero_of_annihilates_site [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (hV : 2 ≤ Fintype.card V) (lam : Fin 3 → ℂ)
    (h : ∀ v ∈ Finset.univ.erase u, ∀ b : Fin 3,
      ∑ j : Fin 3, lam j * W s((u, j), (v, b)) = 0) :
    lam = 0 := by
  classical
  funext k
  have hsum : (∑ j : Fin 3, lam j *
      ∑ v ∈ Finset.univ.erase u, W s((u, j), (v, k)) *
        pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v)) = lam k := by
    have hv : ∀ j : Fin 3, (∑ v ∈ Finset.univ.erase u, W s((u, j), (v, k)) *
        pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v))
        = if j = k then 1 else 0 := fun j => vertex_equations W hone hzero u k j hV
    simp only [hv, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ k lam]
    simp
  have hzero' : (∑ j : Fin 3, lam j *
      ∑ v ∈ Finset.univ.erase u, W s((u, j), (v, k)) *
        pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v)) = 0 := by
    have hdist : ∀ j : Fin 3, lam j *
        (∑ v ∈ Finset.univ.erase u, W s((u, j), (v, k)) *
          pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v))
        = ∑ v ∈ Finset.univ.erase u, lam j * W s((u, j), (v, k)) *
            pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v) := by
      intro j
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    simp only [hdist]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hann := h v hv k
    calc (∑ j : Fin 3, lam j * W s((u, j), (v, k)) *
            pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v))
        = (∑ j : Fin 3, lam j * W s((u, j), (v, k))) *
            pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v) := by
          rw [Finset.sum_mul]
      _ = 0 := by rw [hann, zero_mul]
  rw [← hsum, hzero']
  rfl


/-- Rescaling an annihilator leaves it annihilating: if a nonzero multiple of `lam`
kills a column, so does `lam`. -/
theorem annihilates_of_smul (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (b : Fin 3)
    {lam : Fin 3 → ℂ} {t : ℂ} (ht : t ≠ 0)
    (h : ∑ j : Fin 3, (t * lam j) * W s((u, j), (v, b)) = 0) :
    ∑ j : Fin 3, lam j * W s((u, j), (v, b)) = 0 := by
  have hfac : ∑ j : Fin 3, (t * lam j) * W s((u, j), (v, b))
      = t * ∑ j : Fin 3, lam j * W s((u, j), (v, b)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfac] at h
  exact (mul_eq_zero.mp h).resolve_left ht

/-- **A single direction cannot serve every colouring.**

Suppose the annihilators produced at a site all point the same way — which is what
happens when the block there has rank two, its annihilator being a line — and suppose
that direction kills, for each partner and each colour, the corresponding column.  Then
it kills every block at the site, so it is zero.

The hypothesis is therefore unsustainable: no nonzero direction can do this.  A block of
rank two at a site of low degree would force exactly this situation, so such a block
cannot occur, and the degeneration forced by the dichotomy must go further than rank two.

Four vertices escape because its blocks have rank one: the annihilator is then a plane
rather than a line, the direction is not pinned, and different colourings may use
different ones. -/
theorem no_single_direction [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (hV : 2 ≤ Fintype.card V) (lam : Fin 3 → ℂ) (hlam : lam ≠ 0)
    (h : ∀ v ∈ Finset.univ.erase u, ∀ b : Fin 3, ∃ t : ℂ, t ≠ 0 ∧
      ∑ j : Fin 3, (t * lam j) * W s((u, j), (v, b)) = 0) :
    False := by
  refine hlam (eq_zero_of_annihilates_site W hone hzero u hV lam ?_)
  intro v hv b
  obtain ⟨t, ht, hkill⟩ := h v hv b
  exact annihilates_of_smul W u v b ht hkill


/-- **With rank-one blocks, a nonzero direction must survive at some partner.**

If every block at a site factors — one factor depending on the site's colour, one on the
partner's — then a vector annihilating a block is one orthogonal to that block's first
factor.  Since no nonzero vector annihilates every block, no nonzero vector is orthogonal
to every first factor.

This is what the degeneration has to contend with.  The dichotomy drives blocks at a
low-degree site down to rank one, where they factor; but then the first factors span, and
the annihilator produced at one partner cannot be orthogonal to the factors at the
others.  It must be rescued by the second factor vanishing at the colour the colouring
happens to choose — which is a condition on colourings, not on the weights alone. -/
theorem exists_partner_not_annihilated [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (hV : 2 ≤ Fintype.card V) (a b : V → Fin 3 → ℂ)
    (hfac : ∀ v ∈ Finset.univ.erase u, ∀ j k : Fin 3,
      W s((u, j), (v, k)) = a v j * b v k)
    (lam : Fin 3 → ℂ) (hlam : lam ≠ 0) :
    ∃ v ∈ Finset.univ.erase u, (∑ j : Fin 3, lam j * a v j) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  refine hlam (eq_zero_of_annihilates_site W hone hzero u hV lam ?_)
  intro v hv k
  have hsplit : ∀ j : Fin 3, lam j * W s((u, j), (v, k)) = (lam j * a v j) * b v k := by
    intro j
    rw [hfac v hv j k]
    ring
  calc ∑ j : Fin 3, lam j * W s((u, j), (v, k))
      = ∑ j : Fin 3, (lam j * a v j) * b v k := Finset.sum_congr rfl fun j _ => hsplit j
    _ = (∑ j : Fin 3, lam j * a v j) * b v k := by rw [Finset.sum_mul]
    _ = 0 := by rw [hcon v hv, zero_mul]


/-- **The witnessing colouring is forced onto a zero of a second factor.**

Suppose the blocks at a site factor, a nonzero direction annihilates the first factors
everywhere outside some set of partners, and on that set the annihilator's pairing times
the second factor at the chosen colour vanishes.  Then the colouring sends one of those
partners to a zero of its second factor.

The direction cannot be orthogonal to every first factor, so it survives at some partner;
outside the set it does not, so the survivor is inside; and there the product can only
vanish through the second factor.

This is where the degeneration finally has to be paid for.  It is not a condition on the
weights but on which colours the colouring assigns, and a second factor has only finitely
many zeros to offer. -/
theorem witness_hits_second_factor_zero [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (hV : 2 ≤ Fintype.card V) (a b : V → Fin 3 → ℂ)
    (hfac : ∀ v ∈ Finset.univ.erase u, ∀ j k : Fin 3,
      W s((u, j), (v, k)) = a v j * b v k)
    (lam : Fin 3 → ℂ) (hlam : lam ≠ 0) (c₀ : V → Fin 3) (T : Finset V)
    (hann : ∀ x ∈ T, (∑ j : Fin 3, lam j * a x j) * b x (c₀ x) = 0)
    (hrest : ∀ v ∈ Finset.univ.erase u, v ∉ T → (∑ j : Fin 3, lam j * a v j) = 0) :
    ∃ x ∈ T, b x (c₀ x) = 0 := by
  classical
  obtain ⟨v, hv, hne⟩ :=
    exists_partner_not_annihilated W hone hzero u hV a b hfac lam hlam
  have hvT : v ∈ T := by
    by_contra hvT
    exact hne (hrest v hv hvT)
  exact ⟨v, hvT, (mul_eq_zero.mp (hann v hvT)).resolve_left hne⟩

end Dichotomy


/-! ### Why a simultaneous witness is the wrong thing to look for

The descent alternative would be comfortable if one partner were live for every
colour at once.  It never is, on any solution built by colouring the matchings: an
edge wears one colour, so it can be live for one colour only.

The four-vertex solution is such a solution, and there each colour has exactly one
live partner, the three being distinct.  That is not an accident to be worked around
— four vertices are solvable and must not descend, so every correct descent argument
has to fail there.  A route through a simultaneous witness fails there for the wrong
reason, which is to say it would prove too much.
-/



/-! ### The conditional smaller-solution theorem

The capped amplitude behaves on the remaining sites the way a solution behaves: constant
on constant colourings, vanishing on the rest.  Given the cap identity — which expresses
it as a multiple of the matching sum on those sites plus a defect — absorption folds the
defect into perturbed weights, and what is left is a solution two sites down, up to a
scalar.

Cap existence is not claimed anywhere here; the identity is a hypothesis, so the theorem
is exactly conditional on it.
-/

section SmallerSolution

open Amplitude MatchingSum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The capped amplitude vanishes at any colouring already disagreeing away from the
capped pair, because every amplitude it averages does. -/
theorem capAmp_eq_zero_of_nonConstOff {W : Sym2 (V × Fin 3) → ℂ}
    (hW : KrennGu.IsGHZ W) (C : Fin 3 → Fin 3 → ℂ) {p q : V} {cR : V → Fin 3}
    (h : NonConstOff cR p q) : capAmp W C p q cR = 0 := by
  unfold capAmp
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  have := vanish_of_nonConstOff hW h a b
  rw [pmSum_univ] at this
  rw [show Function.update (Function.update cR p a) q b = paintTwo cR p q a b from rfl,
    this, mul_zero]

/-- **A cap yields a solution two sites down, conditionally.**

The hypothesis `hcap` is the cap identity: the capped amplitude is a nonzero multiple of
the matching sum on the remaining sites, plus a defect whose edges pairwise meet.  Given
it, the matching sum at perturbed weights is the capped amplitude divided by that
multiple — so it is constant on constant colourings and vanishes on the others, which is
what a solution on those sites means.

Nothing here asserts that such a cap exists. -/
theorem smaller_solution_of_cap (W A : Sym2 (V × Fin 3) → ℂ) (C : Fin 3 → Fin 3 → ℂ)
    {p q : V} {R : Finset V} (s : ℂ) (hs : s ≠ 0)
    (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∃ z : V, z ∈ e ∧ z ∈ f)
    (cR : V → Fin 3)
    (hA : ∀ e : Sym2 V, e ∉ E → A (Sym2.map (paint cR) e) = 0)
    (hcap : capAmp W C p q cR
      = s * pmSum W cR R
        + ∑ e ∈ E, A (Sym2.map (paint cR) e) *
            ∑ σ ∈ (pairingsOn R).filter (fun σ => e ∈ R.image (fun x => s(x, σ x))),
              ∏ f ∈ (R.image (fun x => s(x, σ x))).erase e, W (Sym2.map (paint cR) f)) :
    pmSum (fun e => W e + s⁻¹ * A e) cR R = capAmp W C p q cR / s := by
  rw [hcap, absorb_defect_family W A cR E hE hA s hs]
  exact (mul_div_cancel_left₀ _ hs).symm


/-- **The cap identity.**  Capping a solution at a pair of sites gives the contraction
scalar times the matching sum on the remaining sites, plus a correction.

This is not an assumption: it is the block decomposition averaged against the cap, so
it holds for arbitrary weights.  The scalar multiplying the matching sum is exactly the
cap paired against the block of the capped pair, and the correction is the cap paired
against the rank-one pieces. -/
theorem capAmp_split (W : Sym2 (V × Fin 3) → ℂ) (C : Fin 3 → Fin 3 → ℂ)
    {p q : V} (hq : q ∈ (Finset.univ : Finset V).erase p) (cR : V → Fin 3) :
    capAmp W C p q cR
      = (∑ a : Fin 3, ∑ b : Fin 3, C a b * W s((p, a), (q, b)))
          * pmSum W cR (((Finset.univ : Finset V).erase p).erase q)
        + ∑ a : Fin 3, ∑ b : Fin 3, C a b *
            (∑ x ∈ ((Finset.univ : Finset V).erase p).erase q,
              W s((p, a), (x, cR x)) *
                ∑ l ∈ (((Finset.univ : Finset V).erase p).erase x).erase q,
                  W s((q, b), (l, cR l)) *
                    pmSum W cR
                      ((((((Finset.univ : Finset V).erase p).erase x).erase q)).erase l)) := by
  classical
  unfold capAmp
  have key : ∀ a b : Fin 3,
      amplitude W (Function.update (Function.update cR p a) q b)
        = W s((p, a), (q, b)) * pmSum W cR (((Finset.univ : Finset V).erase p).erase q)
          + (∑ x ∈ ((Finset.univ : Finset V).erase p).erase q,
              W s((p, a), (x, cR x)) *
                ∑ l ∈ (((Finset.univ : Finset V).erase p).erase x).erase q,
                  W s((q, b), (l, cR l)) *
                    pmSum W cR
                      ((((((Finset.univ : Finset V).erase p).erase x).erase q)).erase l)) := by
    intro a b
    rw [← pmSum_univ]
    exact block_split W cR (Finset.mem_univ p) hq a b
  simp only [key, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => (mul_assoc _ _ _).symm

end SmallerSolution






/-! ### Character sums

Weighting a solution's amplitude by a product of functions of the individual colours and
summing over all colourings leaves only the constant colourings, since the amplitude
kills every other.  So the whole character sum is determined by the weights not at all —
it depends only on the functions chosen.

This holds regardless of how dense the weights are, which is what makes it available
where the support-based arguments are not.
-/

section CharacterSums

open Amplitude

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **A solution's character sums are forced.**  Summing the amplitude against any
product of per-site functions leaves exactly the constant colourings' contributions. -/
theorem character_sum_of_solution (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (φ : V → Fin 3 → ℂ) :
    (∑ c : V → Fin 3, amplitude W c * ∏ u : V, φ u (c u))
      = ∑ k : Fin 3, ∏ u : V, φ u k := by
  classical
  set S : Finset (V → Fin 3) :=
    (Finset.univ : Finset (Fin 3)).image (fun k => Amplitude.const (V := V) k) with hS
  have hinj : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      Amplitude.const (V := V) i = Amplitude.const (V := V) j → i = j := by
    intro i _ j _ h
    exact congrFun h (Classical.arbitrary V)
  have hout : ∀ c ∈ (Finset.univ : Finset (V → Fin 3)), c ∉ S →
      amplitude W c * ∏ u : V, φ u (c u) = 0 := by
    intro c _ hc
    have hmono : ¬ Amplitude.Monochromatic c := by
      rintro ⟨k, hk⟩
      exact hc (by
        rw [hS]
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, funext fun v => (hk v).symm⟩)
    rw [hzero c hmono, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) hout, hS,
    Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hone k, one_mul]
  rfl

end CharacterSums


/-! ### A site of degree two

Every matching pairs a site with one of its neighbours, so a site reaching only two of
them leaves the amplitude with two terms.  For a solution at a colouring that is already
non-constant away from that site, those two terms cancel — and they cancel for every
colour the site itself might wear, since neither coefficient sees that colour.

So the two columns the site contributes are linearly dependent, with the complementary
matching sums as coefficients.  No hypothesis beyond the degree is needed.
-/

section DegreeTwo

open Amplitude MatchingSum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The two columns at a degree-two site are dependent.**  With the complementary
matching sums as coefficients, and for every colour the site may wear. -/
theorem degree_two_columns_dependent (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p x y : V} (hx : x ∈ Finset.univ.erase p) (hy : y ∈ Finset.univ.erase p) (hxy : x ≠ y)
    (hdeg : ∀ v ∈ Finset.univ.erase p, v ≠ x → v ≠ y →
      ∀ α γ : Fin 3, W s((p, α), (v, γ)) = 0)
    (c : V → Fin 3) (hc : ∀ α : Fin 3, ¬ Amplitude.Monochromatic (Function.update c p α))
    (α : Fin 3) :
    W s((p, α), (x, c x)) *
        pmSum W c ((Finset.univ.erase p).erase x)
      + W s((p, α), (y, c y)) *
        pmSum W c ((Finset.univ.erase p).erase y) = 0 := by
  classical
  set c' : V → Fin 3 := Function.update c p α with hc'
  have hcp : c' p = α := by rw [hc', Function.update_self]
  have hoff : ∀ v : V, v ≠ p → c' v = c v := fun v h => by
    rw [hc', Function.update_of_ne h]
  have hamp := hzero c' (hc α)
  rw [amplitude_eq_sum_pmSum W c' p] at hamp
  have hterm : ∀ v ∈ Finset.univ.erase p,
      W (Sym2.map (paint c') s(p, v)) * pmSum W c' ((Finset.univ.erase p).erase v)
        = W s((p, α), (v, c v)) * pmSum W c ((Finset.univ.erase p).erase v) := by
    intro v hv
    have hvp : v ≠ p := Finset.ne_of_mem_erase hv
    have h1 : W (Sym2.map (paint c') s(p, v)) = W s((p, α), (v, c v)) := by
      rw [show Sym2.map (paint c') s(p, v) = s((p, c' p), (v, c' v)) from rfl, hcp, hoff v hvp]
    have h2 : pmSum W c' ((Finset.univ.erase p).erase v)
        = pmSum W c ((Finset.univ.erase p).erase v) :=
      pmSum_congr_colour W fun z hz =>
        hoff z (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz))
    rw [h1, h2]
  rw [Finset.sum_congr rfl hterm] at hamp
  rw [← Finset.add_sum_erase _ _ hx] at hamp
  have hy' : y ∈ (Finset.univ.erase p).erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  rw [← Finset.add_sum_erase _ _ hy'] at hamp
  have hrest : (∑ v ∈ ((Finset.univ.erase p).erase x).erase y,
      W s((p, α), (v, c v)) * pmSum W c ((Finset.univ.erase p).erase v)) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    have hvy : v ≠ y := Finset.ne_of_mem_erase hv
    have hvx : v ≠ x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hv)
    have hvmem : v ∈ Finset.univ.erase p :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv)
    rw [hdeg v hvmem hvx hvy α (c v), zero_mul]
  rw [hrest, add_zero] at hamp
  exact hamp


/-- **Independent columns at a degree-two site kill both complementary sums.**

The dependency holds for every colour the site wears, so it is a relation between two
vectors.  If those vectors are independent the coefficients vanish — and the coefficients
are the matching sums on the two sets the site's neighbours leave behind.

So a degree-two site forces a choice at every colouring: either the two columns it
contributes are dependent, or both complementary matching sums are zero.  Since the
columns at a site must span, they cannot all be dependent, and the vanishing is forced
somewhere. -/
theorem degree_two_sums_vanish (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p x y : V} (hx : x ∈ Finset.univ.erase p) (hy : y ∈ Finset.univ.erase p) (hxy : x ≠ y)
    (hdeg : ∀ v ∈ Finset.univ.erase p, v ≠ x → v ≠ y →
      ∀ α γ : Fin 3, W s((p, α), (v, γ)) = 0)
    (c : V → Fin 3) (hc : ∀ α : Fin 3, ¬ Amplitude.Monochromatic (Function.update c p α))
    (hindep : ∀ a b : ℂ,
      (∀ α : Fin 3, a * W s((p, α), (x, c x)) + b * W s((p, α), (y, c y)) = 0) →
        a = 0 ∧ b = 0) :
    pmSum W c ((Finset.univ.erase p).erase x) = 0
      ∧ pmSum W c ((Finset.univ.erase p).erase y) = 0 := by
  refine hindep _ _ fun α => ?_
  have h := degree_two_columns_dependent W hzero hx hy hxy hdeg c hc α
  linear_combination h


/-- **A degree-two site forces a monochromatic matching sum to vanish.**

Take the colouring that is constant except at one of the site's two neighbours, where it
differs.  That colouring is non-constant away from the site, so the dependency applies;
and if the two columns it selects are independent, the complementary matching sums vanish.
One of them is a monochromatic sum on everything but the site and that neighbour.

So independence at a single pair of colours already forces a monochromatic matching sum to
be zero — a conclusion about constant colourings drawn from a relation that only holds at
non-constant ones. -/
theorem degree_two_forces_vanishing (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p x y : V} (hx : x ∈ Finset.univ.erase p) (hy : y ∈ Finset.univ.erase p) (hxy : x ≠ y)
    (hdeg : ∀ v ∈ Finset.univ.erase p, v ≠ x → v ≠ y →
      ∀ α γ' : Fin 3, W s((p, α), (v, γ')) = 0)
    {γ δ : Fin 3} (hγδ : γ ≠ δ)
    (z : V) (hzp : z ≠ p) (hzx : z ≠ x)
    (hindep : ∀ a b : ℂ,
      (∀ α : Fin 3, a * W s((p, α), (x, γ)) + b * W s((p, α), (y, δ)) = 0) →
        a = 0 ∧ b = 0) :
    pmSum W (Amplitude.const δ) ((Finset.univ.erase p).erase x) = 0 := by
  classical
  set c : V → Fin 3 := Function.update (Amplitude.const δ) x γ with hc
  have hcx : c x = γ := by rw [hc, Function.update_self]
  have hcoff : ∀ v : V, v ≠ x → c v = δ := fun v h => by
    rw [hc, Function.update_of_ne h]; rfl
  have hcy : c y = δ := hcoff y (Ne.symm hxy)
  have hxp : x ≠ p := Finset.ne_of_mem_erase hx
  have hnc : ∀ α : Fin 3, ¬ Amplitude.Monochromatic (Function.update c p α) := by
    intro α ⟨k, hk⟩
    have h1 : Function.update c p α x = γ := by
      rw [Function.update_of_ne hxp, hcx]
    have h2 : Function.update c p α z = δ := by
      rw [Function.update_of_ne hzp, hcoff z hzx]
    exact hγδ (by rw [← h1, ← h2, hk x, hk z])
  have hres := (degree_two_sums_vanish W hzero hx hy hxy hdeg c hnc
    (by rw [hcx, hcy]; exact hindep)).1
  rwa [pmSum_congr_colour W (c := c) (c' := Amplitude.const δ)
    (fun v hv => hcoff v (Finset.ne_of_mem_erase hv))] at hres


/-- **A degree-two site cannot have independent columns in both directions.**

If at every colour the site's first block has a column independent of the second block's
column there — and symmetrically with the blocks exchanged — then every monochromatic
matching sum on the complement of the site and either neighbour vanishes.

But the vertex equation guarantees that at each colour some neighbour leaves such a sum
alive, and a site of degree two has only these two neighbours.  So the two cannot both
hold, and a solution's degree-two site must have dependent columns somewhere. -/
theorem degree_two_not_independent_both_ways [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : 2 ≤ Fintype.card V)
    {p x y : V} (hx : x ∈ Finset.univ.erase p) (hy : y ∈ Finset.univ.erase p) (hxy : x ≠ y)
    (hdeg : ∀ v ∈ Finset.univ.erase p, v ≠ x → v ≠ y →
      ∀ α γ' : Fin 3, W s((p, α), (v, γ')) = 0)
    (z : V) (hzp : z ≠ p) (hzx : z ≠ x) (hzy : z ≠ y)
    (hIx : ∀ δ : Fin 3, ∃ γ : Fin 3, γ ≠ δ ∧ ∀ a b : ℂ,
      (∀ α : Fin 3, a * W s((p, α), (x, γ)) + b * W s((p, α), (y, δ)) = 0) → a = 0 ∧ b = 0)
    (hIy : ∀ δ : Fin 3, ∃ γ : Fin 3, γ ≠ δ ∧ ∀ a b : ℂ,
      (∀ α : Fin 3, a * W s((p, α), (y, γ)) + b * W s((p, α), (x, δ)) = 0) → a = 0 ∧ b = 0) :
    False := by
  classical
  have hkillx : ∀ δ : Fin 3,
      pmSum W (Amplitude.const δ) ((Finset.univ.erase p).erase x) = 0 := by
    intro δ
    obtain ⟨γ, hγ, hind⟩ := hIx δ
    exact degree_two_forces_vanishing W hzero hx hy hxy hdeg hγ z hzp hzx hind
  have hkilly : ∀ δ : Fin 3,
      pmSum W (Amplitude.const δ) ((Finset.univ.erase p).erase y) = 0 := by
    intro δ
    obtain ⟨γ, hγ, hind⟩ := hIy δ
    exact degree_two_forces_vanishing W hzero hy hx (Ne.symm hxy)
      (fun v hv hvy hvx => hdeg v hv hvx hvy) hγ z hzp hzy hind
  obtain ⟨v, hv, hne, hlive⟩ := exists_partner_live W hone hzero p 0 hV
  by_cases hvx : v = x
  · exact hlive (by rw [hvx]; exact hkillx 0)
  by_cases hvy : v = y
  · exact hlive (by rw [hvy]; exact hkilly 0)
  · exact hne (hdeg v hv hvx hvy 0 0)


/-- **The relation at a site of any degree.**  Expanding the amplitude at a site leaves
one term per neighbour it reaches, and for a solution at a colouring already non-constant
away from that site those terms cancel — for every colour the site itself wears, since no
coefficient sees it.

So the columns the site's neighbours contribute are linearly dependent, with the
complementary matching sums as coefficients.  With fewer neighbours than colours this is
a genuine constraint; a site of degree three against three colours makes the three
selected columns singular unless all three sums vanish. -/
theorem site_relation (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p : V} (T : Finset V) (hT : T ⊆ Finset.univ.erase p)
    (hdeg : ∀ v ∈ Finset.univ.erase p, v ∉ T →
      ∀ α γ : Fin 3, W s((p, α), (v, γ)) = 0)
    (c : V → Fin 3) (hc : ∀ α : Fin 3, ¬ Amplitude.Monochromatic (Function.update c p α))
    (α : Fin 3) :
    (∑ v ∈ T, W s((p, α), (v, c v)) *
      pmSum W c ((Finset.univ.erase p).erase v)) = 0 := by
  classical
  set c' : V → Fin 3 := Function.update c p α with hc'
  have hcp : c' p = α := by rw [hc', Function.update_self]
  have hoff : ∀ v : V, v ≠ p → c' v = c v := fun v h => by
    rw [hc', Function.update_of_ne h]
  have hamp := hzero c' (hc α)
  rw [amplitude_eq_sum_pmSum W c' p] at hamp
  have hterm : ∀ v ∈ Finset.univ.erase p,
      W (Sym2.map (paint c') s(p, v)) * pmSum W c' ((Finset.univ.erase p).erase v)
        = W s((p, α), (v, c v)) * pmSum W c ((Finset.univ.erase p).erase v) := by
    intro v hv
    have hvp : v ≠ p := Finset.ne_of_mem_erase hv
    have h1 : W (Sym2.map (paint c') s(p, v)) = W s((p, α), (v, c v)) := by
      rw [show Sym2.map (paint c') s(p, v) = s((p, c' p), (v, c' v)) from rfl, hcp,
        hoff v hvp]
    have h2 : pmSum W c' ((Finset.univ.erase p).erase v)
        = pmSum W c ((Finset.univ.erase p).erase v) :=
      pmSum_congr_colour W fun z hz =>
        hoff z (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz))
    rw [h1, h2]
  rw [Finset.sum_congr rfl hterm] at hamp
  rw [← Finset.sum_subset hT (fun v hv hvT => by rw [hdeg v hv hvT α (c v), zero_mul])]
    at hamp
  exact hamp


/-- **Independent columns at a site of any degree kill every complementary sum.**

The relation is a dependency among the columns the neighbours contribute, holding for
every colour the site wears.  If those columns are independent as a family, all the
coefficients vanish — and the coefficients are the matching sums on the sets the
neighbours leave behind.

At three colours this is sharp for a site of degree three: three columns in three
dimensions are independent exactly when their determinant is nonzero, and then all three
complementary matching sums are zero. -/
theorem site_sums_vanish_of_independent (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p : V} (T : Finset V) (hT : T ⊆ Finset.univ.erase p)
    (hdeg : ∀ v ∈ Finset.univ.erase p, v ∉ T →
      ∀ α γ : Fin 3, W s((p, α), (v, γ)) = 0)
    (c : V → Fin 3) (hc : ∀ α : Fin 3, ¬ Amplitude.Monochromatic (Function.update c p α))
    (hindep : ∀ f : V → ℂ,
      (∀ α : Fin 3, (∑ v ∈ T, f v * W s((p, α), (v, c v))) = 0) → ∀ v ∈ T, f v = 0) :
    ∀ v ∈ T, pmSum W c ((Finset.univ.erase p).erase v) = 0 := by
  refine hindep _ fun α => ?_
  have h := site_relation W hzero T hT hdeg c hc α
  rw [← h]
  exact Finset.sum_congr rfl fun v _ => mul_comm _ _


/-- **Forced vanishing at any degree.**  Colour everything one way except at a chosen
neighbour: the colouring is non-constant away from the site, and if the columns it selects
are independent, the matching sum on the complement of the site and that neighbour --
monochromatic there -- vanishes. -/
theorem site_forces_vanishing (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p : V} (T : Finset V) (hT : T ⊆ Finset.univ.erase p)
    (hdeg : ∀ v ∈ Finset.univ.erase p, v ∉ T →
      ∀ α γ' : Fin 3, W s((p, α), (v, γ')) = 0)
    {x : V} (hx : x ∈ T) {γ δ : Fin 3} (hγδ : γ ≠ δ)
    (z : V) (hzp : z ≠ p) (hzx : z ≠ x)
    (hindep : ∀ f : V → ℂ,
      (∀ α : Fin 3, (∑ v ∈ T, f v *
        W s((p, α), (v, Function.update (Amplitude.const δ) x γ v))) = 0) →
          ∀ v ∈ T, f v = 0) :
    pmSum W (Amplitude.const δ) ((Finset.univ.erase p).erase x) = 0 := by
  classical
  set c : V → Fin 3 := Function.update (Amplitude.const δ) x γ with hc
  have hcx : c x = γ := by rw [hc, Function.update_self]
  have hcoff : ∀ v : V, v ≠ x → c v = δ := fun v h => by
    rw [hc, Function.update_of_ne h]; rfl
  have hxp : x ≠ p := Finset.ne_of_mem_erase (hT hx)
  have hnc : ∀ α : Fin 3, ¬ Amplitude.Monochromatic (Function.update c p α) := by
    intro α ⟨k, hk⟩
    have h1 : Function.update c p α x = γ := by rw [Function.update_of_ne hxp, hcx]
    have h2 : Function.update c p α z = δ := by
      rw [Function.update_of_ne hzp, hcoff z hzx]
    exact hγδ (by rw [← h1, ← h2, hk x, hk z])
  have hres := site_sums_vanish_of_independent W hzero T hT hdeg c hnc hindep x hx
  rwa [pmSum_congr_colour W (c := c) (c' := Amplitude.const δ)
    (fun v hv => hcoff v (Finset.ne_of_mem_erase hv))] at hres

/-- **A site whose columns are independent at every neighbour and colour is impossible.**

Each such independence forces a monochromatic matching sum to vanish; taken over all
neighbours and colours it kills every one of them.  The vertex equation says some
neighbour keeps one alive, and the site reaches no others.  So no solution has such a
site, whatever its degree. -/
theorem no_site_independent_everywhere [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : 2 ≤ Fintype.card V)
    {p : V} (T : Finset V) (hT : T ⊆ Finset.univ.erase p)
    (hdeg : ∀ v ∈ Finset.univ.erase p, v ∉ T →
      ∀ α γ' : Fin 3, W s((p, α), (v, γ')) = 0)
    (hkill : ∀ x ∈ T, ∀ δ : Fin 3,
      pmSum W (Amplitude.const δ) ((Finset.univ.erase p).erase x) = 0) :
    False := by
  classical
  obtain ⟨v, hv, hne, hlive⟩ := exists_partner_live W hone hzero p 0 hV
  by_cases hvT : v ∈ T
  · exact hlive (hkill v hvT 0)
  · exact hne (hdeg v hv hvT 0 0)


/-- **Where a matching sum stays alive, the columns must degenerate.**

Read the forced vanishing the other way.  If the monochromatic matching sum on the
complement of the site and one of its neighbours does *not* vanish — and the vertex
equation guarantees that somewhere it does not — then the columns selected at that
neighbour cannot be independent.

So liveness and independence exclude each other, site by site and colour by colour.  At
three colours and a site of degree three this says the three selected columns are
singular exactly where the equations keep a sum alive, which is the determinantal
statement the constraint was reaching for. -/
theorem columns_dependent_of_live (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p : V} (T : Finset V) (hT : T ⊆ Finset.univ.erase p)
    (hdeg : ∀ v ∈ Finset.univ.erase p, v ∉ T →
      ∀ α γ' : Fin 3, W s((p, α), (v, γ')) = 0)
    {x : V} (hx : x ∈ T) {γ δ : Fin 3} (hγδ : γ ≠ δ)
    (z : V) (hzp : z ≠ p) (hzx : z ≠ x)
    (hlive : pmSum W (Amplitude.const δ) ((Finset.univ.erase p).erase x) ≠ 0) :
    ¬ (∀ f : V → ℂ,
      (∀ α : Fin 3, (∑ v ∈ T, f v *
        W s((p, α), (v, Function.update (Amplitude.const δ) x γ v))) = 0) →
          ∀ v ∈ T, f v = 0) := by
  intro hindep
  exact hlive (site_forces_vanishing W hzero T hT hdeg hx hγδ z hzp hzx hindep)



/-- **The columns at a site cannot all lie in a plane.**

If every column were a combination of two fixed vectors, the annihilator those two admit
would annihilate every column, hence be zero.  But it is not.

So the nine columns a cubic site contributes span all three dimensions, and any argument
that drives them into a common plane closes. -/
theorem columns_not_in_plane [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (hV : 2 ≤ Fintype.card V) (e : Fin 2 → Fin 3 → ℂ)
    (hplane : ∀ v ∈ Finset.univ.erase u, ∀ b : Fin 3, ∃ s t : ℂ,
      ∀ j : Fin 3, W s((u, j), (v, b)) = s * e 0 j + t * e 1 j) :
    False := by
  classical
  obtain ⟨lam, hne, hann⟩ := exists_annihilator_of_two (K := ℂ) (C := Fin 3) e (by simp)
  refine hne (eq_zero_of_annihilates_site W hone hzero u hV lam ?_)
  intro v hv b
  obtain ⟨s, t, hst⟩ := hplane v hv b
  have : ∑ j : Fin 3, lam j * W s((u, j), (v, b))
      = s * (∑ j, lam j * e 0 j) + t * (∑ j, lam j * e 1 j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hst j]; ring
  rw [this, hann 0, hann 1, mul_zero, mul_zero, add_zero]




/-- **Dependency at every live colouring, not just the near-constant ones.**

Wherever a colouring non-constant away from the site leaves *any* of the complementary
matching sums alive, the columns that colouring selects are dependent.  The earlier
statement is the case of a colouring constant but for one neighbour; this is the whole
family.

So the determinantal conditions are indexed by live colourings, of which there are as
many as the equations permit — a far larger supply than the three the vertex equation
hands over directly. -/
theorem columns_dependent_of_live_general (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p : V} (T : Finset V) (hT : T ⊆ Finset.univ.erase p)
    (hdeg : ∀ v ∈ Finset.univ.erase p, v ∉ T →
      ∀ α γ' : Fin 3, W s((p, α), (v, γ')) = 0)
    (c : V → Fin 3) (hc : ∀ α : Fin 3, ¬ Amplitude.Monochromatic (Function.update c p α))
    {x : V} (hx : x ∈ T)
    (hlive : pmSum W c ((Finset.univ.erase p).erase x) ≠ 0) :
    ¬ (∀ f : V → ℂ,
      (∀ α : Fin 3, (∑ v ∈ T, f v * W s((p, α), (v, c v))) = 0) → ∀ v ∈ T, f v = 0) := by
  intro hindep
  exact hlive (site_sums_vanish_of_independent W hzero T hT hdeg c hc hindep x hx)


/-- **Evading the site relation is the descent condition.**

A solution escapes the determinantal constraints only by having every complementary
matching sum vanish at every colouring non-constant away from the site.  Any colouring
that already disagrees at two of the remaining sites is such a colouring, so the escape
means the matching sum on those sites vanishes whenever they are not uniformly coloured.

That is the vanishing half of the defining conditions, two sites down.  So the count that
decides the cubic case is not an incidental quantity: having no live colouring at all *is*
the descent, and having one forces the columns to degenerate. -/
theorem site_vanishing_on_subset (W : Sym2 (V × Fin 3) → ℂ) {p x : V}
    (hall : ∀ c : V → Fin 3,
      (∀ α : Fin 3, ¬ Amplitude.Monochromatic (Function.update c p α)) →
        pmSum W c ((Finset.univ.erase p).erase x) = 0)
    (c : V → Fin 3) {u w : V}
    (hu : u ∈ (Finset.univ.erase p).erase x) (hw : w ∈ (Finset.univ.erase p).erase x)
    (hne : c u ≠ c w) :
    pmSum W c ((Finset.univ.erase p).erase x) = 0 := by
  refine hall c fun α ⟨k, hk⟩ => hne ?_
  have hup : u ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hu)
  have hwp : w ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hw)
  have h1 : c u = k := by
    have hu' := hk u
    rwa [Function.update_of_ne hup] at hu'
  have h2 : c w = k := by
    have hw' := hk w
    rwa [Function.update_of_ne hwp] at hw'
  rw [h1, h2]


/-- **The site dichotomy.**

At any site of a solution, and any neighbour of it, exactly one of two things happens.

Either some colouring non-constant away from the site leaves that neighbour's
complementary matching sum alive — and then the columns that colouring selects are
linearly dependent, which at three colours and degree three means a vanishing
determinant.

Or no such colouring does, and then the matching sum on the sites the neighbour leaves
behind vanishes at every colouring that is not uniform on them: the vanishing half of the
defining conditions, two sites down.

Nothing here uses a cap, a contraction, or an assumed degeneracy.  The fork is reached
from the amplitude expansion and the vertex equation alone, and both branches are things
the programme wants. -/
theorem site_dichotomy (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p : V} (T : Finset V) (hT : T ⊆ Finset.univ.erase p)
    (hdeg : ∀ v ∈ Finset.univ.erase p, v ∉ T →
      ∀ α γ' : Fin 3, W s((p, α), (v, γ')) = 0)
    {x : V} (hx : x ∈ T) :
    (∃ c : V → Fin 3,
        (∀ α : Fin 3, ¬ Amplitude.Monochromatic (Function.update c p α)) ∧
        pmSum W c ((Finset.univ.erase p).erase x) ≠ 0 ∧
        ¬ (∀ f : V → ℂ,
            (∀ α : Fin 3, (∑ v ∈ T, f v * W s((p, α), (v, c v))) = 0) →
              ∀ v ∈ T, f v = 0))
      ∨ (∀ c : V → Fin 3, ∀ u ∈ (Finset.univ.erase p).erase x,
          ∀ w ∈ (Finset.univ.erase p).erase x, c u ≠ c w →
            pmSum W c ((Finset.univ.erase p).erase x) = 0) := by
  classical
  by_cases h : ∃ c : V → Fin 3,
      (∀ α : Fin 3, ¬ Amplitude.Monochromatic (Function.update c p α)) ∧
      pmSum W c ((Finset.univ.erase p).erase x) ≠ 0
  · obtain ⟨c, hc, hlive⟩ := h
    exact Or.inl ⟨c, hc, hlive,
      columns_dependent_of_live_general W hzero T hT hdeg c hc hx hlive⟩
  · push_neg at h
    exact Or.inr fun c u hu w hw hne =>
      site_vanishing_on_subset W (fun c' hc' => h c' hc') c hu hw hne

end DegreeTwo


/-! ### From a subsystem to a solution

The descent branch says the matching sum over a subset vanishes at every colouring that
is not uniform there.  Paired with the three monochromatic sums surviving, that is a
solution on the subset — and the transport machinery carries it to a solution on a
standard vertex set of the right size.
-/

section Subsystem

open Amplitude MatchingSum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A subset whose matching sums behave carries a solution.**

Vanishing at every non-uniform colouring and surviving at the three uniform ones is
exactly what a solution on those sites means, once the weights are read there. -/
theorem isGHZ_restrict (W : Sym2 (V × Fin 3) → ℂ) (S : Finset V) [Nonempty ↥S]
    (hvan : ∀ c : V → Fin 3, (∃ u ∈ S, ∃ w ∈ S, c u ≠ c w) → pmSum W c S = 0)
    (hmono : ∀ k : Fin 3, pmSum W (Amplitude.const k) S ≠ 0) :
    KrennGu.IsGHZ (restrictW W S) := by
  classical
  constructor
  · intro k
    have h := amplitude_restrictSites W S (Amplitude.const (V := V) k)
    rw [show (fun u : ↥S => (Amplitude.const (V := V) k) (u : V))
        = Amplitude.const (V := ↥S) k from rfl] at h
    rw [h]
    exact hmono k
  · intro c' hc'
    obtain ⟨u₀⟩ := ‹Nonempty ↥S›
    obtain ⟨u, w, huw⟩ : ∃ u w : ↥S, c' u ≠ c' w := by
      by_contra hcon
      push_neg at hcon
      exact hc' ⟨c' u₀, fun v => hcon v u₀⟩
    set c : V → Fin 3 := fun v => if h : v ∈ S then c' ⟨v, h⟩ else c' u₀ with hcdef
    have hc : ∀ v : ↥S, c (v : V) = c' v := by
      intro v
      simp only [hcdef, dif_pos v.2]
    have hcc : c' = fun v : ↥S => c (v : V) := funext fun v => (hc v).symm
    rw [hcc, amplitude_restrictSites]
    refine hvan c ⟨(u : V), u.2, (w : V), w.2, ?_⟩
    rw [hc u, hc w]
    exact huw


/-- Renaming the sites preserves being a solution. -/
theorem isGHZ_relabel {V' : Type*} [Fintype V'] [DecidableEq V']
    (W : Sym2 (V × Fin 3) → ℂ) (e : V' ≃ V) (h : KrennGu.IsGHZ W) :
    KrennGu.IsGHZ (relabelW W e) := by
  obtain ⟨hone, hzero⟩ := h
  constructor
  · intro k
    have := amplitude_relabel W e (Amplitude.const (V := V) k)
    rw [show (fun u : V' => (Amplitude.const (V := V) k) (e u))
        = Amplitude.const (V := V') k from rfl] at this
    rw [this]
    exact hone k
  · intro c' hc'
    have hval : amplitude (relabelW W e) (fun u : V' => (c' ∘ e.symm) (e u))
        = amplitude W (c' ∘ e.symm) := amplitude_relabel W e (c' ∘ e.symm)
    rw [show (fun u : V' => (c' ∘ e.symm) (e u)) = c' from
      funext fun u => by simp] at hval
    rw [hval]
    refine hzero _ fun ⟨k, hk⟩ => hc' ⟨k, fun u => ?_⟩
    have := hk (e u)
    simpa using this

/-- **A six-site subset behaving like a solution contradicts the settled base case.**

If the matching sums over a six-element subset vanish at every non-uniform colouring and
survive at the three uniform ones, that subset carries a solution; relabelling puts it on
the standard six-site vertex set, and the six-site statement denies it.

The base case is taken as a hypothesis, not reproved here. -/
theorem no_six_subsystem (W : Sym2 (V × Fin 3) → ℂ) (hb : ¬ KrennGu.Solvable 3)
    (S : Finset V) (hcard : Fintype.card ↥S = 2 * 3) [Nonempty ↥S]
    (hvan : ∀ c : V → Fin 3, (∃ u ∈ S, ∃ w ∈ S, c u ≠ c w) → pmSum W c S = 0)
    (hmono : ∀ k : Fin 3, pmSum W (Amplitude.const k) S ≠ 0) :
    False := by
  classical
  have hG : KrennGu.IsGHZ (restrictW W S) := isGHZ_restrict W S hvan hmono
  obtain ⟨e⟩ : Nonempty (Fin (2 * 3) ≃ ↥S) :=
    ⟨(Fintype.equivFinOfCardEq hcard).symm⟩
  exact hb ⟨relabelW (restrictW W S) e, isGHZ_relabel _ e hG⟩


/-- **A lone live neighbour pins its column to a basis vector.**

If at some colour exactly one neighbour leaves a nonvanishing monochromatic matching sum
behind, the vertex equation collapses to a single term, and the column that neighbour
contributes at that colour is a multiple of the corresponding basis vector: its entry
agrees with the Kronecker symbol, scaled by the surviving sum.

This is the rigidity of the spread case, where three colours are served by three different
neighbours.  It is exactly the shape of the four-vertex solution, whose blocks each carry
a single entry on the diagonal, and it says a counterexample of that shape has no freedom
in those columns. -/
theorem lone_live_column [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (hV : 2 ≤ Fintype.card V) (k : Fin 3) {v₀ : V} (hv₀ : v₀ ∈ Finset.univ.erase u)
    (hlone : ∀ v ∈ Finset.univ.erase u, v ≠ v₀ →
      pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v) = 0)
    (j : Fin 3) :
    W s((u, j), (v₀, k)) *
      pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v₀)
        = if j = k then 1 else 0 := by
  classical
  have hsum := vertex_equations W hone hzero u k j hV
  rw [← Finset.add_sum_erase _ _ hv₀] at hsum
  have hrest : (∑ v ∈ (Finset.univ.erase u).erase v₀,
      W s((u, j), (v, k)) *
        pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v)) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [hlone v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv), mul_zero]
  rw [hrest, add_zero] at hsum
  exact hsum


/-- **Off the diagonal, a pinned column vanishes.**  Where a colour has exactly one live
neighbour, every entry of that neighbour's column at that colour, other than the matching
one, is zero. -/
theorem lone_live_offdiag [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (hV : 2 ≤ Fintype.card V) (k : Fin 3) {v₀ : V} (hv₀ : v₀ ∈ Finset.univ.erase u)
    (hlone : ∀ v ∈ Finset.univ.erase u, v ≠ v₀ →
      pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v) = 0)
    (hlive : pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v₀) ≠ 0)
    {j : Fin 3} (hjk : j ≠ k) :
    W s((u, j), (v₀, k)) = 0 := by
  have h := lone_live_column W hone hzero u hV k hv₀ hlone j
  rw [if_neg hjk] at h
  exact (mul_eq_zero.mp h).resolve_right hlive

/-- **On the diagonal, a pinned column does not vanish.**  The same collapse makes the
matching entry the reciprocal of the surviving sum, so neither can be zero. -/
theorem lone_live_diag_ne [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const k) = 1)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (hV : 2 ≤ Fintype.card V) (k : Fin 3) {v₀ : V} (hv₀ : v₀ ∈ Finset.univ.erase u)
    (hlone : ∀ v ∈ Finset.univ.erase u, v ≠ v₀ →
      pmSum W (Amplitude.const k) ((Finset.univ.erase u).erase v) = 0) :
    W s((u, k), (v₀, k)) ≠ 0 := by
  intro hW
  have h := lone_live_column W hone hzero u hV k hv₀ hlone k
  rw [if_pos rfl, hW, zero_mul] at h
  exact zero_ne_one h

end Subsystem

end FourVertexRank
