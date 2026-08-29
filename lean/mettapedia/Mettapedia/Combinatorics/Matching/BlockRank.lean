import Mathlib
import Mettapedia.Combinatorics.Matching.Amplitude
import Mettapedia.Combinatorics.Matching.Sum
import Mettapedia.Combinatorics.Matching.EdgeColoring

/-!
# Low-rank structure in weighted matching blocks

Finite-dimensional annihilators, the two-free-vertex matching decomposition,
and generic consequences for edge-coloured and weighted matching systems.
-/

namespace MatchingBlockRank

open Amplitude

/-! ### The rank bound in general

The four-site computation is one instance of a pattern that does not depend on the
vertex count.  Fix a *non-constant* colouring on every site but two.  Then the whole
colouring is non-constant however the two free sites are coloured, so the amplitude
vanishes identically in them, and splitting the matchings by how the free sites are
matched writes that identically vanishing matrix as the block of the free pair scaled
by a matching sum, plus one rank-one term for each way of sending the free sites to
distinct partners.

Only partners adjacent in the support contribute, so the number of rank-one terms is
governed by the degrees, not by the vertex count.  When it falls below the number of
colours the block is pinned.

The linear algebra that turns "few rank-one terms" into "the block degenerates" is
isolated here, since it is the load-bearing step and depends on nothing about
matchings. -/

section RankBound

/-- **A matrix built from too few rank-one pieces has dependent rows.**  If every
entry of `M` is a sum of `m` products, one factor depending on the row and one on the
column, and `m` is smaller than the side of the matrix, then some nonzero combination
of the rows vanishes.

This is what converts a bound on the number of contributing matchings into
degeneracy of a weight block. -/
theorem exists_left_null_of_few_terms {D m : ℕ} (M : Fin D → Fin D → ℂ)
    (u v : Fin m → Fin D → ℂ)
    (hM : ∀ d e, M d e = ∑ i, u i d * v i e) (hlt : m < D) :
    ∃ lam : Fin D → ℂ, lam ≠ 0 ∧ ∀ e, ∑ d, lam d * M d e = 0 := by
  classical
  let L : (Fin D → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun lam i => ∑ d, lam d * u i d
      map_add' := by
        intro x y
        funext i
        simp only [Pi.add_apply, add_mul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro c x
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum] }
  have hrank : Module.finrank ℂ (Fin m → ℂ) < Module.finrank ℂ (Fin D → ℂ) := by
    simpa using hlt
  obtain ⟨lam, hlam, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt hrank)
  refine ⟨lam, hne, fun e => ?_⟩
  have hker : ∀ i, ∑ d, lam d * u i d = 0 := by
    intro i
    have h : L lam = 0 := LinearMap.mem_ker.mp hlam
    have h2 := congrFun h i
    simpa [L] using h2
  calc ∑ d, lam d * M d e
      = ∑ d, ∑ i, lam d * (u i d * v i e) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hM d e, Finset.mul_sum]
    _ = ∑ i, ∑ d, lam d * (u i d * v i e) := Finset.sum_comm
    _ = ∑ i, (∑ d, lam d * u i d) * v i e := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun d _ => by ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hker i, zero_mul]


/-- The same bound with the index set an arbitrary finite type, which is the form the
colour set takes. -/
theorem exists_left_null_of_few_terms' {K : Type*} [Field K] {C : Type*} [Fintype C]
    [DecidableEq C] {m : ℕ} (M : C → C → K) (u v : Fin m → C → K)
    (hM : ∀ d e, M d e = ∑ i, u i d * v i e) (hlt : m < Fintype.card C) :
    ∃ lam : C → K, lam ≠ 0 ∧ ∀ e, ∑ d, lam d * M d e = 0 := by
  classical
  let L : (C → K) →ₗ[K] (Fin m → K) :=
    { toFun := fun lam i => ∑ d, lam d * u i d
      map_add' := by
        intro x y
        funext i
        simp only [Pi.add_apply, add_mul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro c x
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum] }
  have hrank : Module.finrank K (Fin m → K) < Module.finrank K (C → K) := by
    simpa using hlt
  obtain ⟨lam, hlam, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt hrank)
  refine ⟨lam, hne, fun e => ?_⟩
  have hker : ∀ i, ∑ d, lam d * u i d = 0 := by
    intro i
    have h : L lam = 0 := LinearMap.mem_ker.mp hlam
    have h2 := congrFun h i
    simpa [L] using h2
  calc ∑ d, lam d * M d e
      = ∑ d, ∑ i, lam d * (u i d * v i e) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hM d e, Finset.mul_sum]
    _ = ∑ i, ∑ d, lam d * (u i d * v i e) := Finset.sum_comm
    _ = ∑ i, (∑ d, lam d * u i d) * v i e := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun d _ => by ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hker i, zero_mul]


/-- The strengthened form: the annihilator produced also kills each of the vectors the
matrix was built from.  The proof of the bound establishes this on the way, and it is
what lets the conclusion be chained across partners. -/
theorem exists_left_null_of_few_terms_strong {K : Type*} [Field K] {C : Type*}
    [Fintype C] [DecidableEq C] {m : ℕ} (M : C → C → K) (u v : Fin m → C → K)
    (hM : ∀ d e, M d e = ∑ i, u i d * v i e) (hlt : m < Fintype.card C) :
    ∃ lam : C → K, lam ≠ 0 ∧ (∀ i, ∑ d, lam d * u i d = 0) ∧
      ∀ e, ∑ d, lam d * M d e = 0 := by
  classical
  let L : (C → K) →ₗ[K] (Fin m → K) :=
    { toFun := fun lam i => ∑ d, lam d * u i d
      map_add' := by
        intro x y
        funext i
        simp only [Pi.add_apply, add_mul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro c x
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum] }
  have hrank : Module.finrank K (Fin m → K) < Module.finrank K (C → K) := by
    simpa using hlt
  obtain ⟨lam, hlam, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt hrank)
  have hker : ∀ i, ∑ d, lam d * u i d = 0 := by
    intro i
    have h : L lam = 0 := LinearMap.mem_ker.mp hlam
    have h2 := congrFun h i
    simpa [L] using h2
  refine ⟨lam, hne, hker, fun e => ?_⟩
  calc ∑ d, lam d * M d e
      = ∑ d, ∑ i, lam d * (u i d * v i e) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hM d e, Finset.mul_sum]
    _ = ∑ i, ∑ d, lam d * (u i d * v i e) := Finset.sum_comm
    _ = ∑ i, (∑ d, lam d * u i d) * v i e := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun d _ => by ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hker i, zero_mul]

end RankBound
/-! ### The block decomposition at arbitrary vertex count

Fixing every colour but two and letting those vary turns the matching sum into a
matrix.  The two-site splitting says exactly what that matrix is: the block carried by
the free sites, scaled by the matching sum on everything else, plus one rank-one piece
for each way of sending the free sites to distinct partners.
-/

section GeneralSplit

open MatchingSum

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
variable {R : Type*} [CommRing R]

/-- The colouring fixing `c₀` off two sites and painting them freely. -/
def paintTwo (c₀ : V → C) (p q : V) (α β : C) : V → C :=
  Function.update (Function.update c₀ p α) q β

omit [Fintype V] [DecidableEq C] in
@[simp] theorem paintTwo_fst (c₀ : V → C) {p q : V} (h : p ≠ q) (α β : C) :
    paintTwo c₀ p q α β p = α := by
  simp [paintTwo, Function.update_of_ne h]

omit [Fintype V] [DecidableEq C] in
@[simp] theorem paintTwo_snd (c₀ : V → C) (p q : V) (α β : C) :
    paintTwo c₀ p q α β q = β := by
  simp [paintTwo]

omit [Fintype V] [DecidableEq C] in
theorem paintTwo_other (c₀ : V → C) {p q x : V} (hp : x ≠ p) (hq : x ≠ q) (α β : C) :
    paintTwo c₀ p q α β x = c₀ x := by
  simp [paintTwo, Function.update_of_ne hq, Function.update_of_ne hp]

omit [DecidableEq C] in
/-- **The block decomposition.**  With the colours at two sites free and every other
colour fixed, the matching sum is the block those sites carry, scaled by the matching
sum on the rest, plus a correction assembled from rank-one pieces — one for each
ordered pair of distinct partners the two sites can reach.

Nothing here assumes the weights come from a solution; it is an identity. -/
theorem block_split (W : Sym2 (V × C) → R) (c₀ : V → C) {S : Finset V}
    {p q : V} (hp : p ∈ S) (hq : q ∈ S.erase p) (α β : C) :
    pmSum W (paintTwo c₀ p q α β) S
      = W s((p, α), (q, β)) * pmSum W c₀ ((S.erase p).erase q)
        + ∑ v ∈ (S.erase p).erase q,
            W s((p, α), (v, c₀ v)) *
              ∑ l ∈ ((S.erase p).erase v).erase q,
                W s((q, β), (l, c₀ l)) *
                  pmSum W c₀ ((((S.erase p).erase v).erase q).erase l) := by
  classical
  have hpq : p ≠ q := fun h => (Finset.mem_erase.mp hq).1 h.symm
  set c := paintTwo c₀ p q α β with hc
  have hcp : c p = α := paintTwo_fst c₀ hpq α β
  have hcq : c q = β := paintTwo_snd c₀ p q α β
  have hoff : ∀ x : V, x ≠ p → x ≠ q → c x = c₀ x := fun x h1 h2 =>
    paintTwo_other c₀ h1 h2 α β
  rw [pmSum_split_two W c hp hq]
  have hmain : W (Sym2.map (paint c) s(p, q)) = W s((p, α), (q, β)) := by
    rw [show Sym2.map (paint c) s(p, q) = s((p, c p), (q, c q)) from rfl, hcp, hcq]
  have hrest : pmSum W c ((S.erase p).erase q) = pmSum W c₀ ((S.erase p).erase q) :=
    pmSum_congr_colour W fun x hx =>
      hoff x (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx))
        (Finset.ne_of_mem_erase hx)
  rw [hmain, hrest]
  congr 1
  refine Finset.sum_congr rfl fun v hv => ?_
  have hvp : v ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hv)
  have hvq : v ≠ q := Finset.ne_of_mem_erase hv
  have h1 : W (Sym2.map (paint c) s(p, v)) = W s((p, α), (v, c₀ v)) := by
    rw [show Sym2.map (paint c) s(p, v) = s((p, c p), (v, c v)) from rfl, hcp,
      hoff v hvp hvq]
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlq : l ≠ q := Finset.ne_of_mem_erase hl
  have hlv : l ≠ v := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
  have hlp : l ≠ p :=
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))
  have h2 : W (Sym2.map (paint c) s(q, l)) = W s((q, β), (l, c₀ l)) := by
    rw [show Sym2.map (paint c) s(q, l) = s((q, c q), (l, c l)) from rfl, hcq,
      hoff l hlp hlq]
  have h3 : pmSum W c ((((S.erase p).erase v).erase q).erase l)
      = pmSum W c₀ ((((S.erase p).erase v).erase q).erase l) :=
    pmSum_congr_colour W fun x hx =>
      hoff x
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
          (Finset.mem_of_mem_erase hx))))
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx))
  rw [h2, h3]


/-- **The block degenerates when few partners contribute.**

The hypotheses are exactly the three things the situation supplies.  The matching sum
vanishes for every colouring of the two free sites — which a solution gives whenever
the colours fixed elsewhere are already non-constant.  The matching sum on the
remaining sites does not vanish.  And the correction is assembled from fewer rank-one
pieces than there are colours, which is a statement about how many partners the two
sites can reach in the support.

The conclusion is that the block those sites carry has linearly dependent rows, so it
is singular.  No genericity is assumed and no recognizer is involved: this is read off
the defining equations. -/
theorem block_rows_dependent {K : Type*} [Field K] {V C : Type*} [Fintype V]
    [DecidableEq V] [Fintype C] [DecidableEq C]
    (W : Sym2 (V × C) → K) (c₀ : V → C) {S : Finset V} {p q : V}
    (hp : p ∈ S) (hq : q ∈ S.erase p)
    (hvanish : ∀ α β : C, MatchingSum.pmSum W (paintTwo c₀ p q α β) S = 0)
    (hK : MatchingSum.pmSum W c₀ ((S.erase p).erase q) ≠ 0)
    {m : ℕ} (u v : Fin m → C → K) (hm : m < Fintype.card C)
    (hcorr : ∀ α β : C,
      (∑ x ∈ (S.erase p).erase q,
        W s((p, α), (x, c₀ x)) *
          ∑ l ∈ ((S.erase p).erase x).erase q,
            W s((q, β), (l, c₀ l)) *
              MatchingSum.pmSum W c₀ ((((S.erase p).erase x).erase q).erase l))
        = ∑ i, u i α * v i β) :
    ∃ lam : C → K, lam ≠ 0 ∧ ∀ β : C, ∑ α, lam α * W s((p, α), (q, β)) = 0 := by
  classical
  have hKW : ∀ α β : C,
      MatchingSum.pmSum W c₀ ((S.erase p).erase q) * W s((p, α), (q, β))
        = ∑ i, (-(u i α)) * v i β := by
    intro α β
    have h := block_split W c₀ hp hq α β
    rw [hvanish α β, hcorr α β] at h
    have hneg : ∑ i, (-(u i α)) * v i β = -∑ i, u i α * v i β := by
      simp [neg_mul]
    rw [hneg]
    linear_combination -h
  obtain ⟨lam, hne, hlam⟩ :=
    exists_left_null_of_few_terms'
      (fun α β => MatchingSum.pmSum W c₀ ((S.erase p).erase q) * W s((p, α), (q, β)))
      (fun i α => -(u i α)) v hKW hm
  refine ⟨lam, hne, fun β => ?_⟩
  have h1 := hlam β
  have h2 : MatchingSum.pmSum W c₀ ((S.erase p).erase q) *
      ∑ α, lam α * W s((p, α), (q, β)) = 0 := by
    rw [Finset.mul_sum, ← h1]
    exact Finset.sum_congr rfl fun α _ => by ring
  exact (mul_eq_zero.mp h2).resolve_left hK


/-- **The partner count comes from the support at one site alone.**

Grouping the correction by its outer index makes each summand a product of something
depending only on the first free colour with something depending only on the second.
So the number of rank-one pieces is the number of partners the *first* site can reach,
not the number of pairs: a site of degree three contributes two.

`T` is any set containing every partner the first site actually reaches; terms outside
it vanish because their weight does. -/
theorem few_terms_of_support {K : Type*} [Field K] {V C : Type*} [Fintype V]
    [DecidableEq V] [Fintype C] [DecidableEq C]
    (W : Sym2 (V × C) → K) (c₀ : V → C) {S : Finset V} {p q : V}
    (T : Finset V) (hT : T ⊆ (S.erase p).erase q)
    (hout : ∀ x ∈ (S.erase p).erase q, x ∉ T → ∀ α : C, W s((p, α), (x, c₀ x)) = 0) :
    ∃ u v : Fin T.card → C → K, ∀ α β : C,
      (∑ x ∈ (S.erase p).erase q,
        W s((p, α), (x, c₀ x)) *
          ∑ l ∈ ((S.erase p).erase x).erase q,
            W s((q, β), (l, c₀ l)) *
              MatchingSum.pmSum W c₀ ((((S.erase p).erase x).erase q).erase l))
        = ∑ i, u i α * v i β := by
  classical
  refine ⟨fun i α => W s((p, α), ((T.equivFin.symm i : V), c₀ (T.equivFin.symm i : V))),
    fun i β => ∑ l ∈ ((S.erase p).erase (T.equivFin.symm i : V)).erase q,
      W s((q, β), (l, c₀ l)) *
        MatchingSum.pmSum W c₀
          ((((S.erase p).erase (T.equivFin.symm i : V)).erase q).erase l), ?_⟩
  intro α β
  rw [← Finset.sum_subset hT (fun x hx hnx => by rw [hout x hx hnx α, zero_mul])]
  rw [← Finset.sum_coe_sort T]
  exact Fintype.sum_equiv T.equivFin _ _ (fun x => by simp)


/-- **The term count is really a dimension, not a partner count.**

A correction indexed by partners can be reindexed by any spanning family for the vectors
those partners contribute: expanding each partner's vector in that family and exchanging
the sums leaves one term per family member.

This removes the degree hypothesis from the degeneration argument.  What has to fall
below the number of colours is not how many partners a site has but how many dimensions
their contributions span at the chosen colouring — a quantity bounded by the number of
colours whatever the degree, and one that a colouring can lower by killing partners. -/
theorem few_terms_of_span {K : Type*} [Field K] {C ι : Type*} [Fintype C]
    [DecidableEq ι] (T : Finset ι) (u V : ι → C → K) {d : ℕ} (w : Fin d → C → K)
    (coef : ι → Fin d → K)
    (hdecomp : ∀ x ∈ T, ∀ α : C, u x α = ∑ i, coef x i * w i α) :
    ∀ α β : C,
      (∑ x ∈ T, u x α * V x β) = ∑ i, w i α * (∑ x ∈ T, coef x i * V x β) := by
  intro α β
  calc (∑ x ∈ T, u x α * V x β)
      = ∑ x ∈ T, ∑ i, (coef x i * w i α) * V x β := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [hdecomp x hx α, Finset.sum_mul]
    _ = ∑ i, ∑ x ∈ T, (coef x i * w i α) * V x β := Finset.sum_comm
    _ = ∑ i, w i α * (∑ x ∈ T, coef x i * V x β) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring

end GeneralSplit
section NoSimultaneousWitness

open ColourPerMatching

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

omit [Fintype V] [DecidableEq V] in
/-- **An edge is live for at most one colour.**  Weights that come from colouring the
matchings give an edge a single colour, and it carries weight only there.  So the
partners live at one colour and those live at another never coincide unless the
colours do. -/
theorem live_colour_unique (ec : V → V → Option C) (hsymm : ∀ u v, ec u v = ec v u)
    (u v : V) {k k' : C}
    (hk : weightOf ec hsymm s((u, k), (v, k)) ≠ 0)
    (hk' : weightOf ec hsymm s((u, k'), (v, k')) ≠ 0) : k = k' := by
  rw [weightOf_apply] at hk hk'
  by_cases h : (k : C) = k ∧ ec u v = some k
  · by_cases h' : (k' : C) = k' ∧ ec u v = some k'
    · have := h.2.symm.trans h'.2
      exact Option.some_injective _ this
    · exact absurd (if_neg h') hk'
  · exact absurd (if_neg h) hk

omit [Fintype V] [DecidableEq V] in
/-- No partner is live for two distinct colours, so on such a solution a witness
serving every colour at once cannot exist as soon as there are two colours. -/
theorem no_simultaneous_live (ec : V → V → Option C) (hsymm : ∀ u v, ec u v = ec v u)
    (u v : V) {k k' : C} (hne : k ≠ k') :
    weightOf ec hsymm s((u, k), (v, k)) = 0 ∨ weightOf ec hsymm s((u, k'), (v, k')) = 0 := by
  by_contra hcon
  push Not at hcon
  exact hne (live_colour_unique ec hsymm u v hcon.1 hcon.2)

end NoSimultaneousWitness
/-! ### An unused colour resists perturbation

A weight system that never uses a colour has vanishing monochromatic amplitude there,
and so does every system near it: each matching contributes a product of as many
vanishing factors as it has edges, so the amplitude vanishes to that order in the
perturbation.

The consequence is that a solution in fewer colours cannot be deformed into one in more.
The deficient equation is not merely unsatisfied at such a point; its gradient, and every
derivative below the matching size, vanishes as well.  Reaching it requires a jump, not a
path.
-/

section UnusedColour

open Amplitude

variable {V C : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]

/-- **Perturbing an unused colour costs the full matching size.**  If no edge carries
weight at a colour, then perturbing the weights multiplies that colour's monochromatic
amplitude by the perturbation raised to the number of edges in a matching. -/
theorem amplitude_perturb_unused (W A : Sym2 (V × C) → R) (k : C) (t : R)
    (hW : ∀ u v : V, W s((u, k), (v, k)) = 0) (m : ℕ)
    (hcard : ∀ σ ∈ pairings V, (edges σ).card = m) :
    amplitude (fun e => W e + t * A e) (Amplitude.const k)
      = t ^ m * amplitude A (Amplitude.const k) := by
  classical
  rw [amplitude, amplitude, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hstep : ∀ e ∈ edges σ,
      (W (Sym2.map (paint (Amplitude.const k)) e) + t * A (Sym2.map (paint (Amplitude.const k)) e))
        = t * A (Sym2.map (paint (Amplitude.const k)) e) := by
    intro e he
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
    have : W (Sym2.map (paint (Amplitude.const k)) s(x, σ x)) = 0 := hW x (σ x)
    rw [this, zero_add]
  rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, Finset.prod_const, hcard σ hσ]

end UnusedColour
/-! ### Degeneracy from the matching relation, independently of caps

Where a non-constant colouring admits exactly two compatible matchings, their products
are negatives of one another.  When the two differ by a single alternating four-cycle
the surviving equation involves four weights and nothing else, and it is quadratic: one
block times another, plus a third times a fourth.

Read at fixed colours on two of the four sites and varying colours on the other two, that
equation says a block is an outer product.  This is a source of block degeneracy that owes
nothing to the contraction framework — it comes from the parity of matchings — which is
what the cap route was missing.
-/

section RelationDegeneracy

variable {V C : Type*} {K : Type*} [Field K]

/-- **A quadratic matching relation factors a block.**

If, at fixed colours on two sites, a block's entries satisfy the four-weight relation for
every choice of colours on the other two, then that block is an outer product: its
entries are a function of the first colour times a function of the second.

The hypothesis is what the two-matching relation supplies when the matchings differ by an
alternating four-cycle and the shared part of their products does not vanish. -/
theorem block_factors_of_relation (W : Sym2 (V × C) → K) (a b c d : V) (α β : C)
    (hK : W s((a, α), (b, β)) ≠ 0)
    (hrel : ∀ γ δ : C,
      W s((a, α), (b, β)) * W s((c, γ), (d, δ))
        + W s((a, α), (c, γ)) * W s((b, β), (d, δ)) = 0) :
    ∃ u v : C → K, ∀ γ δ : C, W s((c, γ), (d, δ)) = u γ * v δ := by
  refine ⟨fun γ => -W s((a, α), (c, γ)) / W s((a, α), (b, β)),
          fun δ => W s((b, β), (d, δ)), fun γ δ => ?_⟩
  have h := hrel γ δ
  field_simp
  linear_combination h


/-- **The relation identifies the four-vertex matching sum.**

The four-weight equation from two compatible matchings says the matching sum over the
four sites they disagree on equals its third term alone — the term belonging to the
pairing neither matching uses.  If that pairing is itself incompatible, the four-vertex
matching sum vanishes outright.

This is where two independent lines meet.  The contraction framework arrives at the
four-vertex matching sum as the coefficient obstructing second-order absorption; the
parity of matchings arrives at it as the quantity a two-matching colouring annihilates.
They are the same object, reached without either route assuming the other. -/
theorem fourSum_eq_third (W : Sym2 (V × C) → K) (a b c d : V) (α β γ δ : C)
    (hrel : W s((a, α), (b, β)) * W s((c, γ), (d, δ))
      + W s((a, α), (c, γ)) * W s((b, β), (d, δ)) = 0) :
    W s((a, α), (b, β)) * W s((c, γ), (d, δ))
      + W s((a, α), (c, γ)) * W s((b, β), (d, δ))
      + W s((a, α), (d, δ)) * W s((b, β), (c, γ))
      = W s((a, α), (d, δ)) * W s((b, β), (c, γ)) := by
  rw [hrel, zero_add]

/-- With the third pairing incompatible as well, the four-vertex matching sum is zero. -/
theorem fourSum_eq_zero (W : Sym2 (V × C) → K) (a b c d : V) (α β γ δ : C)
    (hrel : W s((a, α), (b, β)) * W s((c, γ), (d, δ))
      + W s((a, α), (c, γ)) * W s((b, β), (d, δ)) = 0)
    (hthird : W s((a, α), (d, δ)) * W s((b, β), (c, γ)) = 0) :
    W s((a, α), (b, β)) * W s((c, γ), (d, δ))
      + W s((a, α), (c, γ)) * W s((b, β), (d, δ))
      + W s((a, α), (d, δ)) * W s((b, β), (c, γ)) = 0 := by
  rw [fourSum_eq_third W a b c d α β γ δ hrel, hthird]

end RelationDegeneracy
/-- Two vectors in a space of three colours admit a nonzero common annihilator: fewer
vectors than dimensions always do. -/
theorem exists_annihilator_of_two {K : Type*} [Field K] {C : Type*} [Fintype C]
    [DecidableEq C] (e : Fin 2 → C → K) (hlt : 2 < Fintype.card C) :
    ∃ lam : C → K, lam ≠ 0 ∧ ∀ i : Fin 2, ∑ d, lam d * e i d = 0 := by
  obtain ⟨lam, hne, hker, -⟩ :=
    exists_left_null_of_few_terms_strong (K := K) (C := C) (m := 2)
      (fun _ _ => 0) e (fun _ => 0) (fun d e' => by simp) hlt
  exact ⟨lam, hne, hker⟩
/-- **A dependent triple with an independent tail puts the head in the tail's span.**

If three vectors are dependent and the last two are independent, the first is a
combination of them: the coefficient on the first cannot vanish, since that would make
the last two dependent.

This is what turns the determinantal constraint into a membership statement.  At a site
whose live neighbour's column joins two independent columns from the others, that column
lies in the plane the others span. -/
theorem head_in_span_of_dep {K : Type*} [Field K] {C : Type*}
    (a b c : C → K) (f : Fin 3 → K)
    (hdep : ∀ j : C, f 0 * a j + f 1 * b j + f 2 * c j = 0)
    (hbc : ∀ s t : K, (∀ j : C, s * b j + t * c j = 0) → s = 0 ∧ t = 0)
    (hf : f ≠ 0) :
    ∃ s t : K, ∀ j : C, a j = s * b j + t * c j := by
  classical
  have hf0 : f 0 ≠ 0 := by
    intro h0
    have hbc' : ∀ j : C, f 1 * b j + f 2 * c j = 0 := by
      intro j
      have := hdep j
      rw [h0, zero_mul, zero_add] at this
      exact this
    obtain ⟨h1, h2⟩ := hbc (f 1) (f 2) hbc'
    exact hf (funext fun i => by fin_cases i <;> assumption)
  refine ⟨-(f 1) / f 0, -(f 2) / f 0, fun j => ?_⟩
  have h := hdep j
  field_simp
  linear_combination h

end MatchingBlockRank
