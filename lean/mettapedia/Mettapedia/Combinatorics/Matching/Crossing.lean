import Mettapedia.Combinatorics.Matching.Sum

/-!
# Crossing identities for weighted perfect-matching sums

A nonzero direct pairing inside a vanishing matching sum must be cancelled by a
crossing term. This module packages the two-pivot expansion, the forced crossing,
its finite descent, and the sharp obstruction at the empty crowd. All statements
are independent of any particular matching problem.
-/

namespace MatchingCrossing

open Amplitude MatchingSum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The two-pivot expansion and the forced crossing

Adjoin two fresh sites to a set and expand the matching sum at each in turn.  Every matching either
pairs the two new sites with each other -- leaving a matching of the old set -- or sends them to two
distinct old sites, leaving a matching of what remains.  That is the identity below, proved from the
one-site expansion and set bookkeeping alone; no determinant-style hafnian identity is used or
needed.

Its consequence over a field is the crossing lemma.  If the direct term is non-zero and the whole
sum vanishes, the double sum cannot be zero termwise, so *some* crossing survives: two distinct old
sites, live edges to them from the two new ones, and a non-zero sum on the smaller remainder.  A
vanishing total forces a crossing rather than merely permitting one. -/

section TwoPivot

variable {C : Type*} {R : Type*} [CommSemiring R]

/-- **Two-pivot expansion.**  Adjoining `u` and `v` to `A`: the direct pairing, plus every way of
sending `u` and `v` to two distinct sites of `A`. -/
theorem pmSum_insert_pair (W : Sym2 (V × C) → R) (d : V → C) {A : Finset V} {u v : V}
    (hu : u ∉ A) (hv : v ∉ A) (huv : u ≠ v) :
    pmSum W d (insert u (insert v A))
      = W (Sym2.map (paint d) s(u, v)) * pmSum W d A
        + ∑ x ∈ A, W (Sym2.map (paint d) s(u, x)) *
            ∑ y ∈ A.erase x, W (Sym2.map (paint d) s(v, y)) *
              pmSum W d ((A.erase x).erase y) := by
  classical
  have hunotin : u ∉ insert v A := by
    simp only [Finset.mem_insert]
    exact fun h => h.elim huv (fun h' => hu h')
  have h1 : (insert u (insert v A)).erase u = insert v A := Finset.erase_insert hunotin
  have h2 : (insert v A).erase v = A := Finset.erase_insert hv
  rw [pmSum_expand W d (Finset.mem_insert_self u (insert v A)), h1,
    ← Finset.add_sum_erase _ _ (Finset.mem_insert_self v A), h2]
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxv : x ≠ v := fun h => hv (h ▸ hx)
  have h3 : (insert v A).erase x = insert v (A.erase x) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hzx, hz | hz⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hzx, hz⟩
    · rintro (rfl | ⟨hzx, hz⟩)
      · exact ⟨fun h => hxv h.symm, Or.inl rfl⟩
      · exact ⟨hzx, Or.inr hz⟩
  have hvnot : v ∉ A.erase x := fun h => hv (Finset.mem_of_mem_erase h)
  rw [h3, pmSum_expand W d (Finset.mem_insert_self v (A.erase x)),
    Finset.erase_insert hvnot, Finset.mul_sum]

end TwoPivot

/-- **The forced crossing.**  A vanishing total with a non-zero direct term produces a crossing:
distinct `x, y` in `A` with live edges `u–x` and `v–y` and a surviving remainder. -/
theorem exists_crossing {C R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R) (d : V → C) {A : Finset V} {u v : V}
    (hu : u ∉ A) (hv : v ∉ A) (huv : u ≠ v)
    (hdirect : W (Sym2.map (paint d) s(u, v)) ≠ 0)
    (hA : pmSum W d A ≠ 0)
    (hzero : pmSum W d (insert u (insert v A)) = 0) :
    ∃ x ∈ A, ∃ y ∈ A.erase x,
      W (Sym2.map (paint d) s(u, x)) ≠ 0 ∧ W (Sym2.map (paint d) s(v, y)) ≠ 0 ∧
        pmSum W d ((A.erase x).erase y) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hsum : ∑ x ∈ A, W (Sym2.map (paint d) s(u, x)) *
      ∑ y ∈ A.erase x, W (Sym2.map (paint d) s(v, y)) *
        pmSum W d ((A.erase x).erase y) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    by_cases hux : W (Sym2.map (paint d) s(u, x)) = 0
    · rw [hux, zero_mul]
    · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y hy => ?_)
      by_cases hvy : W (Sym2.map (paint d) s(v, y)) = 0
      · rw [hvy, zero_mul]
      · rw [hcon x hx y hy hux hvy, mul_zero]
  rw [pmSum_insert_pair W d hu hv huv, hsum, add_zero] at hzero
  exact (mul_ne_zero hdirect hA) hzero

/-- The crowd is not a single site: a forced crossing needs two distinct targets. -/
theorem two_le_card_of_crossing {C R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R) (d : V → C) {A : Finset V}
    {u v : V} (hu : u ∉ A) (hv : v ∉ A) (huv : u ≠ v)
    (hdirect : W (Sym2.map (paint d) s(u, v)) ≠ 0)
    (hA : pmSum W d A ≠ 0)
    (hzero : pmSum W d (insert u (insert v A)) = 0) :
    2 ≤ A.card := by
  obtain ⟨x, hx, y, hy, -, -, -⟩ := exists_crossing W d hu hv huv hdirect hA hzero
  exact Finset.one_lt_card.mpr ⟨y, Finset.mem_of_mem_erase hy, x, hx,
    (Finset.mem_erase.mp hy).1⟩

/-- **The size-two case is the four-site permanent relation.**  With the crowd a single pair, the
two-pivot expansion is exactly the three-term hafnian of four sites. -/
theorem pmSum_insert_pair_two {C R : Type*} [CommSemiring R] (W : Sym2 (V × C) → R)
    (d : V → C) {u v x y : V} (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    (huv : u ≠ v) (hxy : x ≠ y) :
    pmSum W d (insert u (insert v ({x, y} : Finset V)))
      = W (Sym2.map (paint d) s(u, v)) * W (Sym2.map (paint d) s(x, y))
        + W (Sym2.map (paint d) s(u, x)) * W (Sym2.map (paint d) s(v, y))
        + W (Sym2.map (paint d) s(u, y)) * W (Sym2.map (paint d) s(v, x)) := by
  classical
  have hu : u ∉ ({x, y} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim hux huy
  have hv : v ∉ ({x, y} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim hvx hvy
  rw [pmSum_insert_pair W d hu hv huv]
  have hpair : pmSum W d ({x, y} : Finset V) = W (Sym2.map (paint d) s(x, y)) := by
    rw [show (Sym2.map (paint d)) s(x, y) = s((x, d x), (y, d y)) from rfl]
    exact MatchingSum.pmSum_pair W d (Ne.symm hxy)
  rw [hpair, Finset.sum_pair hxy]
  have hex : ({x, y} : Finset V).erase x = ({y} : Finset V) := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl⟩
      · exact absurd rfl hz
      · rfl
    · rintro rfl; exact ⟨fun h => hxy h.symm, Or.inr rfl⟩
  have hey : ({x, y} : Finset V).erase y = ({x} : Finset V) := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl⟩
      · rfl
      · exact absurd rfl hz
    · rintro rfl; exact ⟨hxy, Or.inl rfl⟩
  rw [hex, hey, Finset.sum_singleton, Finset.sum_singleton,
    Finset.erase_singleton, Finset.erase_singleton]
  simp only [pmSum_empty]
  ring

/-- If one of the three pairings of four distinct vertices has zero weight,
the four-vertex matching sum is the sum of the other two products. -/
theorem pmSum_four_two_terms {C R : Type*} [CommSemiring R]
    (W : Sym2 (V × C) → R) (d : V → C)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hdead : W (Sym2.map (paint d) s(a, b)) = 0) :
    pmSum W d ({a, b, x, y} : Finset V)
      = W (Sym2.map (paint d) s(a, x)) * W (Sym2.map (paint d) s(b, y))
        + W (Sym2.map (paint d) s(a, y)) * W (Sym2.map (paint d) s(b, x)) := by
  rw [show ({a, b, x, y} : Finset V) = insert a (insert b ({x, y} : Finset V)) from rfl,
    pmSum_insert_pair_two W d hax hay hbx hby hab hxy, hdead, zero_mul, zero_add]

/-! ## The naive same-colour transition is not available

`excess_site_crossing_certificate` leaves the shrunk crowd `A ∖ {x,y}` certified, but supplies no
vanishing extension of it.  The naive transition -- that some live pair extends the shrunk crowd to
a vanishing sum, giving back a state of the same shape two sites smaller -- is not merely unproved.
At the base case it is false for *every* weight function: a pair-extension of the empty crowd is its
own weight, so it vanishes exactly when the pair is dead.  The failure is therefore structural, not
a matter of a missing estimate: the crossing fields alone carry no partition data, and a vanishing
matching sum can only come from a partition. -/

/-- A live pair on the empty crowd never vanishes. -/
theorem pmSum_live_pair_ne_zero {C R : Type*} [CommSemiring R] (W : Sym2 (V × C) → R)
    (d : V → C) {p q : V} (hpq : p ≠ q)
    (hlive : W (Sym2.map (paint d) s(p, q)) ≠ 0) :
    pmSum W d (insert p (insert q (∅ : Finset V))) ≠ 0 := by
  have h : (insert p (insert q (∅ : Finset V))) = ({p, q} : Finset V) := rfl
  rw [h, MatchingSum.pmSum_pair W d (Ne.symm hpq)]
  exact hlive

/-- No crossing state has an empty crowd: the direct term alone would be the whole sum. -/
theorem no_crossing_state_at_zero {C R : Type*} [CommSemiring R]
    (W : Sym2 (V × C) → R) (d : V → C)
    {u v : V} (huv : u ≠ v)
    (hdirect : W (Sym2.map (paint d) s(u, v)) ≠ 0)
    (hzero : pmSum W d (insert u (insert v (∅ : Finset V))) = 0) : False :=
  pmSum_live_pair_ne_zero W d huv hdirect hzero

/-- **The obstruction.**  With a two-site crowd the crossing empties it, and then *no* live pair
whatever extends the result to a vanishing sum.  So a transition law phrased in the crossing fields
alone cannot close: the state must be enriched. -/
theorem crossing_transport_obstruction {C R : Type*}
    [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R) (d : V → C)
    {A : Finset V} {u v : V} (hu : u ∉ A) (hv : v ∉ A) (huv : u ≠ v)
    (hdirect : W (Sym2.map (paint d) s(u, v)) ≠ 0)
    (hA : pmSum W d A ≠ 0)
    (hzero : pmSum W d (insert u (insert v A)) = 0)
    (hcard : A.card = 2) :
    ∃ x ∈ A, ∃ y ∈ A.erase x,
      W (Sym2.map (paint d) s(u, x)) ≠ 0 ∧ W (Sym2.map (paint d) s(v, y)) ≠ 0 ∧
        pmSum W d ((A.erase x).erase y) ≠ 0 ∧
        (A.erase x).erase y = ∅ ∧
        ∀ p q : V, p ≠ q → W (Sym2.map (paint d) s(p, q)) ≠ 0 →
          pmSum W d (insert p (insert q ((A.erase x).erase y))) ≠ 0 := by
  obtain ⟨x, hx, y, hy, hux, hvy, hrem⟩ := exists_crossing W d hu hv huv hdirect hA hzero
  have hemp : (A.erase x).erase y = ∅ := by
    have h1 : (A.erase x).card = 1 := by rw [Finset.card_erase_of_mem hx, hcard]
    have h2 : ((A.erase x).erase y).card = 0 := by rw [Finset.card_erase_of_mem hy, h1]
    exact Finset.card_eq_zero.mp h2
  refine ⟨x, hx, y, hy, hux, hvy, hrem, hemp, ?_⟩
  intro p q hpq hlive
  rw [hemp]
  exact pmSum_live_pair_ne_zero W d hpq hlive

/-- A weight function on four sites realizing the crossing state with a two-site crowd, so the
obstruction above is not vacuous.  The entry depends only on the sum of the two indices, which makes
it symmetric with no case analysis. -/
noncomputable def crossingWitness : Sym2 (Fin 4 × Unit) → ℂ :=
  Sym2.lift ⟨fun p q => if p.1.val + q.1.val = 3 then 0
                        else if p.1.val + q.1.val = 4 then -1 else 1,
    by intro a b; simp only [Nat.add_comm]⟩

theorem crossing_state_at_two_nonvacuous :
    ∃ (W : Sym2 (Fin 4 × Unit) → ℂ) (d : Fin 4 → Unit) (A : Finset (Fin 4)) (u v : Fin 4),
      u ∉ A ∧ v ∉ A ∧ u ≠ v ∧
        W (Sym2.map (paint d) s(u, v)) ≠ 0 ∧
        pmSum W d A ≠ 0 ∧
        pmSum W d (insert u (insert v A)) = 0 ∧
        A.card = 2 := by
  refine ⟨crossingWitness, fun _ => (), ({2, 3} : Finset (Fin 4)), 0, 1, by decide, by decide,
    by decide, ?_, ?_, ?_, by decide⟩
  · show crossingWitness s(((0 : Fin 4), ()), ((1 : Fin 4), ())) ≠ 0
    norm_num [crossingWitness, Sym2.lift_mk]
  · rw [MatchingSum.pmSum_pair crossingWitness (fun _ => ()) (by decide : (3 : Fin 4) ≠ 2)]
    show crossingWitness s(((2 : Fin 4), ()), ((3 : Fin 4), ())) ≠ 0
    norm_num [crossingWitness, Sym2.lift_mk]
  · rw [pmSum_insert_pair_two crossingWitness (fun _ => ()) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    show crossingWitness s(((0 : Fin 4), ()), ((1 : Fin 4), ())) *
        crossingWitness s(((2 : Fin 4), ()), ((3 : Fin 4), ())) +
      crossingWitness s(((0 : Fin 4), ()), ((2 : Fin 4), ())) *
        crossingWitness s(((1 : Fin 4), ()), ((3 : Fin 4), ())) +
      crossingWitness s(((0 : Fin 4), ()), ((3 : Fin 4), ())) *
        crossingWitness s(((1 : Fin 4), ()), ((2 : Fin 4), ())) = 0
    norm_num [crossingWitness, Sym2.lift_mk]

/-- **The descent branch is a genuine state.**  If the shrunk crowd does carry a vanishing extension
by the same live pair, the crossing fires again on a crowd exactly two sites smaller -- and the
original crowd had at least four sites. -/
theorem crossing_descent_step {C R : Type*}
    [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R) (d : V → C) {A : Finset V}
    {u v x y : V} (hu : u ∉ A) (hv : v ∉ A) (huv : u ≠ v)
    (hdirect : W (Sym2.map (paint d) s(u, v)) ≠ 0)
    (hx : x ∈ A) (hy : y ∈ A.erase x)
    (hrem : pmSum W d ((A.erase x).erase y) ≠ 0)
    (hdesc : pmSum W d (insert u (insert v ((A.erase x).erase y))) = 0) :
    (∃ x' ∈ (A.erase x).erase y, ∃ y' ∈ ((A.erase x).erase y).erase x',
      W (Sym2.map (paint d) s(u, x')) ≠ 0 ∧ W (Sym2.map (paint d) s(v, y')) ≠ 0 ∧
        pmSum W d ((((A.erase x).erase y).erase x').erase y') ≠ 0)
      ∧ ((A.erase x).erase y).card = A.card - 2 ∧ 4 ≤ A.card := by
  have hu' : u ∉ (A.erase x).erase y := fun h =>
    hu (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hv' : v ∉ (A.erase x).erase y := fun h =>
    hv (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hcross := exists_crossing W d hu' hv' huv hdirect hrem hdesc
  have hcard2 := two_le_card_of_crossing W d hu' hv' huv hdirect hrem hdesc
  have h1 : (A.erase x).card = A.card - 1 := Finset.card_erase_of_mem hx
  have h2 : ((A.erase x).erase y).card = (A.erase x).card - 1 := Finset.card_erase_of_mem hy
  refine ⟨hcross, by omega, by omega⟩


/-- A four-set whose matching is forced: with two of the three options at `a` dead, the sum
collapses to one product. -/
theorem pmSum_quad_forced {D R : Type*} [CommSemiring R]
    (W : Sym2 (V × D) → R) (c : V → D)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hdb : W (Sym2.map (paint c) s(a, b)) = 0)
    (hdy : W (Sym2.map (paint c) s(a, y)) = 0) :
    pmSum W c ({a, b, x, y} : Finset V)
      = W (Sym2.map (paint c) s(a, x)) * W (Sym2.map (paint c) s(b, y)) := by
  classical
  have ha : a ∈ ({a, b, x, y} : Finset V) := by simp
  have hxmem : x ∈ ({a, b, x, y} : Finset V).erase a := by
    refine Finset.mem_erase.mpr ⟨Ne.symm hax, by simp⟩
  have hset : ((({a, b, x, y} : Finset V).erase a).erase x) = ({b, y} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzx, hza, h⟩
      rcases h with rfl | rfl | rfl | rfl
      · exact absurd rfl hza
      · exact Or.inl rfl
      · exact absurd rfl hzx
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hbx, Ne.symm hab, by simp⟩
      · exact ⟨Ne.symm hxy, Ne.symm hay, by simp⟩
  have huniq : ∀ z ∈ ({a, b, x, y} : Finset V).erase a, z ≠ x →
      W (Sym2.map (paint c) s(a, z)) = 0 := by
    intro z hz hzx
    rcases Finset.mem_erase.mp hz with ⟨hza, hzmem⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
    rcases hzmem with rfl | rfl | rfl | rfl
    · exact absurd rfl hza
    · exact hdb
    · exact absurd rfl hzx
    · exact hdy
  rw [pmSum_of_forced W c ha hxmem huniq, hset, pmSum_pair W c (Ne.symm hby)]
  rfl


/-! ### Certificates inside a vanishing set

A site of a set whose matching sum vanishes cannot have exactly one partner whose
complement inside the set carries a nonzero sum: expansion at that site would
leave a single nonzero term. Thus every site has either no certified partner or
at least two.
-/

/-- **No site of a vanishing set has exactly one certified partner in it.** -/
theorem no_lone_certified_in_vanishing {C R : Type*}
    [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R) (c : V → C)
    {S : Finset V} (hS : pmSum W c S = 0) {x w₀ : V} (hx : x ∈ S) (hw : w₀ ∈ S.erase x)
    (hlive : W (Sym2.map (paint c) s(x, w₀)) ≠ 0)
    (hcert : pmSum W c ((S.erase x).erase w₀) ≠ 0)
    (hlone : ∀ w ∈ S.erase x, w ≠ w₀ →
      W (Sym2.map (paint c) s(x, w)) * pmSum W c ((S.erase x).erase w) = 0) :
    False := by
  classical
  rw [pmSum_expand W c hx, Finset.sum_eq_single_of_mem w₀ hw hlone] at hS
  exact (mul_ne_zero hlive hcert) hS

/-- **Two certified partners, or none.**  The contrapositive, in the form the fibre analysis
uses. -/
theorem two_or_no_certified_in_vanishing {C R : Type*}
    [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    (W : Sym2 (V × C) → R) (c : V → C)
    {S : Finset V} (hS : pmSum W c S = 0) {x w₀ : V} (hx : x ∈ S) (hw : w₀ ∈ S.erase x)
    (hlive : W (Sym2.map (paint c) s(x, w₀)) ≠ 0)
    (hcert : pmSum W c ((S.erase x).erase w₀) ≠ 0) :
    ∃ w ∈ S.erase x, w ≠ w₀ ∧
      W (Sym2.map (paint c) s(x, w)) ≠ 0 ∧
      pmSum W c ((S.erase x).erase w) ≠ 0 := by
  classical
  by_contra hno
  push Not at hno
  refine no_lone_certified_in_vanishing W c hS hx hw hlive hcert (fun w hwS hwne => ?_)
  by_cases h1 : W (Sym2.map (paint c) s(x, w)) = 0
  · rw [h1, zero_mul]
  · rw [hno w hwS hwne h1, mul_zero]


/-- Expanding a six-vertex matching sum whose three distinguished pair
weights vanish leaves the eight cross-pairing products. -/
theorem pmSum_six_three_dead {C R : Type*} [CommRing R]
    (W : Sym2 (V × C) → R) (c : V → C)
    {u₁ u₂ v₁ v₂ w₁ w₂ : V}
    (h12 : u₁ ≠ u₂) (h1v1 : u₁ ≠ v₁) (h1v2 : u₁ ≠ v₂) (h1w1 : u₁ ≠ w₁) (h1w2 : u₁ ≠ w₂)
    (h2v1 : u₂ ≠ v₁) (h2v2 : u₂ ≠ v₂) (h2w1 : u₂ ≠ w₁) (h2w2 : u₂ ≠ w₂)
    (hv : v₁ ≠ v₂) (hv1w1 : v₁ ≠ w₁) (hv1w2 : v₁ ≠ w₂)
    (hv2w1 : v₂ ≠ w₁) (hv2w2 : v₂ ≠ w₂) (hw : w₁ ≠ w₂)
    (hdu : W (Sym2.map (paint c) s(u₁, u₂)) = 0)
    (hdv : W (Sym2.map (paint c) s(v₁, v₂)) = 0)
    (hdw : W (Sym2.map (paint c) s(w₁, w₂)) = 0) :
    pmSum W c ({u₁, u₂, v₁, v₂, w₁, w₂} : Finset V)
      = W (Sym2.map (paint c) s(u₁, v₁))
          * (W (Sym2.map (paint c) s(w₁, u₂))
              * W (Sym2.map (paint c) s(w₂, v₂))
            + W (Sym2.map (paint c) s(w₁, v₂))
              * W (Sym2.map (paint c) s(w₂, u₂)))
        + W (Sym2.map (paint c) s(u₁, v₂))
          * (W (Sym2.map (paint c) s(w₁, u₂))
              * W (Sym2.map (paint c) s(w₂, v₁))
            + W (Sym2.map (paint c) s(w₁, v₁))
              * W (Sym2.map (paint c) s(w₂, u₂)))
        + (W (Sym2.map (paint c) s(u₁, w₁))
          * (W (Sym2.map (paint c) s(v₁, u₂))
              * W (Sym2.map (paint c) s(v₂, w₂))
            + W (Sym2.map (paint c) s(v₁, w₂))
              * W (Sym2.map (paint c) s(v₂, u₂)))
        + W (Sym2.map (paint c) s(u₁, w₂))
          * (W (Sym2.map (paint c) s(v₁, u₂))
              * W (Sym2.map (paint c) s(v₂, w₁))
            + W (Sym2.map (paint c) s(v₁, w₁))
              * W (Sym2.map (paint c) s(v₂, u₂)))) := by
  classical
  have hu₁ : u₁ ∈ ({u₁, u₂, v₁, v₂, w₁, w₂} : Finset V) := by simp
  have her : ({u₁, u₂, v₁, v₂, w₁, w₂} : Finset V).erase u₁ = ({u₂, v₁, v₂, w₁, w₂} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl | rfl | rfl | rfl⟩
      exacts [absurd rfl hz, by simp, by simp, by simp, by simp, by simp]
    · rintro (rfl | rfl | rfl | rfl | rfl)
      exacts [⟨Ne.symm h12, by simp⟩, ⟨Ne.symm h1v1, by simp⟩, ⟨Ne.symm h1v2, by simp⟩,
        ⟨Ne.symm h1w1, by simp⟩, ⟨Ne.symm h1w2, by simp⟩]
  have e1 : ({u₂, v₁, v₂, w₁, w₂} : Finset V).erase v₁ = ({w₁, w₂, u₂, v₂} : Finset V) := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl | rfl | rfl⟩
      exacts [by simp, absurd rfl hz, by simp, by simp, by simp]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨Ne.symm hv1w1, by simp⟩, ⟨Ne.symm hv1w2, by simp⟩, ⟨h2v1, by simp⟩,
        ⟨Ne.symm hv, by simp⟩]
  have e2 : ({u₂, v₁, v₂, w₁, w₂} : Finset V).erase v₂ = ({w₁, w₂, u₂, v₁} : Finset V) := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl | rfl | rfl⟩
      exacts [by simp, by simp, absurd rfl hz, by simp, by simp]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨Ne.symm hv2w1, by simp⟩, ⟨Ne.symm hv2w2, by simp⟩, ⟨h2v2, by simp⟩,
        ⟨hv, by simp⟩]
  have e3 : ({u₂, v₁, v₂, w₁, w₂} : Finset V).erase w₁ = ({v₁, v₂, u₂, w₂} : Finset V) := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl | rfl | rfl⟩
      exacts [by simp, by simp, by simp, absurd rfl hz, by simp]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨hv1w1, by simp⟩, ⟨hv2w1, by simp⟩, ⟨h2w1, by simp⟩, ⟨Ne.symm hw, by simp⟩]
  have e4 : ({u₂, v₁, v₂, w₁, w₂} : Finset V).erase w₂ = ({v₁, v₂, u₂, w₁} : Finset V) := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl | rfl | rfl⟩
      exacts [by simp, by simp, by simp, by simp, absurd rfl hz]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨hv1w2, by simp⟩, ⟨hv2w2, by simp⟩, ⟨h2w2, by simp⟩, ⟨hw, by simp⟩]
  have e0 : ({u₂, v₁, v₂, w₁, w₂} : Finset V).erase u₂ = ({v₁, v₂, w₁, w₂} : Finset V) := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl | rfl | rfl⟩
      exacts [absurd rfl hz, by simp, by simp, by simp, by simp]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨Ne.symm h2v1, by simp⟩, ⟨Ne.symm h2v2, by simp⟩, ⟨Ne.symm h2w1, by simp⟩,
        ⟨Ne.symm h2w2, by simp⟩]
  rw [pmSum_expand W c hu₁, her]
  rw [show ({u₂, v₁, v₂, w₁, w₂} : Finset V) = insert u₂ (insert v₁ (insert v₂ (insert w₁ {w₂})))
    from rfl]
  rw [Finset.sum_insert (by simp [h2v1, h2v2, h2w1, h2w2]),
    Finset.sum_insert (by simp [hv, hv1w1, hv1w2]),
    Finset.sum_insert (by simp [hv2w1, hv2w2]),
    Finset.sum_insert (by simp [hw]), Finset.sum_singleton]
  rw [e0, e1, e2, e3, e4, hdu, zero_mul, zero_add]
  rw [pmSum_four_two_terms W c hw (Ne.symm h2w1) (Ne.symm hv2w1) (Ne.symm h2w2)
      (Ne.symm hv2w2) h2v2 hdw,
    pmSum_four_two_terms W c hw (Ne.symm h2w1) (Ne.symm hv1w1) (Ne.symm h2w2)
      (Ne.symm hv1w2) h2v1 hdw,
    pmSum_four_two_terms W c hv (Ne.symm h2v1) hv1w2
      (Ne.symm h2v2) hv2w2 h2w2 hdv,
    pmSum_four_two_terms W c hv (Ne.symm h2v1) hv1w1
      (Ne.symm h2v2) hv2w1 h2w1 hdv]
  ring

/-! ### Routing a dead pair inside a set

A pair whose own edge is dead still has to be covered by a non-vanishing matching sum on any set
containing it, and it cannot be covered by joining the two sites to each other.  So the sum routes
them through two *other* sites of the set, and the certified-deletion step supplies a remainder that
still does not vanish.  Two applications of the partner lemma; no field, no enumeration, and no
hypothesis beyond a commutative semiring. -/

theorem exists_dead_pair_detour_on {C : Type*} {R : Type*} [CommSemiring R]
    (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V} {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) (hS : pmSum W c S ≠ 0)
    (hdead : W (Sym2.map (paint c) s(u, v)) = 0) :
    ∃ x y : V, x ∈ S ∧ y ∈ S ∧
      x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v ∧ x ≠ y ∧
      W (Sym2.map (paint c) s(u, x)) ≠ 0 ∧ W (Sym2.map (paint c) s(v, y)) ≠ 0 ∧
      pmSum W c (S \ ({u, x, v, y} : Finset V)) ≠ 0 := by
  classical
  obtain ⟨x, hx, hux, hrest⟩ := MatchingSum.exists_partner_ne_zero W c hu hS
  have hxu : x ≠ u := Finset.ne_of_mem_erase hx
  have hxS : x ∈ S := Finset.mem_of_mem_erase hx
  have hxv : x ≠ v := by
    intro h; rw [h] at hux; exact hux hdead
  have hvmem : v ∈ (S.erase u).erase x :=
    Finset.mem_erase.mpr ⟨Ne.symm hxv, Finset.mem_erase.mpr ⟨Ne.symm huv, hv⟩⟩
  obtain ⟨y, hy, hvy, hrest'⟩ := MatchingSum.exists_partner_ne_zero W c hvmem hrest
  have hyv : y ≠ v := Finset.ne_of_mem_erase hy
  have hyx : y ≠ x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)
  have hyu : y ≠ u :=
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
  have hyS : y ∈ S :=
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
  refine ⟨x, y, hxS, hyS, hxu, hxv, hyu, hyv, Ne.symm hyx, hux, hvy, ?_⟩
  have hset : S \ ({u, x, v, y} : Finset V) = (((S.erase u).erase x).erase v).erase y := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, not_or]
    tauto
  rw [hset]; exact hrest'

/-- Four distinct sites of `S` are exhibited, so a dead pair inside a non-vanishing sum needs at
least four sites. -/
theorem four_le_card_of_dead_pair_detour {C : Type*} {R : Type*} [CommSemiring R]
    (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V} {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) (hS : pmSum W c S ≠ 0)
    (hdead : W (Sym2.map (paint c) s(u, v)) = 0) :
    4 ≤ S.card := by
  classical
  obtain ⟨x, y, hxS, hyS, hxu, hxv, hyu, hyv, hxy, -, -, -⟩ :=
    exists_dead_pair_detour_on W c hu hv huv hS hdead
  have hsub : ({u, x, v, y} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({u, x, v, y} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hxu, huv, Ne.symm hyu⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxv, hxy⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]; exact Ne.symm hyv),
      Finset.card_singleton]
  exact hcard ▸ Finset.card_le_card hsub

/-- Base behaviour at two sites: a dead pair is the whole sum, so the hypotheses are contradictory. -/
theorem dead_pair_detour_card_two {C : Type*} {R : Type*} [CommSemiring R]
    (W : Sym2 (V × C) → R) (c : V → C) {u v : V} (huv : u ≠ v)
    (hS : pmSum W c ({u, v} : Finset V) ≠ 0)
    (hdead : W (Sym2.map (paint c) s(u, v)) = 0) : False := by
  rw [MatchingSum.pmSum_pair W c (Ne.symm huv)] at hS
  exact hS hdead

/-- Base behaviour at four sites: the detour exhausts the set and the remainder is empty. -/
theorem dead_pair_detour_card_four {C : Type*} {R : Type*} [CommSemiring R]
    (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V} {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) (hS : pmSum W c S ≠ 0)
    (hdead : W (Sym2.map (paint c) s(u, v)) = 0) (hcard : S.card = 4) :
    ∃ x y : V, x ∈ S ∧ y ∈ S ∧
      x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v ∧ x ≠ y ∧
      W (Sym2.map (paint c) s(u, x)) ≠ 0 ∧ W (Sym2.map (paint c) s(v, y)) ≠ 0 ∧
      S \ ({u, x, v, y} : Finset V) = (∅ : Finset V) := by
  classical
  obtain ⟨x, y, hxS, hyS, hxu, hxv, hyu, hyv, hxy, hux, hvy, -⟩ :=
    exists_dead_pair_detour_on W c hu hv huv hS hdead
  refine ⟨x, y, hxS, hyS, hxu, hxv, hyu, hyv, hxy, hux, hvy, ?_⟩
  have hsub : ({u, x, v, y} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hc4 : ({u, x, v, y} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hxu, huv, Ne.symm hyu⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxv, hxy⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]; exact Ne.symm hyv),
      Finset.card_singleton]
  have heq : ({u, x, v, y} : Finset V) = S := Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [heq, Finset.sdiff_self]

end MatchingCrossing
