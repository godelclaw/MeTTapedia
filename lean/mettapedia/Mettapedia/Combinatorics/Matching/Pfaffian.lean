import Mathlib
import Mettapedia.Combinatorics.Matching.Sum

/-!
# Signed matching sums

Order the sites linearly.  The *signed matching sum* of a set `S` expands at its smallest site
`m`: each partner `v` contributes the weight of `mv` times the signed sum of the rest, with the
sign `(-1) ^ (pos S v + 1)`, where `pos S v` counts the sites of `S` below `v`.

Read the weight of a pair as the entry, from its smaller site to its larger one, of a skew
matrix.  The signed matching sum is then that matrix's Pfaffian: the unsigned matching sum
`pmSum` with each matching counted with its sign.

The recursion is stated at the smallest site only.  `pfSum_expand` shows it holds at every site,
with the sign `(-1) ^ (pos S u + pos S v + 1)`: expanding twice, at the smallest site and at `u`,
gives the same double sum.
-/

namespace MatchingPfaffian

open Amplitude MatchingSum

variable {V C : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {R : Type*} [CommRing R]

/-- The number of sites of `S` below `x`. -/
def pos (S : Finset V) (x : V) : ℕ := (S.filter (· < x)).card

/-- **The signed matching sum**, expanded at the smallest site. -/
noncomputable def pfSum (W : Sym2 (V × C) → R) (c : V → C) (S : Finset V) : R :=
  if h : S.Nonempty then
    ∑ v ∈ S.erase (S.min' h),
      (-1) ^ (pos S v + 1) * W (Sym2.map (paint c) s(S.min' h, v)) *
        pfSum W c ((S.erase (S.min' h)).erase v)
  else 1
termination_by S.card
decreasing_by
  exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem (S.min'_mem h))

omit [Fintype V] in
@[simp] theorem pfSum_empty (W : Sym2 (V × C) → R) (c : V → C) : pfSum W c ∅ = 1 := by
  rw [pfSum, dif_neg Finset.not_nonempty_empty]

omit [Fintype V] in
/-- The defining recursion, at the smallest site `u` of `S`. -/
theorem pfSum_min (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V} {u : V} (hu : u ∈ S)
    (hmin : ∀ w ∈ S, u ≤ w) :
    pfSum W c S = ∑ v ∈ S.erase u,
      (-1) ^ (pos S v + 1) * W (Sym2.map (paint c) s(u, v)) * pfSum W c ((S.erase u).erase v) := by
  have h : S.Nonempty := ⟨u, hu⟩
  have hm : S.min' h = u := le_antisymm (Finset.min'_le S u hu) (hmin _ (S.min'_mem h))
  rw [pfSum, dif_pos h, hm]

/-! ### Positions -/

omit [Fintype V] [DecidableEq V] in
theorem pos_eq_zero_of_min {S : Finset V} {u : V} (hmin : ∀ w ∈ S, u ≤ w) : pos S u = 0 := by
  rw [pos, Finset.card_eq_zero]
  refine Finset.filter_eq_empty_iff.mpr fun w hw hlt => ?_
  exact absurd (hmin w hw) (not_le.mpr hlt)

omit [Fintype V] in
/-- Deleting a site `y` of `S` lowers the position of every site above it by one. -/
theorem pos_erase {S : Finset V} {y : V} (hy : y ∈ S) (x : V) :
    pos S x = pos (S.erase y) x + if y < x then 1 else 0 := by
  rw [pos, pos, Finset.filter_erase]
  split_ifs with hyx
  · rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hy, hyx⟩)]
    have : 0 < (S.filter (· < x)).card := Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hyx⟩⟩
    omega
  · have hy' : y ∉ S.filter (· < x) := fun h => hyx (Finset.mem_filter.mp h).2
    rw [Finset.erase_eq_of_notMem hy', add_zero]

/-- Two signs agree when their exponents have the same parity. -/
theorem neg_one_pow_congr {a b : ℕ} (h : a % 2 = b % 2) : ((-1 : R) ^ a) = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

/-! ### Parity and locality -/

omit [Fintype V] in
/-- An odd set has signed matching sum zero. -/
theorem pfSum_of_odd (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V} (hS : ¬ Even S.card) :
    pfSum W c S = 0 := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  have hne : S.Nonempty := Finset.card_pos.mp (by
    rcases Nat.eq_zero_or_pos S.card with h0 | h0
    · exact absurd (h0 ▸ (⟨0, rfl⟩ : Even 0)) hS
    · exact h0)
  rw [pfSum, dif_pos hne]
  refine Finset.sum_eq_zero fun v hv => ?_
  have hm := S.min'_mem hne
  have hcard : ((S.erase (S.min' hne)).erase v).card + 2 = S.card := by
    rw [Finset.card_erase_of_mem hv, Finset.card_erase_of_mem hm]
    have : 2 ≤ S.card := by
      have := Finset.card_erase_of_mem hm
      have : 0 < (S.erase (S.min' hne)).card := Finset.card_pos.mpr ⟨v, hv⟩
      omega
    omega
  rw [ih _ (by omega) (fun h => hS (by rw [← hcard]; exact h.add even_two)) rfl, mul_zero]

omit [Fintype V] in
/-- **Locality.**  The signed matching sum over `S` sees only the weights of pairs inside `S`. -/
theorem pfSum_congr (W W' : Sym2 (V × C) → R) (c : V → C) {S : Finset V}
    (h : ∀ x ∈ S, ∀ y ∈ S,
      W (Sym2.map (paint c) s(x, y)) = W' (Sym2.map (paint c) s(x, y))) :
    pfSum W c S = pfSum W' c S := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  by_cases hne : S.Nonempty
  · rw [pfSum, dif_pos hne, pfSum, dif_pos hne]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hm := S.min'_mem hne
    have hvS : v ∈ S := Finset.mem_of_mem_erase hv
    have hsub : (S.erase (S.min' hne)).erase v ⊆ S := fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    have hlt : ((S.erase (S.min' hne)).erase v).card < n := by
      rw [← hn]
      exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hm)
    rw [h _ hm _ hvS, ih _ hlt (fun x hx y hy => h x (hsub hx) y (hsub hy)) rfl]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp

omit [Fintype V] in
/-- **Locality in the colouring.** -/
theorem pfSum_congr_colour (W : Sym2 (V × C) → R) {c c' : V → C} {S : Finset V}
    (h : ∀ x ∈ S, c x = c' x) : pfSum W c S = pfSum W c' S := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  by_cases hne : S.Nonempty
  · rw [pfSum, dif_pos hne, pfSum, dif_pos hne]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hm := S.min'_mem hne
    have hvS : v ∈ S := Finset.mem_of_mem_erase hv
    have hsub : (S.erase (S.min' hne)).erase v ⊆ S := fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    have hlt : ((S.erase (S.min' hne)).erase v).card < n := by
      rw [← hn]
      exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hm)
    have hw : W (Sym2.map (paint c) s(S.min' hne, v)) = W (Sym2.map (paint c') s(S.min' hne, v)) := by
      show W s((S.min' hne, c (S.min' hne)), (v, c v)) = W s((S.min' hne, c' (S.min' hne)), (v, c' v))
      rw [h _ hm, h _ hvS]
    rw [hw, ih _ hlt (fun x hx => h x (hsub hx)) rfl]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp

/-! ### Expansion at any site -/

omit [Fintype V] [LinearOrder V] in
theorem erase_erase_comm (S : Finset V) (a b : V) : (S.erase a).erase b = (S.erase b).erase a :=
  Finset.erase_right_comm

omit [Fintype V] [LinearOrder V] in
/-- Swapping the two indices of a sum over ordered pairs of distinct elements. -/
theorem sum_sum_erase_swap {M : Type*} [AddCommMonoid M] (B : Finset V) (G : V → V → M) :
    ∑ x ∈ B, ∑ y ∈ B.erase x, G x y = ∑ y ∈ B, ∑ x ∈ B.erase y, G x y := by
  refine Finset.sum_comm' fun x y => ?_
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hx, hyx, hy⟩; exact ⟨⟨fun h => hyx h.symm, hx⟩, hy⟩
  · rintro ⟨⟨hxy, hx⟩, hy⟩; exact ⟨hx, fun h => hxy h.symm, hy⟩

omit [Fintype V] in
/-- **Expansion at any site.**  The recursion holds at every site `u` of `S`, with the sign
`(-1) ^ (pos S u + pos S v + 1)`.  Expanding at the smallest site and then at `u` gives the same
double sum as expanding in the other order; the two signs differ by
`[w < u] + [u < w] + [w < v] + [v < w] = 2`. -/
theorem pfSum_expand (W : Sym2 (V × C) → R) (c : V → C) {S : Finset V} {u : V} (hu : u ∈ S) :
    pfSum W c S = ∑ v ∈ S.erase u,
      (-1) ^ (pos S u + pos S v + 1) * W (Sym2.map (paint c) s(u, v)) *
        pfSum W c ((S.erase u).erase v) := by
  induction hn : S.card using Nat.strong_induction_on generalizing S u with
  | _ n ih =>
  have hne : S.Nonempty := ⟨u, hu⟩
  set m := S.min' hne with hmdef
  have hm : m ∈ S := S.min'_mem hne
  have hmin : ∀ w ∈ S, m ≤ w := fun w hw => Finset.min'_le S w hw
  by_cases hum : u = m
  · subst hum
    rw [pfSum_min W c hu hmin, pos_eq_zero_of_min hmin]
    simp only [zero_add]
  have hmu : m < u := lt_of_le_of_ne (hmin u hu) (Ne.symm hum)
  -- the left side, expanded at the smallest site
  rw [pfSum_min W c hm hmin]
  have huS : u ∈ S.erase m := Finset.mem_erase.mpr ⟨hum, hu⟩
  have hmS : m ∈ S.erase u := Finset.mem_erase.mpr ⟨fun h => hum h.symm, hm⟩
  set T := (S.erase m).erase u with hT
  have hTu : (S.erase u).erase m = T := erase_erase_comm S u m
  rw [← Finset.add_sum_erase _ _ huS, ← Finset.add_sum_erase _ _ hmS, hTu]
  congr 1
  · -- the term pairing `m` with `u`
    have hsw : Sym2.map (paint c) s(u, m) = Sym2.map (paint c) s(m, u) := by rw [Sym2.eq_swap]
    rw [pos_eq_zero_of_min hmin, add_zero, hsw]
  · -- both sides are one double sum over distinct `w, v` in `T`, up to the sign
    set D : V → V → Finset V := fun w v => (((S.erase m).erase w).erase u).erase v with hD
    have hL : ∀ w ∈ T,
        (-1 : R) ^ (pos S w + 1) * W (Sym2.map (paint c) s(m, w)) * pfSum W c ((S.erase m).erase w)
          = ∑ v ∈ T.erase w, (-1) ^ (pos S w + 1 + (pos ((S.erase m).erase w) u +
              pos ((S.erase m).erase w) v + 1)) *
              (W (Sym2.map (paint c) s(m, w)) * W (Sym2.map (paint c) s(u, v)) * pfSum W c (D w v)) := by
      intro w hw
      have hwu : w ≠ u := (Finset.mem_erase.mp hw).1
      have hu' : u ∈ (S.erase m).erase w := Finset.mem_erase.mpr ⟨fun h => hwu h.symm, huS⟩
      have hlt : ((S.erase m).erase w).card < n := by
        rw [← hn]
        exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hm)
      rw [ih _ hlt hu' rfl, Finset.mul_sum]
      have hset : ((S.erase m).erase w).erase u = T.erase w := erase_erase_comm _ _ _
      rw [hset]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hfin : (T.erase w).erase v = D w v := by
        simp only [hD, hT]; ext x; simp only [Finset.mem_erase]; tauto
      rw [hfin, pow_add (-1 : R) (pos S w + 1)]
      ring
    have hR : ∀ v ∈ T,
        (-1 : R) ^ (pos S u + pos S v + 1) * W (Sym2.map (paint c) s(u, v)) *
            pfSum W c ((S.erase u).erase v)
          = ∑ w ∈ T.erase v, (-1) ^ (pos S u + pos S v + 1 + (pos ((S.erase u).erase v) w + 1)) *
              (W (Sym2.map (paint c) s(m, w)) * W (Sym2.map (paint c) s(u, v)) * pfSum W c (D w v)) := by
      intro v hv
      have hvm : v ≠ m := fun h => by
        rw [h, hT] at hv; simp at hv
      have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
      have hmS' : m ∈ S.erase u := hmS
      have hm' : m ∈ (S.erase u).erase v :=
        Finset.mem_erase.mpr ⟨fun h => hvm h.symm, hmS'⟩
      have hmin' : ∀ w ∈ (S.erase u).erase v, m ≤ w := fun w hw =>
        hmin w (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))
      rw [pfSum_min W c hm' hmin', Finset.mul_sum]
      have hset : ((S.erase u).erase v).erase m = T.erase v := by
        rw [hT]; ext x; simp only [Finset.mem_erase]; tauto
      rw [hset]
      refine Finset.sum_congr rfl fun w _ => ?_
      have hfin : (T.erase v).erase w = D w v := by
        simp only [hD, hT]; ext x; simp only [Finset.mem_erase]; tauto
      rw [hfin, pow_add (-1 : R) (pos S u + pos S v + 1)]
      ring
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
    refine Eq.trans ?_ (sum_sum_erase_swap T _).symm
    refine Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun v hv => ?_
    congr 1
    -- the parity bookkeeping
    have hwu : w ≠ u := (Finset.mem_erase.mp hw).1
    have hwS : w ∈ S.erase m := Finset.mem_of_mem_erase hw
    have hwm : w ≠ m := (Finset.mem_erase.mp hwS).1
    have hw' : w ∈ S := Finset.mem_of_mem_erase hwS
    have hvw : v ≠ w := (Finset.mem_erase.mp hv).1
    have hvT : v ∈ T := Finset.mem_of_mem_erase hv
    have hvu : v ≠ u := (Finset.mem_erase.mp hvT).1
    have hvS : v ∈ S.erase m := Finset.mem_of_mem_erase hvT
    have hvm : v ≠ m := (Finset.mem_erase.mp hvS).1
    have hv' : v ∈ S := Finset.mem_of_mem_erase hvS
    have hmw : m < w := lt_of_le_of_ne (hmin w hw') (Ne.symm hwm)
    have hmv : m < v := lt_of_le_of_ne (hmin v hv') (Ne.symm hvm)
    have e1 := pos_erase hm u
    have e2 := pos_erase (Finset.mem_erase.mpr ⟨hwm, hw'⟩) u
    have e3 := pos_erase hm v
    have e4 := pos_erase (Finset.mem_erase.mpr ⟨hwm, hw'⟩) v
    have e5 := pos_erase hu w
    have e6 := pos_erase (Finset.mem_erase.mpr ⟨hvu, hv'⟩) w
    rw [if_pos hmu] at e1
    rw [if_pos hmv] at e3
    apply neg_one_pow_congr
    rcases lt_or_gt_of_ne hwu with h1 | h1 <;> rcases lt_or_gt_of_ne hvw with h2 | h2
    · rw [if_pos h1] at e2; rw [if_neg (not_lt.mpr h1.le)] at e5
      rw [if_neg (not_lt.mpr h2.le)] at e4; rw [if_pos h2] at e6
      omega
    · rw [if_pos h1] at e2; rw [if_neg (not_lt.mpr h1.le)] at e5
      rw [if_pos h2] at e4; rw [if_neg (not_lt.mpr h2.le)] at e6
      omega
    · rw [if_neg (not_lt.mpr h1.le)] at e2; rw [if_pos h1] at e5
      rw [if_neg (not_lt.mpr h2.le)] at e4; rw [if_pos h2] at e6
      omega
    · rw [if_neg (not_lt.mpr h1.le)] at e2; rw [if_pos h1] at e5
      rw [if_pos h2] at e4; rw [if_neg (not_lt.mpr h2.le)] at e6
      omega

end MatchingPfaffian
