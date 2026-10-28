import Mathlib
import Mettapedia.Combinatorics.Matching.PfaffianUpdate
import Mettapedia.Combinatorics.Matching.BlockRank
import Mettapedia.Combinatorics.Matching.CharTwoContraction

/-!
# Contracting a pair of sites of a signed matching sum

Fix two pivot sites `p ≠ q` and cap their colours with `κ` and `μ`.  The capped signed matching
sum of a set `S` with the two pivots added, `capPf`, is a signed matching sum on `S` alone: that
of the updated weights `a · W - P ⊗ Q + Q ⊗ P`, where `P` and `Q` are the oriented weights with
which the pivots reach a site and `a` is the oriented cap value on the pivot pair
(`capVal_mul_pfSum_update_eq_cap`).  The only price is a power of `a` and a global sign.

This is the Pfaffian's Schur complement at a pair of sites, and it holds over every commutative
ring.  The unsigned matching sum satisfies it only when `2 = 0` (`MatchingCharTwo`).  There the
terms that use a pivot twice cancel because they come in pairs; here the members of each pair
carry opposite signs.
-/

namespace MatchingPfaffian

open Amplitude MatchingSum MatchingBlockRank

variable {V C : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] [Fintype C]
  {R : Type*} [CommRing R]

section Cap

variable (W : Sym2 (V × C) → R) (p q : V) (κ μ : C → R)

/-- The sign of the pair `x, y` read from `x` to `y`: `1` if `x < y`, `-1` otherwise. -/
def orient (x y : V) : R := (-1) ^ (if y < x then 1 else 0)

/-- The oriented weight with which the pivot `p`, capped with `κ`, reaches `v` coloured `α'`. -/
def profile (p : V) (κ : C → R) (v : V) (α' : C) : R :=
  orient p v * ∑ α, κ α * W s((p, α), (v, α'))

/-- The oriented cap value on the pivot pair. -/
def capVal : R := orient p q * ∑ α, ∑ β, κ α * μ β * W s((p, α), (q, β))

/-- The capped signed matching sum of `S` with the two pivots added. -/
noncomputable def capPf (c : V → C) (S : Finset V) : R :=
  ∑ α, ∑ β, κ α * μ β * pfSum W (paintTwo c p q α β) (insert p (insert q S))

end Cap

omit [Fintype V] [DecidableEq V] [Fintype C] in
/-- Inserting a site `x` not in `S` raises the position of every site above it by one. -/
theorem pos_insert [DecidableEq V] {S : Finset V} {x : V} (hx : x ∉ S) (y : V) :
    pos (insert x S) y = pos S y + if x < y then 1 else 0 := by
  have := pos_erase (Finset.mem_insert_self x S) y
  rwa [Finset.erase_insert hx] at this

omit [Fintype V] in
/-- **The capped sum at the two pivots.**  Expanding at `p` and then at `q` writes the capped
signed matching sum as the cap value times the signed matching sum of `S`, plus the terms in which
each pivot reaches a site of `S`, all up to the global sign `(-1) ^ (pos S p + pos S q + [q < p])`. -/
theorem capPf_eq (W : Sym2 (V × C) → R) {p q : V} (κ μ : C → R) (c : V → C) {S : Finset V}
    (hpq : p ≠ q) (hp : p ∉ S) (hq : q ∉ S) :
    capPf W p q κ μ c S
      = (-1) ^ (pos S p + pos S q + if q < p then 1 else 0) *
          (capVal W p q κ μ * pfSum W c S + reach W (profile W p κ) (profile W q μ) c S) := by
  classical
  have hpqS : p ∉ insert q S := by
    simp only [Finset.mem_insert, not_or]; exact ⟨hpq, hp⟩
  -- position bookkeeping
  have ep : pos (insert p (insert q S)) p = pos S p + if q < p then 1 else 0 := by
    rw [pos_insert hpqS, pos_insert hq, if_neg (lt_irrefl p)]; omega
  have eq' : pos (insert p (insert q S)) q = pos S q + if p < q then 1 else 0 := by
    rw [pos_insert hpqS, pos_insert hq, if_neg (lt_irrefl q)]; omega
  have ev : ∀ v, pos (insert p (insert q S)) v
      = pos S v + (if q < v then 1 else 0) + if p < v then 1 else 0 := fun v => by
    rw [pos_insert hpqS, pos_insert hq]
  -- the sign of a reached pair, as the expansion produces it
  set E : V → V → ℕ := fun v l => pos S p + (if q < p then 1 else 0) + (pos S v +
      (if q < v then 1 else 0) + (if p < v then 1 else 0)) + 1 +
        (pos (insert q (S.erase v)) q + pos (insert q (S.erase v)) l + 1) with hE
  set M : V → V → R := fun v l => (-1) ^ E v l * pfSum W c ((S.erase v).erase l) with hM
  -- the expansion of one capped term
  have hterm : ∀ α β, pfSum W (paintTwo c p q α β) (insert p (insert q S))
      = (-1) ^ (pos S p + (if q < p then 1 else 0) + (pos S q + (if p < q then 1 else 0)) + 1) *
          W s((p, α), (q, β)) * pfSum W c S
        + ∑ v ∈ S, W s((p, α), (v, c v)) * ∑ l ∈ S.erase v, W s((q, β), (l, c l)) * M v l := by
    intro α β
    set c' := paintTwo c p q α β with hc'
    have hc'p : c' p = α := paintTwo_fst c hpq α β
    have hc'q : c' q = β := paintTwo_snd c p q α β
    have hc'S : ∀ x ∈ S, c' x = c x := fun x hx =>
      paintTwo_other c (fun h => hp (by rw [← h]; exact hx)) (fun h => hq (by rw [← h]; exact hx)) α β
    rw [pfSum_expand W c' (Finset.mem_insert_self p (insert q S)), Finset.erase_insert hpqS,
      Finset.sum_insert hq]
    congr 1
    · rw [ep, eq', Finset.erase_insert hq, pfSum_congr_colour W hc'S]
      show _ * W s((p, c' p), (q, c' q)) * _ = _
      rw [hc'p, hc'q]
    · refine Finset.sum_congr rfl fun v hv => ?_
      have hvq : v ≠ q := fun h => hq (h ▸ hv)
      have hqS' : q ∉ S.erase v := fun h => hq (Finset.mem_of_mem_erase h)
      rw [ep, ev v, show (insert q S).erase v = insert q (S.erase v) from
          Finset.erase_insert_of_ne hvq.symm,
        pfSum_expand W c' (Finset.mem_insert_self q (S.erase v)), Finset.erase_insert hqS',
        Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hlS : l ∈ S := Finset.mem_of_mem_erase hl
      have hsub : ∀ x ∈ (S.erase v).erase l, c' x = c x := fun x hx =>
        hc'S x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      rw [pfSum_congr_colour W hsub]
      show _ * W s((p, c' p), (v, c' v)) * (_ * W s((q, c' q), (l, c' l)) * _) = _
      rw [hc'p, hc'q, hc'S v hv, hc'S l hlS]
      simp only [hM, hE]
      rw [pow_add (-1 : R) (pos S p + (if q < p then 1 else 0) + (pos S v + (if q < v then 1 else 0) +
        (if p < v then 1 else 0)) + 1)]
      ring
  -- sum the capped terms
  unfold capPf
  simp_rw [hterm, mul_add, Finset.sum_add_distrib]
  rw [MatchingCharTwo.sum_cap_rearrange κ μ S (fun α v => W s((p, α), (v, c v)))
    (fun β l => W s((q, β), (l, c l))) M]
  congr 1
  · -- the pivot pair
    unfold capVal orient
    have hs : (-1 : R) ^ (pos S p + (if q < p then 1 else 0) + (pos S q + (if p < q then 1 else 0)) + 1)
        = (-1) ^ (pos S p + pos S q + if q < p then 1 else 0) * (-1) ^ (if q < p then 1 else 0) := by
      rw [← pow_add]
      apply neg_one_pow_congr
      rcases lt_or_gt_of_ne hpq with h | h
      · rw [if_pos h, if_neg (not_lt.mpr h.le)]; omega
      · rw [if_neg (not_lt.mpr h.le), if_pos h]; omega
    simp only [hs, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    ring
  · -- the reached sites
    unfold reach profile orient
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlS : l ∈ S := Finset.mem_of_mem_erase hl
    have hlv : l ≠ v := (Finset.mem_erase.mp hl).1
    have hvq : v ≠ q := fun h => hq (h ▸ hv)
    have hvp : v ≠ p := fun h => hp (h ▸ hv)
    have hlq : l ≠ q := fun h => hq (h ▸ hlS)
    have hqS' : q ∉ S.erase v := fun h => hq (Finset.mem_of_mem_erase h)
    have e1 := pos_insert hqS' q
    have e2 := pos_insert hqS' l
    have e3 := pos_erase hv q
    have e4 := pos_erase hv l
    rw [if_neg (lt_irrefl q)] at e1
    have hsign : (-1 : R) ^ E v l
        = (-1) ^ (pos S p + pos S q + (if q < p then 1 else 0)) *
            ((-1) ^ (1 + pos S v + pos S l + (if v < l then 1 else 0)) *
              (-1) ^ (if v < p then 1 else 0) * (-1) ^ (if l < q then 1 else 0)) := by
      simp only [hE]
      rw [← pow_add, ← pow_add, ← pow_add]
      apply neg_one_pow_congr
      rw [e1, e2]
      rcases lt_or_gt_of_ne hvp with h1 | h1 <;> rcases lt_or_gt_of_ne hvq with h2 | h2 <;>
        rcases lt_or_gt_of_ne hlq with h3 | h3 <;> rcases lt_or_gt_of_ne hlv with h4 | h4 <;>
        simp only [h1, h2, h3, h4, if_true, not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr h3.le,
          not_lt.mpr h4.le, if_false] at e3 e4 ⊢ <;> omega
    simp only [hM]
    rw [hsign]
    ring

omit [Fintype V] in
/-- **The signed contraction.**  The capped signed matching sum of `S` with the pivots added is,
up to a power of the oriented cap value and a global sign, the signed matching sum of `S` for the
updated weights.  An identity over every commutative ring. -/
theorem capVal_mul_pfSum_update_eq_cap (W : Sym2 (V × C) → R) {p q : V} (κ μ : C → R)
    (c : V → C) {S : Finset V} (hpq : p ≠ q) (hp : p ∉ S) (hq : q ∉ S) :
    capVal W p q κ μ * pfSum (update W (profile W p κ) (profile W q μ) (capVal W p q κ μ)) c S
      = (-1) ^ (pos S p + pos S q + if q < p then 1 else 0) * capVal W p q κ μ ^ (S.card / 2) *
          capPf W p q κ μ c S := by
  rw [a_mul_pfSum_update, capPf_eq W κ μ c hpq hp hq]
  have hsq : ((-1 : R) ^ (pos S p + pos S q + if q < p then 1 else 0)) *
      (-1) ^ (pos S p + pos S q + if q < p then 1 else 0) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc capVal W p q κ μ ^ (S.card / 2) * (capVal W p q κ μ * pfSum W c S +
          reach W (profile W p κ) (profile W q μ) c S)
      = ((-1 : R) ^ (pos S p + pos S q + if q < p then 1 else 0) *
          (-1) ^ (pos S p + pos S q + if q < p then 1 else 0)) *
            (capVal W p q κ μ ^ (S.card / 2) * (capVal W p q κ μ * pfSum W c S +
              reach W (profile W p κ) (profile W q μ) c S)) := by rw [hsq, one_mul]
    _ = _ := by ring

end MatchingPfaffian
