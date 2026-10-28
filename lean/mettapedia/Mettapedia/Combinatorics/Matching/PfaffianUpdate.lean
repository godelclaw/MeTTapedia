import Mathlib
import Mettapedia.Combinatorics.Matching.Pfaffian

/-!
# A rank-two update of a signed matching sum

Add to `a · W` the rank-two part `-P ⊗ Q + Q ⊗ P`, read from the smaller site to the larger.  The
signed matching sum of the result is `a ^ (|S|/2 - 1)` times the signed matching sum of `W`,
corrected by the terms in which the rank-two part is used exactly once
(`a_mul_pfSum_update`).  The matchings that use it twice cancel in pairs, each against the one with
two indices swapped, which carries the opposite sign.  The identity therefore holds over every
commutative ring.

The unsigned matching sum has no such identity: there the doubly used terms add up instead of
cancelling, and only vanish when `2 = 0`.
-/

namespace MatchingPfaffian

open Amplitude MatchingSum

variable {V C : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {R : Type*} [CommRing R]

section Update

variable (W : Sym2 (V × C) → R) (P Q : V → C → R) (a : R)

/-- The rank-two part, from the site `x` coloured `α` to the site `y` coloured `β`. -/
def rankTwo (x : V) (α : C) (y : V) (β : C) : R := - P x α * Q y β + Q x α * P y β

/-- The updated weight of a pair, oriented by the order of the sites. -/
def updateFun (e f : V × C) : R :=
  a * W s(e, f) +
    if e.1 < f.1 then rankTwo P Q e.1 e.2 f.1 f.2
    else if f.1 < e.1 then rankTwo P Q f.1 f.2 e.1 e.2 else 0

omit [Fintype V] [DecidableEq V] in
theorem updateFun_comm (e f : V × C) : updateFun W P Q a e f = updateFun W P Q a f e := by
  unfold updateFun
  rw [Sym2.eq_swap]
  congr 1
  by_cases h1 : e.1 < f.1
  · rw [if_pos h1, if_neg (not_lt.mpr h1.le), if_pos h1]
  · by_cases h2 : f.1 < e.1
    · rw [if_neg h1, if_pos h2, if_pos h2]
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

/-- **The updated weights** `a · W - P ⊗ Q + Q ⊗ P`. -/
def update : Sym2 (V × C) → R := Sym2.lift ⟨updateFun W P Q a, updateFun_comm W P Q a⟩

omit [Fintype V] [DecidableEq V] in
theorem update_of_lt {x y : V} (hxy : x < y) (α β : C) :
    update W P Q a s((x, α), (y, β)) = a * W s((x, α), (y, β)) + rankTwo P Q x α y β := by
  show updateFun W P Q a (x, α) (y, β) = _
  unfold updateFun
  rw [if_pos hxy]

/-- The matchings that use the rank-two part once: `x` reached through `P`, `y` through `Q`. -/
noncomputable def reach (c : V → C) (S : Finset V) : R :=
  ∑ x ∈ S, ∑ y ∈ S.erase x,
    (-1) ^ (1 + pos S x + pos S y + if x < y then 1 else 0) * P x (c x) * Q y (c y) *
      pfSum W c ((S.erase x).erase y)

end Update

/-! ### Sums over ordered pairs and triples of distinct sites -/

omit [Fintype V] [LinearOrder V] in
/-- **An antisymmetric sum over ordered pairs vanishes.**  Each term cancels against the one
with the two indices swapped. -/
theorem sum_sum_erase_antisymm (B : Finset V) (G : V → V → R) (hG : ∀ x y, G y x = - G x y) :
    ∑ x ∈ B, ∑ y ∈ B.erase x, G x y = 0 := by
  rw [← Finset.sum_sigma (s := B) (t := fun x => B.erase x) (f := fun z => G z.1 z.2)]
  refine Finset.sum_involution (fun z _ => ⟨z.2, z.1⟩) ?_ ?_ ?_ ?_
  · intro z _
    show G z.1 z.2 + G z.2 z.1 = 0
    rw [hG z.1 z.2, add_neg_cancel]
  · intro z hz _ h
    have hmem := Finset.mem_sigma.mp hz
    exact (Finset.mem_erase.mp hmem.2).1 (congrArg Sigma.fst h)
  · intro z hz
    have hmem := Finset.mem_sigma.mp hz
    obtain ⟨hyx, hy⟩ := Finset.mem_erase.mp hmem.2
    exact Finset.mem_sigma.mpr ⟨hy, Finset.mem_erase.mpr ⟨fun h => hyx h.symm, hmem.1⟩⟩
  · intro z _
    rfl

omit [Fintype V] [LinearOrder V] in
/-- Moving the last index of a sum over ordered triples of distinct elements to the front. -/
theorem sum_triple_rotate {M : Type*} [AddCommMonoid M] (A : Finset V) (G : V → V → V → M) :
    ∑ x ∈ A, ∑ y ∈ A.erase x, ∑ w ∈ (A.erase x).erase y, G x y w
      = ∑ w ∈ A, ∑ x ∈ A.erase w, ∑ y ∈ (A.erase w).erase x, G x y w := by
  have h1 : ∀ x ∈ A, ∑ y ∈ A.erase x, ∑ w ∈ (A.erase x).erase y, G x y w
      = ∑ w ∈ A.erase x, ∑ y ∈ (A.erase x).erase w, G x y w := fun x _ =>
    sum_sum_erase_swap (A.erase x) (fun y w => G x y w)
  rw [Finset.sum_congr rfl h1, sum_sum_erase_swap A (fun x w => ∑ y ∈ (A.erase x).erase w, G x y w)]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => ?_
  rw [erase_erase_comm A x w]

/-! ### The reach term -/

section Reach

variable (W : Sym2 (V × C) → R) (P Q : V → C → R) (c : V → C)

omit [Fintype V] in
theorem reach_of_odd {S : Finset V} (hS : ¬ Even S.card) : reach W P Q c S = 0 := by
  refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
  have hcard : ((S.erase x).erase y).card + 2 = S.card := by
    rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx]
    have : 0 < (S.erase x).card := Finset.card_pos.mpr ⟨y, hy⟩
    have := Finset.card_erase_of_mem hx
    omega
  rw [pfSum_of_odd W c (fun h => hS (by rw [← hcard]; exact h.add even_two)), mul_zero]

omit [Fintype V] in
@[simp] theorem reach_empty : reach W P Q c ∅ = 0 := by
  simp [reach]

omit [Fintype V] in
/-- **The reach term at the smallest site.**  Either a pivot reaches the smallest site `u`, or
`u` is matched inside and the reach happens in the rest. -/
theorem reach_expand_min {S : Finset V} {u : V} (hu : u ∈ S) (hmin : ∀ w ∈ S, u ≤ w) :
    reach W P Q c S
      = ∑ v ∈ S.erase u, (-1) ^ (pos S v + 1) * rankTwo P Q u (c u) v (c v) *
          pfSum W c ((S.erase u).erase v)
        + ∑ w ∈ S.erase u, (-1) ^ (pos S w + 1) * W (Sym2.map (paint c) s(u, w)) *
            reach W P Q c ((S.erase u).erase w) := by
  set A := S.erase u with hA
  have hpu : pos S u = 0 := pos_eq_zero_of_min hmin
  have hlt : ∀ x ∈ A, u < x := fun x hx =>
    lt_of_le_of_ne (hmin x (Finset.mem_of_mem_erase hx)) (fun h => (Finset.mem_erase.mp hx).1 h.symm)
  -- split the outer index at `u`, then the inner index at `u`
  unfold reach
  rw [← Finset.add_sum_erase S _ hu, ← hA]
  have hsplit : ∀ x ∈ A,
      ∑ y ∈ S.erase x, (-1 : R) ^ (1 + pos S x + pos S y + if x < y then 1 else 0) * P x (c x) *
          Q y (c y) * pfSum W c ((S.erase x).erase y)
        = (-1) ^ (pos S x + 1) * P x (c x) * Q u (c u) * pfSum W c (A.erase x)
          + ∑ y ∈ A.erase x, ∑ w ∈ (A.erase x).erase y,
              (-1) ^ (1 + pos S x + pos S y + (if x < y then 1 else 0) +
                (pos ((S.erase x).erase y) w + 1)) *
                (P x (c x) * Q y (c y) * W (Sym2.map (paint c) s(u, w)) *
                  pfSum W c ((((A.erase x).erase y).erase w))) := by
    intro x hx
    have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
    have huSx : u ∈ S.erase x := Finset.mem_erase.mpr ⟨fun h => hxu h.symm, hu⟩
    rw [← Finset.add_sum_erase _ _ huSx]
    congr 1
    · rw [hpu, if_neg (not_lt.mpr (hlt x hx).le), erase_erase_comm S x u]
      apply congrArg₂ (· * ·) _ rfl
      rw [show 1 + pos S x + 0 + 0 = pos S x + 1 by omega]
    · have hset : (S.erase x).erase u = A.erase x := erase_erase_comm S x u
      rw [hset]
      refine Finset.sum_congr rfl fun y hy => ?_
      have hyA : y ∈ A := Finset.mem_of_mem_erase hy
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      have huxy : u ∈ (S.erase x).erase y := Finset.mem_erase.mpr ⟨fun h => ?_, huSx⟩
      · have hmin' : ∀ w ∈ (S.erase x).erase y, u ≤ w := fun w hw =>
          hmin w (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))
        rw [pfSum_min W c huxy hmin', Finset.mul_sum]
        have hset2 : ((S.erase x).erase y).erase u = (A.erase x).erase y := by
          rw [hA]; ext z; simp only [Finset.mem_erase]; tauto
        rw [hset2]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [pow_add (-1 : R) (1 + pos S x + pos S y + if x < y then 1 else 0)]
        ring
      · exact (Finset.mem_erase.mp hyA).1 h.symm
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- the terms in which `u` is reached
  have hfirst : ∑ y ∈ A, (-1 : R) ^ (1 + pos S u + pos S y + if u < y then 1 else 0) * P u (c u) *
        Q y (c y) * pfSum W c ((S.erase u).erase y)
      + ∑ x ∈ A, (-1) ^ (pos S x + 1) * P x (c x) * Q u (c u) * pfSum W c (A.erase x)
      = ∑ v ∈ A, (-1) ^ (pos S v + 1) * rankTwo P Q u (c u) v (c v) * pfSum W c (A.erase v) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hpu, if_pos (hlt v hv), ← hA]
    unfold rankTwo
    rw [show 1 + 0 + pos S v + 1 = pos S v + 1 + 1 by omega, pow_succ]
    ring
  rw [← add_assoc, hfirst]
  congr 1
  -- the terms in which `u` is matched inside: reorder the triple sum and compare signs
  rw [sum_triple_rotate A]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hwA := hw
  have hxA : x ∈ A := Finset.mem_of_mem_erase hx
  have hxw : x ≠ w := (Finset.mem_erase.mp hx).1
  have hyA : y ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hyw : y ≠ w := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hy)).1
  have hS : ∀ z ∈ A, z ∈ S := fun z hz => Finset.mem_of_mem_erase hz
  have hset : (((A.erase x).erase y).erase w) = (((A.erase w).erase x).erase y) := by
    ext z; simp only [Finset.mem_erase]; tauto
  rw [hset]
  have hsetA : (S.erase u).erase w = A.erase w := by rw [hA]
  rw [hsetA]
  have hl : (-1 : R) ^ (1 + pos S x + pos S y + (if x < y then 1 else 0) +
        (pos ((S.erase x).erase y) w + 1))
      = (-1) ^ (pos S w + 1) * (-1) ^ (1 + pos (A.erase w) x + pos (A.erase w) y +
          if x < y then 1 else 0) := by
    rw [← pow_add]
    apply neg_one_pow_congr
    have e1 := pos_erase (hS x hxA) w
    have e2 := pos_erase (Finset.mem_erase.mpr ⟨hyx, hS y hyA⟩) w
    have e3 := pos_erase hu x
    have e4 := pos_erase hwA x
    have e5 := pos_erase hu y
    have e6 := pos_erase hwA y
    rw [if_pos (hlt x hxA)] at e3
    rw [if_pos (hlt y hyA)] at e5
    rw [← hA] at e3 e5
    rcases lt_or_gt_of_ne hxw with h1 | h1 <;> rcases lt_or_gt_of_ne hyw with h2 | h2
    · rw [if_pos h1] at e1; rw [if_neg (not_lt.mpr h1.le)] at e4
      rw [if_pos h2] at e2; rw [if_neg (not_lt.mpr h2.le)] at e6
      split_ifs <;> omega
    · rw [if_pos h1] at e1; rw [if_neg (not_lt.mpr h1.le)] at e4
      rw [if_neg (not_lt.mpr h2.le)] at e2; rw [if_pos h2] at e6
      split_ifs <;> omega
    · rw [if_neg (not_lt.mpr h1.le)] at e1; rw [if_pos h1] at e4
      rw [if_pos h2] at e2; rw [if_neg (not_lt.mpr h2.le)] at e6
      split_ifs <;> omega
    · rw [if_neg (not_lt.mpr h1.le)] at e1; rw [if_pos h1] at e4
      rw [if_neg (not_lt.mpr h2.le)] at e2; rw [if_pos h2] at e6
      split_ifs <;> omega
  rw [hl]
  have hsw : ((A.erase w).erase x).erase y = (((A.erase w).erase x).erase y) := rfl
  ring

theorem neg_neg_one_pow (n : ℕ) : -((-1 : R) ^ n) = (-1) ^ (n + 1) := by
  rw [pow_succ]; ring

omit [Fintype V] in
/-- **The rank-two part used twice cancels.**  Expanding a reach term at the smallest site `u`
and letting the rank-two part reach `u` a second time gives terms that cancel in pairs.  Where
`u` meets `Q`, swapping the two `Q`-indices flips the sign; where it meets `P`, swapping the two
`P`-indices does. -/
theorem double_reach_eq_zero {S : Finset V} {u : V} (hu : u ∈ S) (hmin : ∀ w ∈ S, u ≤ w) :
    ∑ v ∈ S.erase u, (-1 : R) ^ (pos S v + 1) * rankTwo P Q u (c u) v (c v) *
      reach W P Q c ((S.erase u).erase v) = 0 := by
  set A := S.erase u with hA
  have hlt : ∀ x ∈ A, u < x := fun x hx =>
    lt_of_le_of_ne (hmin x (Finset.mem_of_mem_erase hx)) (fun h => (Finset.mem_erase.mp hx).1 h.symm)
  have hS : ∀ z ∈ A, z ∈ S := fun z hz => Finset.mem_of_mem_erase hz
  -- the sign of a double reach, as a function of the three reached sites
  set ε : V → V → V → R := fun v x y => (-1) ^ (pos S v + 1) *
    (-1) ^ (1 + pos (A.erase v) x + pos (A.erase v) y + if x < y then 1 else 0) with hε
  set D : V → V → V → Finset V := fun v x y => ((A.erase v).erase x).erase y with hD
  have hDsym1 : ∀ v x y, D x v y = D v x y := fun v x y => by
    simp only [hD]; ext z; simp only [Finset.mem_erase]; tauto
  have hDsym2 : ∀ v x y, D y x v = D v x y := fun v x y => by
    simp only [hD]; ext z; simp only [Finset.mem_erase]; tauto
  -- the parity facts: swapping `v, x` or `v, y` flips the sign
  have hpos : ∀ v ∈ A, ∀ x ∈ A.erase v, pos (A.erase v) x + 1 + (if v < x then 1 else 0) = pos S x := by
    intro v hv x hx
    have e1 := pos_erase hu x
    have e2 := pos_erase hv x
    rw [if_pos (hlt x (Finset.mem_of_mem_erase hx))] at e1
    rw [← hA] at e1
    omega
  have hswap1 : ∀ v ∈ A, ∀ x ∈ A.erase v, ∀ y ∈ (A.erase v).erase x, ε x v y = - ε v x y := by
    intro v hv x hx y hy
    have hxA : x ∈ A := Finset.mem_of_mem_erase hx
    have hvx : v ∈ A.erase x := Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hx).1 h.symm, hv⟩
    have hyA : y ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
    have hyv : y ∈ A.erase v := Finset.mem_of_mem_erase hy
    have hyx : y ∈ A.erase x := Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1, hyA⟩
    have a1 := hpos v hv x hx
    have a2 := hpos v hv y hyv
    have a3 := hpos x hxA v hvx
    have a4 := hpos x hxA y hyx
    simp only [hε]
    rw [← pow_add, ← pow_add, neg_neg_one_pow]
    apply neg_one_pow_congr
    have hvx' : v ≠ x := fun h => (Finset.mem_erase.mp hx).1 h.symm
    have hvy' : v ≠ y := fun h => (Finset.mem_erase.mp hyv).1 h.symm
    have hxy' : x ≠ y := fun h => (Finset.mem_erase.mp hy).1 h.symm
    rcases lt_or_gt_of_ne hvx' with h1 | h1 <;> rcases lt_or_gt_of_ne hvy' with h2 | h2 <;>
      rcases lt_or_gt_of_ne hxy' with h3 | h3 <;>
      simp only [h1, h2, h3, if_true, not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr h3.le,
        if_false] at a1 a2 a3 a4 ⊢ <;> omega
  have hswap2 : ∀ v ∈ A, ∀ x ∈ A.erase v, ∀ y ∈ (A.erase v).erase x, ε y x v = - ε v x y := by
    intro v hv x hx y hy
    have hxA : x ∈ A := Finset.mem_of_mem_erase hx
    have hyA : y ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
    have hyv : y ∈ A.erase v := Finset.mem_of_mem_erase hy
    have hxy : x ∈ A.erase y := Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hy).1 h.symm, hxA⟩
    have hvy : v ∈ A.erase y := Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hyv).1 h.symm, hv⟩
    have a1 := hpos v hv x hx
    have a2 := hpos v hv y hyv
    have a3 := hpos y hyA x hxy
    have a4 := hpos y hyA v hvy
    simp only [hε]
    rw [← pow_add, ← pow_add, neg_neg_one_pow]
    apply neg_one_pow_congr
    have hvx' : v ≠ x := fun h => (Finset.mem_erase.mp hx).1 h.symm
    have hvy' : v ≠ y := fun h => (Finset.mem_erase.mp hyv).1 h.symm
    have hxy' : x ≠ y := fun h => (Finset.mem_erase.mp hy).1 h.symm
    rcases lt_or_gt_of_ne hvx' with h1 | h1 <;> rcases lt_or_gt_of_ne hvy' with h2 | h2 <;>
      rcases lt_or_gt_of_ne hxy' with h3 | h3 <;>
      simp only [h1, h2, h3, if_true, not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr h3.le,
        if_false] at a1 a2 a3 a4 ⊢ <;> omega
  -- write the double reach as two triple sums
  have hexp : ∀ v ∈ A, (-1 : R) ^ (pos S v + 1) * rankTwo P Q u (c u) v (c v) *
      reach W P Q c ((S.erase u).erase v)
        = ∑ x ∈ A.erase v, ∑ y ∈ (A.erase v).erase x,
            (- (ε v x y * (P u (c u) * Q v (c v) * P x (c x) * Q y (c y) * pfSum W c (D v x y)))
              + ε v x y * (Q u (c u) * P v (c v) * P x (c x) * Q y (c y) * pfSum W c (D v x y))) := by
    intro v _
    rw [← hA]
    unfold reach rankTwo
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hε, hD]
    ring
  rw [Finset.sum_congr rfl hexp]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  -- the part through `P u`: antisymmetric in the two `Q`-indices `v, y`
  have hT1 : ∑ v ∈ A, ∑ x ∈ A.erase v, ∑ y ∈ (A.erase v).erase x,
      ε v x y * (P u (c u) * Q v (c v) * P x (c x) * Q y (c y) * pfSum W c (D v x y)) = 0 := by
    rw [sum_sum_erase_swap A (fun v x => ∑ y ∈ (A.erase v).erase x,
      ε v x y * (P u (c u) * Q v (c v) * P x (c x) * Q y (c y) * pfSum W c (D v x y)))]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hset : ∀ v, (A.erase v).erase x = (A.erase x).erase v := fun v => erase_erase_comm A v x
    simp_rw [hset]
    have key := sum_sum_erase_antisymm (A.erase x)
      (fun v y => if v ∈ A.erase x ∧ y ∈ (A.erase x).erase v then
        ε v x y * (P u (c u) * Q v (c v) * P x (c x) * Q y (c y) * pfSum W c (D v x y)) else 0)
      (fun v y => by
        by_cases h : v ∈ A.erase x ∧ y ∈ (A.erase x).erase v
        · have hy' : y ∈ A.erase x := Finset.mem_of_mem_erase h.2
          have hv' : v ∈ (A.erase x).erase y :=
            Finset.mem_erase.mpr ⟨fun e => (Finset.mem_erase.mp h.2).1 e.symm, h.1⟩
          rw [if_pos ⟨hy', hv'⟩, if_pos h]
          have hvA : v ∈ A := Finset.mem_of_mem_erase h.1
          have hxv : x ∈ A.erase v := Finset.mem_erase.mpr ⟨fun e => (Finset.mem_erase.mp h.1).1 e.symm, hx⟩
          have hyvx : y ∈ (A.erase v).erase x := by rw [hset]; exact h.2
          rw [hswap2 v hvA x hxv y hyvx, hDsym2]
          ring
        · rw [if_neg h]
          by_cases h' : y ∈ A.erase x ∧ v ∈ (A.erase x).erase y
          · exfalso
            refine h ⟨Finset.mem_of_mem_erase h'.2, Finset.mem_erase.mpr
              ⟨fun e => (Finset.mem_erase.mp h'.2).1 e.symm, h'.1⟩⟩
          · rw [if_neg h', neg_zero])
    rw [← key]
    refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun y hy => ?_
    rw [if_pos ⟨hv, hy⟩]
  -- the part through `Q u`: antisymmetric in the two `P`-indices `v, x`
  have hT2 : ∑ v ∈ A, ∑ x ∈ A.erase v, ∑ y ∈ (A.erase v).erase x,
      ε v x y * (Q u (c u) * P v (c v) * P x (c x) * Q y (c y) * pfSum W c (D v x y)) = 0 := by
    have key := sum_sum_erase_antisymm A
      (fun v x => if v ∈ A ∧ x ∈ A.erase v then ∑ y ∈ (A.erase v).erase x,
        ε v x y * (Q u (c u) * P v (c v) * P x (c x) * Q y (c y) * pfSum W c (D v x y)) else 0)
      (fun v x => by
        by_cases h : v ∈ A ∧ x ∈ A.erase v
        · have hx' : x ∈ A := Finset.mem_of_mem_erase h.2
          have hv' : v ∈ A.erase x :=
            Finset.mem_erase.mpr ⟨fun e => (Finset.mem_erase.mp h.2).1 e.symm, h.1⟩
          rw [if_pos ⟨hx', hv'⟩, if_pos h, erase_erase_comm A x v, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun y hy => ?_
          rw [hswap1 v h.1 x h.2 y hy, hDsym1]
          ring
        · rw [if_neg h]
          by_cases h' : x ∈ A ∧ v ∈ A.erase x
          · exfalso
            exact h ⟨Finset.mem_of_mem_erase h'.2, Finset.mem_erase.mpr
              ⟨fun e => (Finset.mem_erase.mp h'.2).1 e.symm, h'.1⟩⟩
          · rw [if_neg h', neg_zero])
    rw [← key]
    refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun x hx => ?_
    rw [if_pos ⟨hv, hx⟩]
  rw [hT1, hT2, neg_zero, zero_add]

end Reach

/-! ### The update identity -/

omit [Fintype V] in
/-- **The rank-two update of a signed matching sum.**  With the rank-two part `-P ⊗ Q + Q ⊗ P`
added to `a · W`, the signed matching sum is `a ^ (|S|/2 - 1)` times the signed matching sum of
`W` plus the single-use terms.  An identity over every commutative ring: the doubly used terms
cancel by sign (`double_reach_eq_zero`). -/
theorem a_mul_pfSum_update (W : Sym2 (V × C) → R) (P Q : V → C → R) (a : R) (c : V → C) :
    ∀ S : Finset V, a * pfSum (update W P Q a) c S
      = a ^ (S.card / 2) * (a * pfSum W c S + reach W P Q c S) := by
  intro S
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  by_cases hodd : ¬ Even S.card
  · rw [pfSum_of_odd _ c hodd, pfSum_of_odd _ c hodd, reach_of_odd W P Q c hodd]
    ring
  push Not at hodd
  rcases S.eq_empty_or_nonempty with hS | hne
  · subst hS
    simp at hn
    subst hn
    simp
  set u := S.min' hne with hudef
  have hu : u ∈ S := S.min'_mem hne
  have hmin : ∀ w ∈ S, u ≤ w := fun w hw => Finset.min'_le S w hw
  have hcard : 2 ≤ S.card := by
    obtain ⟨k, hk⟩ := hodd
    have : 0 < S.card := Finset.card_pos.mpr hne
    omega
  rw [pfSum_min _ c hu hmin, Finset.mul_sum]
  have hstep : ∀ v ∈ S.erase u,
      a * ((-1) ^ (pos S v + 1) * update W P Q a (Sym2.map (paint c) s(u, v)) *
          pfSum (update W P Q a) c ((S.erase u).erase v))
        = a ^ ((S.card - 2) / 2) * ((-1) ^ (pos S v + 1) *
            (a * W (Sym2.map (paint c) s(u, v)) + rankTwo P Q u (c u) v (c v)) *
              (a * pfSum W c ((S.erase u).erase v) + reach W P Q c ((S.erase u).erase v))) := by
    intro v hv
    have huv : u < v := lt_of_le_of_ne (hmin v (Finset.mem_of_mem_erase hv))
      (fun h => (Finset.mem_erase.mp hv).1 h.symm)
    have hT : ((S.erase u).erase v).card = S.card - 2 := by
      rw [Finset.card_erase_of_mem hv, Finset.card_erase_of_mem hu]; omega
    have := ih _ (by omega) ((S.erase u).erase v) hT
    have hupd : update W P Q a (Sym2.map (paint c) s(u, v))
        = a * W (Sym2.map (paint c) s(u, v)) + rankTwo P Q u (c u) v (c v) :=
      update_of_lt W P Q a huv (c u) (c v)
    rw [hupd]
    calc a * ((-1) ^ (pos S v + 1) * (a * W (Sym2.map (paint c) s(u, v)) + rankTwo P Q u (c u) v (c v)) *
          pfSum (update W P Q a) c ((S.erase u).erase v))
        = (-1) ^ (pos S v + 1) * (a * W (Sym2.map (paint c) s(u, v)) + rankTwo P Q u (c u) v (c v)) *
            (a * pfSum (update W P Q a) c ((S.erase u).erase v)) := by ring
      _ = _ := by rw [this]; ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  have hkey : ∑ v ∈ S.erase u, (-1 : R) ^ (pos S v + 1) *
        (a * W (Sym2.map (paint c) s(u, v)) + rankTwo P Q u (c u) v (c v)) *
          (a * pfSum W c ((S.erase u).erase v) + reach W P Q c ((S.erase u).erase v))
      = a * (a * pfSum W c S + reach W P Q c S) := by
    have hz := double_reach_eq_zero W P Q c hu hmin
    have hr := reach_expand_min W P Q c hu hmin
    have hp := pfSum_min W c hu hmin
    have hsplit : ∀ v ∈ S.erase u, (-1 : R) ^ (pos S v + 1) *
          (a * W (Sym2.map (paint c) s(u, v)) + rankTwo P Q u (c u) v (c v)) *
            (a * pfSum W c ((S.erase u).erase v) + reach W P Q c ((S.erase u).erase v))
        = a * a * ((-1) ^ (pos S v + 1) * W (Sym2.map (paint c) s(u, v)) *
              pfSum W c ((S.erase u).erase v))
          + a * ((-1) ^ (pos S v + 1) * W (Sym2.map (paint c) s(u, v)) *
              reach W P Q c ((S.erase u).erase v))
          + a * ((-1) ^ (pos S v + 1) * rankTwo P Q u (c u) v (c v) *
              pfSum W c ((S.erase u).erase v))
          + (-1) ^ (pos S v + 1) * rankTwo P Q u (c u) v (c v) *
              reach W P Q c ((S.erase u).erase v) := by
      intro v _; ring
    rw [Finset.sum_congr rfl hsplit]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hz, ← hp, hr]
    ring
  rw [hkey]
  have hpow : a ^ ((S.card - 2) / 2) * a = a ^ (S.card / 2) := by
    rw [← pow_succ]
    congr 1
    obtain ⟨k, hk⟩ := hodd
    omega
  rw [← mul_assoc, hpow, hn]

end MatchingPfaffian
