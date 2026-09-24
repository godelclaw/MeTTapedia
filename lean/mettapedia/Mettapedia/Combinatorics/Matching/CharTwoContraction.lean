import Mathlib
import Mettapedia.Combinatorics.Matching.Sum
import Mettapedia.Combinatorics.Matching.BlockRank

/-!
# Contracting a pair of sites in characteristic two

Fix two sites `p ≠ q` and weight the colours at them by `κ` and `μ`.  Summing every
matching sum over those two weightings — capping the pair with the rank-one covector
`κ ⊗ μ` — produces a quantity on the remaining sites.  Replacing each remaining edge
weight by

  `s · W(u,v) + X(u) Y(v) + X(v) Y(u)`,

where `s` is the cap value on the edge `pq` and `X`, `Y` are the weights through which a
site reaches `p` and `q`, turns that quantity back into an ordinary matching sum, up to a
power of `s`.

Over a general ring the identity fails exactly by the terms in which both pivots are used
more than once, and those terms occur in pairs.  So it holds on the nose as soon as
`2 = 0`.  The proof is an induction that deletes one site at a time; the only surviving
discrepancy is a sum over ordered triples of sites that an involution pairs off.

The rank-one cap is essential: with a cap of higher rank the cross terms between two of
its rank-one pieces do not pair up.

Credit: the contraction with the all-ones cap over `ZMod 2` is due to KitaKen1
(monochromatic-quantum-graphs-lean, Apache-2.0).  This file proves the general rank-one
version over any commutative ring in which `2 = 0`, by a different induction.
-/

namespace MatchingCharTwo

open Amplitude MatchingSum MatchingBlockRank

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
variable {R : Type*} [CommRing R]

section Definitions

variable (W : Sym2 (V × C) → R) (p q : V) (κ μ : C → R)

/-- The value of the cap `κ ⊗ μ` on the edge joining the two pivots. -/
def capValue : R := ∑ a, ∑ b, κ a * μ b * W s((p, a), (q, b))

/-- The weight with which the site `u`, coloured `a`, reaches the pivot `p`, the colour
at the pivot being summed against `κ`. -/
def pivotProfile (u : V) (a : C) : R := ∑ a', κ a' * W s((p, a'), (u, a))

/-- The contracted weights, before dividing by the cap value. -/
def contracted : Sym2 (V × C) → R :=
  Sym2.lift ⟨fun x y => capValue W p q κ μ * W s(x, y)
      + pivotProfile W p κ x.1 x.2 * pivotProfile W q μ y.1 y.2
      + pivotProfile W p κ y.1 y.2 * pivotProfile W q μ x.1 x.2,
    fun x y => by dsimp only; rw [Sym2.eq_swap]; ring⟩

/-- The matchings in which the two pivots reach two distinct sites of `S`: `p` reaches
`v` and `q` reaches `l`. -/
def reach (c : V → C) (S : Finset V) : R :=
  ∑ v ∈ S, ∑ l ∈ S.erase v,
    pivotProfile W p κ v (c v) * pivotProfile W q μ l (c l) *
      pmSum W c ((S.erase v).erase l)

end Definitions

variable (W : Sym2 (V × C) → R) (p q : V) (κ μ : C → R)

omit [Fintype V] [DecidableEq V] in
theorem contracted_apply (u v : V) (a b : C) :
    contracted W p q κ μ s((u, a), (v, b))
      = capValue W p q κ μ * W s((u, a), (v, b))
        + pivotProfile W p κ u a * pivotProfile W q μ v b
        + pivotProfile W p κ v b * pivotProfile W q μ u a := rfl

omit [Fintype V] [DecidableEq V] in
theorem contracted_paint (c : V → C) (u v : V) :
    contracted W p q κ μ (Sym2.map (paint c) s(u, v))
      = capValue W p q κ μ * W (Sym2.map (paint c) s(u, v))
        + pivotProfile W p κ u (c u) * pivotProfile W q μ v (c v)
        + pivotProfile W p κ v (c v) * pivotProfile W q μ u (c u) := rfl

/-! ### The capped matching sum, in any characteristic -/

omit [Fintype V] in
/-- Pure bookkeeping: summing a two-pivot expansion against a rank-one cap factors the
pivot weights out of the double sum over the two reached sites. -/
theorem sum_cap_rearrange (S : Finset V) (A B : C → V → R) (M : V → V → R) :
    ∑ a, ∑ b, κ a * μ b * (∑ v ∈ S, A a v * ∑ l ∈ S.erase v, B b l * M v l)
      = ∑ v ∈ S, ∑ l ∈ S.erase v, (∑ a, κ a * A a v) * (∑ b, μ b * B b l) * M v l := by
  have h1 : ∀ a b, κ a * μ b * (∑ v ∈ S, A a v * ∑ l ∈ S.erase v, B b l * M v l)
      = ∑ v ∈ S, ∑ l ∈ S.erase v, κ a * A a v * (μ b * B b l) * M v l := by
    intro a b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [h1]
  have h2 : ∀ v l, (∑ a, κ a * A a v) * (∑ b, μ b * B b l) * M v l
      = ∑ a, ∑ b, κ a * A a v * (μ b * B b l) * M v l := by
    intro v l
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
  simp_rw [h2]
  have key : ∀ F : C → C → V → V → R,
      (∑ a, ∑ b, ∑ v ∈ S, ∑ l ∈ S.erase v, F a b v l)
        = ∑ v ∈ S, ∑ l ∈ S.erase v, ∑ a, ∑ b, F a b v l := by
    intro F
    calc (∑ a, ∑ b, ∑ v ∈ S, ∑ l ∈ S.erase v, F a b v l)
        = ∑ a, ∑ v ∈ S, ∑ l ∈ S.erase v, ∑ b, F a b v l := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm (s := (Finset.univ : Finset C)) (t := S)]
          exact Finset.sum_congr rfl fun v _ => Finset.sum_comm
      _ = ∑ v ∈ S, ∑ l ∈ S.erase v, ∑ a, ∑ b, F a b v l := by
          rw [Finset.sum_comm (s := (Finset.univ : Finset C)) (t := S)]
          exact Finset.sum_congr rfl fun v _ => Finset.sum_comm
  exact key (fun a b v l => κ a * A a v * (μ b * B b l) * M v l)

/-- **Capping the pivot pair.**  Summing the matching sum over the pivot colours against
`κ ⊗ μ` gives the cap value times the matching sum of the rest, plus the matchings in which
the pivots reach two distinct sites.  An identity over any commutative ring. -/
theorem sum_cap_pmSum (c : V → C) {S : Finset V} (hpq : p ≠ q) (hp : p ∉ S)
    (hq : q ∉ S) :
    ∑ a, ∑ b, κ a * μ b * pmSum W (paintTwo c p q a b) (insert p (insert q S))
      = capValue W p q κ μ * pmSum W c S + reach W p q κ μ c S := by
  classical
  have hpS : p ∈ insert p (insert q S) := Finset.mem_insert_self p _
  have hqS : q ∈ (insert p (insert q S)).erase p :=
    Finset.mem_erase.mpr ⟨fun h => hpq h.symm, Finset.mem_insert_of_mem
      (Finset.mem_insert_self q S)⟩
  have hbase : ((insert p (insert q S)).erase p).erase q = S := by
    rw [Finset.erase_insert (by simp [hp, hpq]), Finset.erase_insert hq]
  have hinner : ∀ v ∈ S,
      (((insert p (insert q S)).erase p).erase v).erase q = S.erase v := by
    intro v _
    rw [Finset.erase_right_comm, hbase]
  have hsplit : ∀ a b, pmSum W (paintTwo c p q a b) (insert p (insert q S))
      = W s((p, a), (q, b)) * pmSum W c S
        + ∑ v ∈ S, W s((p, a), (v, c v)) *
            ∑ l ∈ S.erase v, W s((q, b), (l, c l)) * pmSum W c ((S.erase v).erase l) := by
    intro a b
    rw [block_split W c hpS hqS, hbase]
    congr 1
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hinner v hv]
  simp_rw [hsplit, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp only [capValue, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · rw [sum_cap_rearrange κ μ S (fun a v => W s((p, a), (v, c v)))
      (fun b l => W s((q, b), (l, c l))) (fun v l => pmSum W c ((S.erase v).erase l))]
    rfl


/-! ### Bookkeeping over ordered pairs and triples of distinct sites -/

omit [Fintype V] in
/-- Swapping the two indices of a sum over ordered pairs of distinct elements. -/
theorem sum_sum_erase_comm {M : Type*} [AddCommMonoid M] (B : Finset V) (G : V → V → M) :
    ∑ x ∈ B, ∑ y ∈ B.erase x, G x y = ∑ y ∈ B, ∑ x ∈ B.erase y, G x y := by
  refine Finset.sum_comm' fun x y => ?_
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hx, hyx, hy⟩; exact ⟨⟨fun h => hyx h.symm, hx⟩, hy⟩
  · rintro ⟨⟨hxy, hx⟩, hy⟩; exact ⟨hx, fun h => hxy h.symm, hy⟩

omit [Fintype V] in
/-- **Symmetric sums over ordered pairs vanish when `2 = 0`.**  Each unordered pair is
counted twice. -/
theorem sum_sum_erase_symm_eq_zero (h2 : (2 : R) = 0) (B : Finset V) (G : V → V → R)
    (hG : ∀ x y, G x y = G y x) :
    ∑ x ∈ B, ∑ y ∈ B.erase x, G x y = 0 := by
  rw [← Finset.sum_sigma (s := B) (t := fun x => B.erase x) (f := fun z => G z.1 z.2)]
  refine Finset.sum_involution (fun z _ => ⟨z.2, z.1⟩) ?_ ?_ ?_ ?_
  · intro z _
    show G z.1 z.2 + G z.2 z.1 = 0
    rw [hG z.2 z.1, ← two_mul, h2, zero_mul]
  · intro z hz _ h
    have hmem := Finset.mem_sigma.mp hz
    have hne : z.2 ≠ z.1 := (Finset.mem_erase.mp hmem.2).1
    have h1 : z.2 = z.1 := congrArg Sigma.fst h
    exact hne h1
  · intro z hz
    have hmem := Finset.mem_sigma.mp hz
    obtain ⟨hyx, hy⟩ := Finset.mem_erase.mp hmem.2
    exact Finset.mem_sigma.mpr ⟨hy, Finset.mem_erase.mpr ⟨fun h => hyx h.symm, hmem.1⟩⟩
  · intro z _
    rfl

/-! ### Expanding the reach term at a site -/

section Reach

variable (c : V → C)

theorem reach_eq (S : Finset V) :
    reach W p q κ μ c S = ∑ v ∈ S, ∑ l ∈ S.erase v,
      pivotProfile W p κ v (c v) * pivotProfile W q μ l (c l) *
        pmSum W c ((S.erase v).erase l) := rfl

/-- An odd vertex set is not reached: every remaining matching sum is over an odd set. -/
theorem reach_of_odd {S : Finset V} (hS : ¬ Even S.card) : reach W p q κ μ c S = 0 := by
  refine Finset.sum_eq_zero fun v hv => Finset.sum_eq_zero fun l hl => ?_
  have hlS : l ∈ S := Finset.mem_of_mem_erase hl
  have hcard : ((S.erase v).erase l).card + 2 = S.card := by
    rw [Finset.card_erase_of_mem hl, Finset.card_erase_of_mem hv]
    have : 2 ≤ S.card := by
      have hsub : ({v, l} : Finset V) ⊆ S := by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hv
        · rw [Finset.mem_singleton.mp hx]; exact hlS
      have hvl : v ≠ l := fun h => (Finset.mem_erase.mp hl).1 h.symm
      calc 2 = ({v, l} : Finset V).card := (Finset.card_pair hvl).symm
        _ ≤ S.card := Finset.card_le_card hsub
    omega
  rw [pmSum_of_odd W c (fun h => hS (by rw [← hcard]; exact h.add even_two)), mul_zero]

/-- **The reach term at a site.**  Either one pivot reaches the chosen site `u`, or `u` is
matched inside the rest and the pivots reach two other sites. -/
theorem reach_expand {S : Finset V} {u : V} (hu : u ∈ S) :
    reach W p q κ μ c S
      = ∑ l ∈ S.erase u,
          (pivotProfile W p κ u (c u) * pivotProfile W q μ l (c l)
            + pivotProfile W p κ l (c l) * pivotProfile W q μ u (c u)) *
              pmSum W c ((S.erase u).erase l)
        + ∑ w ∈ S.erase u, W (Sym2.map (paint c) s(u, w)) *
            reach W p q κ μ c ((S.erase u).erase w) := by
  classical
  set X : V → R := fun v => pivotProfile W p κ v (c v) with hX
  set Y : V → R := fun v => pivotProfile W q μ v (c v) with hY
  set A := S.erase u with hA
  have hsplit_v : ∀ v ∈ A,
      ∑ l ∈ S.erase v, X v * Y l * pmSum W c ((S.erase v).erase l)
        = X v * Y u * pmSum W c (A.erase v)
          + ∑ l ∈ A.erase v, ∑ w ∈ (A.erase v).erase l,
              X v * Y l * W (Sym2.map (paint c) s(u, w)) *
                pmSum W c (((A.erase v).erase l).erase w) := by
    intro v hv
    have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    have huv : u ∈ S.erase v := Finset.mem_erase.mpr ⟨fun h => hvu h.symm, hu⟩
    rw [← Finset.add_sum_erase (S.erase v) _ huv]
    have hset1 : (S.erase v).erase u = A.erase v := by
      ext x; simp only [hA, Finset.mem_erase]; tauto
    congr 1
    · rw [hset1]
    · rw [hset1]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hlu : l ≠ u := fun h => by
        rw [h] at hl; simp [hA] at hl
      have hlv : l ≠ v := (Finset.mem_erase.mp hl).1
      have hul : u ∈ (S.erase v).erase l :=
        Finset.mem_erase.mpr ⟨fun h => hlu h.symm, huv⟩
      rw [pmSum_expand W c hul, Finset.mul_sum]
      have hset2 : ((S.erase v).erase l).erase u = (A.erase v).erase l := by
        ext x; simp only [hA, Finset.mem_erase]; tauto
      rw [hset2]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring
  -- the part with neither pivot reaching `u`, reordered
  have htriple :
      ∑ v ∈ A, ∑ l ∈ A.erase v, ∑ w ∈ (A.erase v).erase l,
          X v * Y l * W (Sym2.map (paint c) s(u, w)) * pmSum W c (((A.erase v).erase l).erase w)
        = ∑ w ∈ A, W (Sym2.map (paint c) s(u, w)) * reach W p q κ μ c (A.erase w) := by
    have step1 : ∀ v ∈ A,
        ∑ l ∈ A.erase v, ∑ w ∈ (A.erase v).erase l,
            X v * Y l * W (Sym2.map (paint c) s(u, w)) *
              pmSum W c (((A.erase v).erase l).erase w)
          = ∑ w ∈ A.erase v, ∑ l ∈ (A.erase v).erase w,
            X v * Y l * W (Sym2.map (paint c) s(u, w)) *
              pmSum W c (((A.erase v).erase w).erase l) := by
      intro v _
      rw [sum_sum_erase_comm (A.erase v) (fun l w => X v * Y l * W (Sym2.map (paint c) s(u, w)) *
        pmSum W c (((A.erase v).erase l).erase w))]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun l _ => ?_
      have : ((A.erase v).erase l).erase w = ((A.erase v).erase w).erase l := by
        ext x; simp only [Finset.mem_erase]; tauto
      rw [this]
    rw [Finset.sum_congr rfl step1]
    rw [sum_sum_erase_comm A (fun v w => ∑ l ∈ (A.erase v).erase w,
      X v * Y l * W (Sym2.map (paint c) s(u, w)) * pmSum W c (((A.erase v).erase w).erase l))]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [reach_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    have hset : (A.erase v).erase w = (A.erase w).erase v := by
      ext x; simp only [Finset.mem_erase]; tauto
    rw [hset]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [reach_eq, ← Finset.add_sum_erase S _ hu, Finset.sum_congr rfl hsplit_v,
    Finset.sum_add_distrib, htriple]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

omit [Fintype V] in
/-- A triple sum symmetric in its first and last indices vanishes when `2 = 0`. -/
theorem triple_sum_eq_zero_left (h2 : (2 : R) = 0) (A : Finset V) (x₀ : R) (X Y : V → R)
    (M : Finset V → R) :
    ∑ v ∈ A, ∑ w ∈ A.erase v, ∑ l ∈ (A.erase v).erase w,
        x₀ * Y v * (X w * Y l * M (((A.erase v).erase w).erase l)) = 0 := by
  rw [sum_sum_erase_comm A (fun v w => ∑ l ∈ (A.erase v).erase w,
    x₀ * Y v * (X w * Y l * M (((A.erase v).erase w).erase l)))]
  refine Finset.sum_eq_zero fun w _ => ?_
  have hG := sum_sum_erase_symm_eq_zero (R := R) h2 (A.erase w)
    (fun v l => x₀ * Y v * (X w * Y l * M (((A.erase w).erase v).erase l)))
    (fun v l => by
      have : ((A.erase w).erase v).erase l = ((A.erase w).erase l).erase v := by
        ext x; simp only [Finset.mem_erase]; tauto
      simp only [this]; ring)
  rw [← hG]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hset : (A.erase v).erase w = (A.erase w).erase v := by
    ext x; simp only [Finset.mem_erase]; tauto
  rw [hset]

omit [Fintype V] in
/-- A triple sum symmetric in its first two indices vanishes when `2 = 0`. -/
theorem triple_sum_eq_zero_right (h2 : (2 : R) = 0) (A : Finset V) (y₀ : R) (X Y : V → R)
    (M : Finset V → R) :
    ∑ v ∈ A, ∑ w ∈ A.erase v, ∑ l ∈ (A.erase v).erase w,
        X v * y₀ * (X w * Y l * M (((A.erase v).erase w).erase l)) = 0 := by
  refine sum_sum_erase_symm_eq_zero (R := R) h2 A
    (fun v w => ∑ l ∈ (A.erase v).erase w, X v * y₀ * (X w * Y l * M (((A.erase v).erase w).erase l)))
    (fun v w => ?_)
  have hset : (A.erase v).erase w = (A.erase w).erase v := by
    ext x; simp only [Finset.mem_erase]; tauto
  simp only [hset]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The double reach cancels in characteristic two.**  Letting a pivot reach `u` while the
other two pivot visits land elsewhere counts every configuration twice. -/
theorem double_reach_eq_zero (h2 : (2 : R) = 0) {S : Finset V} {u : V} :
    ∑ v ∈ S.erase u,
        (pivotProfile W p κ u (c u) * pivotProfile W q μ v (c v)
          + pivotProfile W p κ v (c v) * pivotProfile W q μ u (c u)) *
            reach W p q κ μ c ((S.erase u).erase v) = 0 := by
  have hexp : ∀ v, (pivotProfile W p κ u (c u) * pivotProfile W q μ v (c v)
          + pivotProfile W p κ v (c v) * pivotProfile W q μ u (c u)) *
            reach W p q κ μ c ((S.erase u).erase v)
        = (∑ w ∈ (S.erase u).erase v, ∑ l ∈ ((S.erase u).erase v).erase w,
            pivotProfile W p κ u (c u) * pivotProfile W q μ v (c v) *
              (pivotProfile W p κ w (c w) * pivotProfile W q μ l (c l) *
                pmSum W c ((((S.erase u).erase v).erase w).erase l)))
          + ∑ w ∈ (S.erase u).erase v, ∑ l ∈ ((S.erase u).erase v).erase w,
            pivotProfile W p κ v (c v) * pivotProfile W q μ u (c u) *
              (pivotProfile W p κ w (c w) * pivotProfile W q μ l (c l) *
                pmSum W c ((((S.erase u).erase v).erase w).erase l)) := by
    intro v
    rw [reach_eq, add_mul, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.mul_sum]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun v _ => hexp v), Finset.sum_add_distrib,
    triple_sum_eq_zero_left h2 (S.erase u) (pivotProfile W p κ u (c u))
      (fun w => pivotProfile W p κ w (c w)) (fun v => pivotProfile W q μ v (c v)) (pmSum W c),
    triple_sum_eq_zero_right h2 (S.erase u) (pivotProfile W q μ u (c u))
      (fun w => pivotProfile W p κ w (c w)) (fun v => pivotProfile W q μ v (c v)) (pmSum W c),
    add_zero]

end Reach

/-! ### The contraction theorem -/

/-- **Contraction in characteristic two.**  On any vertex set avoiding the pivots, the
contracted weights reproduce the capped matching sum, up to a power of the cap value:
`s · pmSum y S = s^(|S|/2) · (s · pmSum W S + reach S)`. -/
theorem capValue_mul_pmSum_contracted (h2 : (2 : R) = 0) (c : V → C) :
    ∀ (S : Finset V), p ∉ S → q ∉ S →
      capValue W p q κ μ * pmSum (contracted W p q κ μ) c S
        = capValue W p q κ μ ^ (S.card / 2) *
            (capValue W p q κ μ * pmSum W c S + reach W p q κ μ c S) := by
  classical
  intro S
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  intro hp hq
  by_cases hodd : ¬ Even S.card
  · rw [pmSum_of_odd _ c hodd, pmSum_of_odd _ c hodd, reach_of_odd W p q κ μ c hodd]
    ring
  push Not at hodd
  rcases S.eq_empty_or_nonempty with hS | ⟨u, hu⟩
  · subst hS
    rw [Finset.card_empty] at hn
    subst hn
    have hr : reach W p q κ μ c ∅ = 0 := by unfold reach; simp
    simp [hr]
  have hcard : 2 ≤ S.card := by
    obtain ⟨k, hk⟩ := hodd
    have : 0 < S.card := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  -- expand the contracted matching sum at `u` and apply the induction hypothesis
  rw [pmSum_expand _ c hu, Finset.mul_sum]
  have hstep : ∀ v ∈ S.erase u,
      capValue W p q κ μ * (contracted W p q κ μ (Sym2.map (paint c) s(u, v)) *
          pmSum (contracted W p q κ μ) c ((S.erase u).erase v))
        = capValue W p q κ μ ^ ((S.card - 2) / 2) *
            (contracted W p q κ μ (Sym2.map (paint c) s(u, v)) *
              (capValue W p q κ μ * pmSum W c ((S.erase u).erase v)
                + reach W p q κ μ c ((S.erase u).erase v))) := by
    intro v hv
    have hT : ((S.erase u).erase v).card = S.card - 2 := by
      rw [Finset.card_erase_of_mem hv, Finset.card_erase_of_mem hu]; omega
    have hpT : p ∉ (S.erase u).erase v := fun h => hp (Finset.mem_of_mem_erase
      (Finset.mem_of_mem_erase h))
    have hqT : q ∉ (S.erase u).erase v := fun h => hq (Finset.mem_of_mem_erase
      (Finset.mem_of_mem_erase h))
    have := ih _ (by omega) ((S.erase u).erase v) hT hpT hqT
    calc capValue W p q κ μ * (contracted W p q κ μ (Sym2.map (paint c) s(u, v)) *
          pmSum (contracted W p q κ μ) c ((S.erase u).erase v))
        = contracted W p q κ μ (Sym2.map (paint c) s(u, v)) *
            (capValue W p q κ μ * pmSum (contracted W p q κ μ) c ((S.erase u).erase v)) := by ring
      _ = _ := by rw [this]; ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  -- the key identity
  have hkey : ∑ v ∈ S.erase u, contracted W p q κ μ (Sym2.map (paint c) s(u, v)) *
        (capValue W p q κ μ * pmSum W c ((S.erase u).erase v)
          + reach W p q κ μ c ((S.erase u).erase v))
      = capValue W p q κ μ *
          (capValue W p q κ μ * pmSum W c S + reach W p q κ μ c S) := by
    rw [pmSum_expand W c hu, reach_expand W p q κ μ c hu]
    have hz := double_reach_eq_zero W p q κ μ c h2 (S := S) (u := u)
    have hterm : ∀ v, contracted W p q κ μ (Sym2.map (paint c) s(u, v)) *
          (capValue W p q κ μ * pmSum W c ((S.erase u).erase v)
            + reach W p q κ μ c ((S.erase u).erase v))
        = capValue W p q κ μ * capValue W p q κ μ *
            (W (Sym2.map (paint c) s(u, v)) * pmSum W c ((S.erase u).erase v))
          + capValue W p q κ μ *
            (W (Sym2.map (paint c) s(u, v)) * reach W p q κ μ c ((S.erase u).erase v))
          + capValue W p q κ μ *
            ((pivotProfile W p κ u (c u) * pivotProfile W q μ v (c v)
              + pivotProfile W p κ v (c v) * pivotProfile W q μ u (c u)) *
                pmSum W c ((S.erase u).erase v))
          + (pivotProfile W p κ u (c u) * pivotProfile W q μ v (c v)
              + pivotProfile W p κ v (c v) * pivotProfile W q μ u (c u)) *
                reach W p q κ μ c ((S.erase u).erase v) := by
      intro v
      rw [contracted_paint]
      ring
    rw [Finset.sum_congr rfl (fun v _ => hterm v)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hz]
    ring
  rw [hkey]
  have hpow : capValue W p q κ μ ^ ((S.card - 2) / 2) * capValue W p q κ μ
      = capValue W p q κ μ ^ (S.card / 2) := by
    rw [← pow_succ]
    congr 1
    obtain ⟨k, hk⟩ := hodd
    omega
  rw [← mul_assoc, hpow, hn]

/-- **Contraction in characteristic two, capped form.**  The contracted matching sum on a
set avoiding the pivots equals the capped matching sum of the original weights on the set
with the pivots added, up to a power of the cap value. -/
theorem capValue_mul_pmSum_contracted_eq_cap (h2 : (2 : R) = 0) (c : V → C) {S : Finset V}
    (hpq : p ≠ q) (hp : p ∉ S) (hq : q ∉ S) :
    capValue W p q κ μ * pmSum (contracted W p q κ μ) c S
      = capValue W p q κ μ ^ (S.card / 2) *
          ∑ a, ∑ b, κ a * μ b * pmSum W (paintTwo c p q a b) (insert p (insert q S)) := by
  rw [capValue_mul_pmSum_contracted W p q κ μ h2 c S hp hq,
    sum_cap_pmSum W p q κ μ c hpq hp hq]

end MatchingCharTwo
