import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitSurgery

/-!
# The orbit exchange lemma

Gluing two closed-up sides along `k` ports replaces, at each port, one pairing
by another.  On the face permutation that is two transpositions per port: one
that merges a hub face of the left side with a hub face of the right side, and
one that splits the merged face again along the seam.  Net, the number of face
orbits does not change.

This file proves that as a statement about permutations alone.  Given a family
of permutations indexed by finite sets of ports, growing by exactly those two
transpositions when a port is added, and given that the ports' hub faces are
pairwise distinct in the initial permutation, the orbit count is invariant.

The proof is an induction over the set of exchanged ports.  The invariant is
that the orbits of the not-yet-exchanged ports are untouched: a point whose
initial orbit avoids every transposition so far still has its initial orbit.
That is the one fact needed to apply the split/merge law at the next port.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrbitExchange

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Orbits avoiding a transposition are untouched -/

/-- Along an orbit that avoids both swapped points, the swapped permutation
agrees with the original at every power. -/
theorem pow_swap_mul_apply_of_avoiding (ψ : Perm D) {a b x : D}
    (ha : ¬ ψ.SameCycle x a) (hb : ¬ ψ.SameCycle x b) (n : ℕ) :
    ((swap a b * ψ) ^ n) x = (ψ ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hL : ((swap a b * ψ) ^ (n + 1)) x = swap a b (ψ (((swap a b * ψ) ^ n) x)) := by
        rw [pow_succ', Perm.mul_apply, Perm.mul_apply]
      have hR : (ψ ^ (n + 1)) x = ψ ((ψ ^ n) x) := by
        rw [pow_succ', Perm.mul_apply]
      rw [hL, hR, ih]
      have hcyc : ψ.SameCycle x (ψ ((ψ ^ n) x)) :=
        ⟨((n + 1 : ℕ) : ℤ), by rw [zpow_natCast, hR]⟩
      apply swap_apply_of_ne_of_ne
      · intro h
        exact ha (h ▸ hcyc)
      · intro h
        exact hb (h ▸ hcyc)

/-- **An orbit avoiding both swapped points is unchanged.** -/
theorem sameCycle_swap_mul_iff_of_avoiding (ψ : Perm D) {a b x : D}
    (ha : ¬ ψ.SameCycle x a) (hb : ¬ ψ.SameCycle x b) (y : D) :
    (swap a b * ψ).SameCycle x y ↔ ψ.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← pow_swap_mul_apply_of_avoiding ψ ha hb, hn]⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, pow_swap_mul_apply_of_avoiding ψ ha hb, hn]⟩

/-- The same, across the two transpositions of one port exchange. -/
theorem sameCycle_exchange_iff_of_avoiding (ψ : Perm D) {u v u' v' x : D}
    (hu : ¬ ψ.SameCycle x u) (hv : ¬ ψ.SameCycle x v)
    (hu' : ¬ ψ.SameCycle x u') (hv' : ¬ ψ.SameCycle x v') (y : D) :
    (swap u' v' * (swap u v * ψ)).SameCycle x y ↔ ψ.SameCycle x y := by
  have h1 : ¬ (swap u v * ψ).SameCycle x u' := fun h =>
    hu' ((sameCycle_swap_mul_iff_of_avoiding ψ hu hv u').1 h)
  have h2 : ¬ (swap u v * ψ).SameCycle x v' := fun h =>
    hv' ((sameCycle_swap_mul_iff_of_avoiding ψ hu hv v').1 h)
  rw [sameCycle_swap_mul_iff_of_avoiding (swap u v * ψ) h1 h2,
    sameCycle_swap_mul_iff_of_avoiding ψ hu hv]

/-! ## One port: merge, then split -/

/-- **One exchange leaves the orbit count fixed.**  The first transposition
merges two distinct orbits; the second then splits the merged orbit, because
its two points came one from each. -/
theorem orbitCount_exchange_step (φ : Perm D) {u v u' v' : D}
    (huv : ¬ φ.SameCycle u v) (hu' : φ.SameCycle u u') (hv' : φ.SameCycle v v')
    (hne : u' ≠ v') :
    orbitCount (swap u' v' * (swap u v * φ)) = orbitCount φ := by
  have hne1 : u ≠ v := fun h => huv (h ▸ SameCycle.refl _ _)
  have hmerge := orbitCount_swap_mul_of_not_sameCycle φ hne1 huv
  have h1 : (swap u v * φ).SameCycle u v := swap_mul_sameCycle_of_not_sameCycle huv
  have hu'' : (swap u v * φ).SameCycle u u' := by
    rcases swap_mul_sameCycle_or (b := v) hu' with h | h
    · exact h
    · exact h1.trans h
  have hv'' : (swap u v * φ).SameCycle v v' := by
    rcases swap_mul_sameCycle_or (b := u) hv' with h | h
    · rwa [swap_comm] at h
    · rw [swap_comm] at h
      exact h1.symm.trans h
  have hsame : (swap u v * φ).SameCycle u' v' := hu''.symm.trans (h1.trans hv'')
  have hsplit := orbitCount_swap_mul_of_sameCycle (swap u v * φ) hne hsame
  omega

/-! ## All ports: the exchange family -/

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The orbit exchange lemma.**

`φ S` is the permutation after exchanging the ports in `S`.  Adding a port
applies its merging transposition `(u p, v p)` and then its splitting
transposition `(u' p, v' p)`.  If in the initial permutation the merging points
of distinct ports lie on pairwise distinct orbits, each port's two merging
points lie on distinct orbits, and each splitting point lies on the orbit of the
corresponding merging point, then every `φ S` has the orbit count of `φ ∅`.

The invariant carried is the untouched-orbit statement for unexchanged ports. -/
theorem orbitCount_exchange_family
    (φ : Finset ι → Perm D) (u v u' v' : ι → D)
    (hstep : ∀ S p, p ∉ S →
      φ (insert p S) = swap (u' p) (v' p) * (swap (u p) (v p) * φ S))
    (hdistinct : ∀ p q, p ≠ q →
      ¬ (φ ∅).SameCycle (u p) (u q) ∧ ¬ (φ ∅).SameCycle (u p) (v q) ∧
        ¬ (φ ∅).SameCycle (v p) (u q) ∧ ¬ (φ ∅).SameCycle (v p) (v q))
    (huv : ∀ p, ¬ (φ ∅).SameCycle (u p) (v p))
    (hu' : ∀ p, (φ ∅).SameCycle (u p) (u' p))
    (hv' : ∀ p, (φ ∅).SameCycle (v p) (v' p))
    (hne : ∀ p, u' p ≠ v' p) (S : Finset ι) :
    orbitCount (φ S) = orbitCount (φ ∅) ∧
      ∀ p ∉ S, ∀ x, ((φ ∅).SameCycle x (u p) ∨ (φ ∅).SameCycle x (v p)) →
        ∀ y, (φ S).SameCycle x y ↔ (φ ∅).SameCycle x y := by
  induction S using Finset.induction_on with
  | empty => exact ⟨rfl, fun _ _ _ _ _ => Iff.rfl⟩
  | insert p₀ S hp₀ ih =>
      obtain ⟨hcount, hinv⟩ := ih
      -- the unexchanged port p₀ still has its initial orbits
      have hu_inv := hinv p₀ hp₀ (u p₀) (Or.inl (SameCycle.refl _ _))
      have hv_inv := hinv p₀ hp₀ (v p₀) (Or.inr (SameCycle.refl _ _))
      have huv' : ¬ (φ S).SameCycle (u p₀) (v p₀) := fun h => huv p₀ ((hu_inv _).1 h)
      have hu'' : (φ S).SameCycle (u p₀) (u' p₀) := (hu_inv _).2 (hu' p₀)
      have hv'' : (φ S).SameCycle (v p₀) (v' p₀) := (hv_inv _).2 (hv' p₀)
      refine ⟨?_, ?_⟩
      · rw [hstep S p₀ hp₀, orbitCount_exchange_step (φ S) huv' hu'' hv'' (hne p₀), hcount]
      · intro p hp x hx y
        have hpS : p ∉ S := fun h => hp (Finset.mem_insert_of_mem h)
        have hpne : p ≠ p₀ := fun h => hp (h ▸ Finset.mem_insert_self _ _)
        obtain ⟨d1, d2, d3, d4⟩ := hdistinct p p₀ hpne
        -- x avoids all four points of port p₀, in the initial permutation
        have hxu : ¬ (φ ∅).SameCycle x (u p₀) := by
          rcases hx with hx | hx
          · exact fun h => d1 (hx.symm.trans h)
          · exact fun h => d3 (hx.symm.trans h)
        have hxv : ¬ (φ ∅).SameCycle x (v p₀) := by
          rcases hx with hx | hx
          · exact fun h => d2 (hx.symm.trans h)
          · exact fun h => d4 (hx.symm.trans h)
        have hxu' : ¬ (φ ∅).SameCycle x (u' p₀) := fun h => hxu (h.trans (hu' p₀).symm)
        have hxv' : ¬ (φ ∅).SameCycle x (v' p₀) := fun h => hxv (h.trans (hv' p₀).symm)
        -- hence also in `φ S`, by the invariant at `p`
        have hx_inv := hinv p hpS x hx
        rw [hstep S p₀ hp₀,
          sameCycle_exchange_iff_of_avoiding (φ S)
            (fun h => hxu ((hx_inv _).1 h)) (fun h => hxv ((hx_inv _).1 h))
            (fun h => hxu' ((hx_inv _).1 h)) (fun h => hxv' ((hx_inv _).1 h)),
          hx_inv]

/-- The orbit count after exchanging every port. -/
theorem orbitCount_exchange_univ
    (φ : Finset ι → Perm D) (u v u' v' : ι → D)
    (hstep : ∀ S p, p ∉ S →
      φ (insert p S) = swap (u' p) (v' p) * (swap (u p) (v p) * φ S))
    (hdistinct : ∀ p q, p ≠ q →
      ¬ (φ ∅).SameCycle (u p) (u q) ∧ ¬ (φ ∅).SameCycle (u p) (v q) ∧
        ¬ (φ ∅).SameCycle (v p) (u q) ∧ ¬ (φ ∅).SameCycle (v p) (v q))
    (huv : ∀ p, ¬ (φ ∅).SameCycle (u p) (v p))
    (hu' : ∀ p, (φ ∅).SameCycle (u p) (u' p))
    (hv' : ∀ p, (φ ∅).SameCycle (v p) (v' p))
    (hne : ∀ p, u' p ≠ v' p) :
    orbitCount (φ Finset.univ) = orbitCount (φ ∅) :=
  (orbitCount_exchange_family φ u v u' v' hstep hdistinct huv hu' hv' hne Finset.univ).1

end Family

end GoertzelV24OrbitExchange

end Mettapedia.GraphTheory.FourColor
