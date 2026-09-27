import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitSurgery
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic

/-!
# Orbit counts under carrier equivalence and disjoint sums

Two bookkeeping facts about `orbitCount`, needed to move face counts between
the several carriers a seam glue passes through.

* Conjugating a permutation across an equivalence of carriers does not change
  its orbit count: the equivalence carries orbits to orbits.
* The orbit count of a disjoint sum of permutations is the sum of the orbit
  counts: no orbit crosses between the summands.

Also the right-hand form of the transposition law: a transposition on the right
of `σ` is a transposition on the left at the images, and two transpositions on
disjoint points commute.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrbitCountCongr

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24CompositeSeamCubic

/-! ## Transposition bookkeeping -/

section Swap

variable {D : Type*} [DecidableEq D]

/-- A transposition on the right is a transposition on the left, at the images. -/
theorem mul_swap_eq_swap_mul (σ : Perm D) (a b : D) :
    σ * swap a b = swap (σ a) (σ b) * σ := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hxa : x = a
  · subst hxa; simp
  · by_cases hxb : x = b
    · subst hxb; simp
    · rw [swap_apply_of_ne_of_ne hxa hxb,
        swap_apply_of_ne_of_ne (σ.injective.ne hxa) (σ.injective.ne hxb)]

/-- Transpositions on four distinct points commute. -/
theorem swap_mul_swap_comm {a b c d : D} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    swap a b * swap c d = swap c d * swap a b := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hxa : x = a
  · subst hxa
    rw [swap_apply_of_ne_of_ne hac had, swap_apply_left, swap_apply_of_ne_of_ne hbc hbd]
  · by_cases hxb : x = b
    · subst hxb
      rw [swap_apply_of_ne_of_ne hbc hbd, swap_apply_right, swap_apply_of_ne_of_ne hac had]
    · rw [swap_apply_of_ne_of_ne hxa hxb]
      by_cases hxc : x = c
      · subst hxc
        rw [swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]
      · by_cases hxd : x = d
        · subst hxd
          rw [swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
        · rw [swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb]

end Swap

/-! ## Carrier equivalence -/

section Conj

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Same cycle is reflected as well as preserved across a conjugating
equivalence. -/
theorem sameCycle_conjEquiv_iff (e : α ≃ β) (σ : Perm α) (x y : α) :
    Equiv.Perm.SameCycle ((e.symm.trans σ).trans e) (e x) (e y) ↔ σ.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [conjEquiv_pow, Equiv.symm_apply_apply] at hn
    exact ⟨n, by rw [zpow_natCast]; exact e.injective hn⟩
  · exact sameCycle_conjEquiv e σ

/-- **Orbit counts are invariant under carrier equivalence.** -/
theorem orbitCount_conjEquiv (e : α ≃ β) (σ : Perm α) :
    orbitCount ((e.symm.trans σ).trans e) = orbitCount σ := by
  unfold orbitCount
  refine (Fintype.card_congr ?_).symm
  exact Quotient.congr e fun x y => (sameCycle_conjEquiv_iff e σ x y).symm

end Conj

/-! ## Disjoint sums -/

section Sum

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem sameCycle_sumCongr_inl_iff (σ : Perm α) (τ : Perm β) (a a' : α) :
    Equiv.Perm.SameCycle (Equiv.sumCongr σ τ) (Sum.inl a) (Sum.inl a') ↔ σ.SameCycle a a' := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [sumCongr_pow_inl] at hn
    exact ⟨n, by rw [zpow_natCast]; exact Sum.inl_injective hn⟩
  · exact sameCycle_sumCongr_inl σ τ

theorem sameCycle_sumCongr_inr_iff (σ : Perm α) (τ : Perm β) (b b' : β) :
    Equiv.Perm.SameCycle (Equiv.sumCongr σ τ) (Sum.inr b) (Sum.inr b') ↔ τ.SameCycle b b' := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [sumCongr_pow_inr] at hn
    exact ⟨n, by rw [zpow_natCast]; exact Sum.inr_injective hn⟩
  · exact sameCycle_sumCongr_inr σ τ

/-- No orbit crosses between the summands. -/
theorem not_sameCycle_sumCongr_inl_inr (σ : Perm α) (τ : Perm β) (a : α) (b : β) :
    ¬ Equiv.Perm.SameCycle (Equiv.sumCongr σ τ) (Sum.inl a) (Sum.inr b) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [sumCongr_pow_inl] at hn
  exact Sum.inl_ne_inr hn

/-- Orbits of a disjoint sum: an orbit in either summand, tagged. -/
def sumOrbitEquiv (σ : Perm α) (τ : Perm β) :
    Quotient (Equiv.Perm.SameCycle.setoid (Equiv.sumCongr σ τ)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid σ) ⊕ Quotient (Equiv.Perm.SameCycle.setoid τ) where
  toFun := Quotient.lift
    (fun x => match x with
      | Sum.inl a => Sum.inl (Quotient.mk _ a)
      | Sum.inr b => Sum.inr (Quotient.mk _ b))
    (by
      rintro (a | b) (a' | b') h
      · exact congrArg Sum.inl (Quotient.sound ((sameCycle_sumCongr_inl_iff σ τ a a').1 h))
      · exact absurd h (not_sameCycle_sumCongr_inl_inr σ τ a b')
      · exact absurd h.symm (not_sameCycle_sumCongr_inl_inr σ τ a' b)
      · exact congrArg Sum.inr (Quotient.sound ((sameCycle_sumCongr_inr_iff σ τ b b').1 h)))
  invFun := fun x => match x with
    | Sum.inl q => Quotient.map Sum.inl
        (fun a a' h => (sameCycle_sumCongr_inl_iff σ τ a a').2 h) q
    | Sum.inr q => Quotient.map Sum.inr
        (fun b b' h => (sameCycle_sumCongr_inr_iff σ τ b b').2 h) q
  left_inv := by
    rintro ⟨a | b⟩ <;> rfl
  right_inv := by
    rintro (q | q)
    · induction q using Quotient.inductionOn with
      | h a => rfl
    · induction q using Quotient.inductionOn with
      | h b => rfl

/-- **Orbit counts add over disjoint sums.** -/
theorem orbitCount_sumCongr (σ : Perm α) (τ : Perm β) :
    orbitCount (Equiv.sumCongr σ τ) = orbitCount σ + orbitCount τ := by
  unfold orbitCount
  rw [Fintype.card_congr (sumOrbitEquiv σ τ), Fintype.card_sum]

end Sum

end GoertzelV24OrbitCountCongr

end Mettapedia.GraphTheory.FourColor
