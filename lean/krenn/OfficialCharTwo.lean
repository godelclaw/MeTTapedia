import Mathlib
import CharTwoSix
import GeneralOfficialBridge

/-!
# The Krenn–Gu conjecture in characteristic two

Over every field of characteristic two, the official equation system on `2n ≥ 6` vertices,
with three or more colours, has no solution.  Reducing modulo a maximal ideal containing
`2`, neither has it over any commutative ring in which `2` is not a unit.

The argument: a live pair contracts a GHZ system to one on two fewer sites
(`CharTwoDescent`), down to six sites, where no GHZ system exists (`CharTwoSix`).  Both steps
need an infinite field; a finite field first embeds in its algebraic closure.

Over `ZMod 2` the statement is due to KitaKen1 (monochromatic-quantum-graphs-lean,
Apache-2.0), whose contraction with the all-ones cap this development generalizes; the
six-site base case here is different, and works over every field of characteristic two.
-/

namespace KrennCharTwo

open Amplitude MatchingSum MonochromaticQuantumGraph GeneralOfficialBridge

/-- Over an infinite field of characteristic two, no GHZ system on `2n ≥ 6` sites. -/
theorem no_isGHZOver_of_infinite {F : Type*} [Field F] (h2 : (2 : F) = 0) [Infinite F] :
    ∀ n : ℕ, 3 ≤ n → ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = 2 * n →
      ∀ W : Sym2 (V × Fin 3) → F, ¬ IsGHZOver W :=
  no_isGHZOver_of_six h2 (no_isGHZOver_six h2)

/-- **No GHZ system on `2n ≥ 6` sites over any field of characteristic two.** -/
theorem no_isGHZOver {F : Type*} [Field F] (h2 : (2 : F) = 0) :
    ∀ n : ℕ, 3 ≤ n → ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = 2 * n →
      ∀ W : Sym2 (V × Fin 3) → F, ¬ IsGHZOver W := by
  intro n hn V _ _ hV W hW
  have h2K : (2 : AlgebraicClosure F) = 0 := by
    rw [← map_ofNat (algebraMap F (AlgebraicClosure F)) 2, h2, map_zero]
  exact no_isGHZOver_of_infinite h2K n hn V hV _ (isGHZOver_map (algebraMap F _) W hW)

/-- An official solution is a GHZ system. -/
theorem isGHZOver_of_eqSystemN {F : Type} [Field F] {N : ℕ} (hN : 0 < N)
    {W : WeightsN N 3 F} (h : EqSystemN N 3 W) : IsGHZOver (symWeight W) := by
  rw [eqSystemN_iff_amplitude_const] at h
  refine ⟨fun k => ?_, fun c hc => ?_⟩
  · rw [h]
    simp [Amplitude.const]
  · rw [h, if_neg]
    intro hconst
    exact hc ⟨c ⟨0, hN⟩, fun v => hconst v _⟩

/-- **The Krenn–Gu conjecture over every field of characteristic two**, in the official
formulation: no weighting of the complete graph on `2n ≥ 6` vertices in three colours solves
the equation system. -/
theorem krennGu_charTwo (F : Type) [Field F] (h2 : (2 : F) = 0) :
    ∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) 3 F, EqSystemN (2 * n) 3 W := by
  rintro n hn ⟨W, hW⟩
  exact no_isGHZOver h2 n hn (Fin (2 * n)) (Fintype.card_fin _) _
    (isGHZOver_of_eqSystemN (by omega) hW)

/-- **Every number of colours from three on.**  Restricting the colours to the first three
turns a solution into a three-colour GHZ system. -/
theorem krennGu_charTwo_colours (F : Type) [Field F] (h2 : (2 : F) = 0) {D : ℕ}
    (hD : 3 ≤ D) :
    ∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) D F, EqSystemN (2 * n) D W := by
  rintro n hn ⟨W, hW⟩
  rw [eqSystemN_iff_amplitude_const] at hW
  apply no_isGHZOver h2 n hn (Fin (2 * n)) (Fintype.card_fin _)
    (restrict (Fin.castLE hD) (symWeight W))
  refine ⟨fun k => ?_, fun c hc => ?_⟩
  · rw [amplitude_restrict, hW]
    simp [Amplitude.const]
  · rw [amplitude_restrict, hW, if_neg]
    intro hconst
    exact hc ⟨c ⟨0, by omega⟩, fun v => Fin.castLE_injective hD (hconst v _)⟩

/-- **No solution over any commutative ring in which `2` is not a unit** — for instance the
integers, or the ring of integers of a number field, where `2` is never a unit.  A maximal
ideal containing `2` has a residue field of characteristic two, where the reduced weights
would solve the system. -/
theorem krennGu_of_not_isUnit_two (R : Type) [CommRing R] (h : ¬ IsUnit (2 : R)) :
    ∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) 3 R, EqSystemN (2 * n) 3 W := by
  rintro n hn ⟨W, hW⟩
  obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : R)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact h)
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  have h2 : (2 : R ⧸ M) = 0 := by
    rw [← map_ofNat (Ideal.Quotient.mk M) 2]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h2M (Ideal.mem_span_singleton_self 2))
  rw [eqSystemN_iff_amplitude_const] at hW
  apply no_isGHZOver h2 n hn (Fin (2 * n)) (Fintype.card_fin _)
    (fun e => Ideal.Quotient.mk M (symWeight W e))
  refine ⟨fun k => ?_, fun c hc => ?_⟩
  · rw [amplitude_map_ringHom, hW]
    simp [Amplitude.const]
  · rw [amplitude_map_ringHom, hW, if_neg, map_zero]
    intro hconst
    exact hc ⟨c ⟨0, by omega⟩, fun v => hconst v _⟩

end KrennCharTwo

#print axioms KrennCharTwo.krennGu_charTwo
#print axioms KrennCharTwo.krennGu_charTwo_colours
#print axioms KrennCharTwo.krennGu_of_not_isUnit_two
