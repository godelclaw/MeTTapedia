import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharZero.Defs

/-!
# Finite outcome-fibre coefficients

Distinct origins remain distinct in the finite catalogue. Dividing an
outcome's weight by its inhabited fibre cardinality preserves exactly that
outcome's total coefficient. This requires a field of characteristic zero,
not an arbitrary semiring. Funding gates commute with this normalization
when the price is supplied on outcomes; origin-sensitive prices need their
own compatibility theorem.

These are coefficient comparisons for a supplied finite catalogue. They do
not establish completeness or whole-term operational correspondence for a
process translation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting.OutcomeFibreRates

open scoped BigOperators

universe uOrigin uOutcome uR

variable {Origin : Type uOrigin} {Outcome : Type uOutcome}
  [Fintype Origin] [DecidableEq Outcome] (observe : Origin → Outcome)

def fibre (outcome : Outcome) : Finset Origin := Finset.univ.filter (fun origin => observe origin = outcome)

theorem mem_fibre (origin : Origin) (outcome : Outcome) :
    origin ∈ fibre observe outcome ↔ observe origin = outcome := by
  simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and]

variable {R : Type uR} [Field R] [CharZero R]

def share (weight : Outcome → R) (origin : Origin) : R :=
  weight (observe origin) / ((fibre observe (observe origin)).card : R)

def pushed (weight : Origin → R) (outcome : Outcome) : R :=
  ∑ origin ∈ fibre observe outcome, weight origin

theorem pushed_share (weight : Outcome → R) (outcome : Outcome)
    (inhabited : (fibre observe outcome).Nonempty) :
    pushed observe (share observe weight) outcome = weight outcome := by
  have nonzero : ((fibre observe outcome).card : R) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr inhabited)
  unfold pushed
  have coefficients : (∑ origin ∈ fibre observe outcome, share observe weight origin) =
      ∑ _origin ∈ fibre observe outcome, weight outcome / ((fibre observe outcome).card : R) := by
    apply Finset.sum_congr rfl
    intro origin member
    unfold share
    rw [(mem_fibre observe origin outcome).mp member]
  rw [coefficients, Finset.sum_const, nsmul_eq_mul]
  exact (mul_comm _ _).trans (div_mul_cancel₀ _ nonzero)

def gatedShare (weight : Outcome → R) (price : Outcome → Nat) (budget : Nat) (origin : Origin) : R :=
  if price (observe origin) ≤ budget then share observe weight origin else 0

theorem pushed_gatedShare (weight : Outcome → R) (price : Outcome → Nat) (budget : Nat)
    (outcome : Outcome) (inhabited : (fibre observe outcome).Nonempty) :
    pushed observe (gatedShare observe weight price budget) outcome =
      if price outcome ≤ budget then weight outcome else 0 := by
  by_cases affordable : price outcome ≤ budget
  · rw [if_pos affordable]
    calc pushed observe (gatedShare observe weight price budget) outcome
        = pushed observe (share observe weight) outcome := by
          unfold pushed
          apply Finset.sum_congr rfl
          intro origin member
          unfold gatedShare
          rw [(mem_fibre observe origin outcome).mp member, if_pos affordable]
      _ = weight outcome := pushed_share observe weight outcome inhabited
  · rw [if_neg affordable]
    unfold pushed
    apply Finset.sum_eq_zero
    intro origin member
    unfold gatedShare
    rw [(mem_fibre observe origin outcome).mp member, if_neg affordable]

end Mettapedia.GSLT.Weighting.OutcomeFibreRates
