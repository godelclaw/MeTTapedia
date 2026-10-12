import Mettapedia.GSLT.Weighting.OutcomeFibreRates
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Equal shares require fractions and compatible funding

Two retained origins report one outcome. Rational half shares recover its
unit coefficient; natural coefficients cannot share it equally. Giving the
origins prices one and two reduces the observed coefficient to one half at
budget one. The outcome-based gate theorem therefore cannot be extended to
arbitrary origin-sensitive prices.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting.OutcomeFibreRates.Controls

open scoped BigOperators

def observe : Fin 2 → Unit := fun _ => ()

def weight : Unit → ℚ := fun _ => 1

theorem complete_fibre : fibre observe () = Finset.univ := by simp [fibre, observe]

theorem fibre_inhabited : (fibre observe ()).Nonempty := by
  rw [complete_fibre]
  exact ⟨0, Finset.mem_univ _⟩

theorem each_origin_has_half (origin : Fin 2) : share observe weight origin = 1 / 2 := by
  change (1 : ℚ) / ((fibre observe ()).card : ℚ) = 1 / 2
  rw [complete_fibre]
  norm_num

theorem actual_rational_mass_is_one : pushed observe (share observe weight) () = 1 :=
  pushed_share observe weight () fibre_inhabited

theorem no_equal_natural_shares : ¬ ∃ coefficient : Nat, (∑ _origin : Fin 2, coefficient) = 1 := by
  rintro ⟨coefficient, total⟩
  simp only [Fin.sum_univ_two] at total
  omega

def originPrice (origin : Fin 2) : Nat := origin.val + 1

def fundedOrigins (budget : Nat) (origin : Fin 2) : ℚ :=
  if originPrice origin ≤ budget then share observe weight origin else 0

theorem origin_sensitive_budget_has_half_mass : pushed observe (fundedOrigins 1) () = 1 / 2 := by
  unfold pushed
  rw [complete_fibre, Fin.sum_univ_two]
  unfold fundedOrigins
  rw [each_origin_has_half, each_origin_has_half]
  norm_num [originPrice]

theorem larger_budget_restores_the_full_mass : pushed observe (fundedOrigins 2) () = 1 := by
  unfold pushed
  rw [complete_fibre, Fin.sum_univ_two]
  unfold fundedOrigins
  rw [each_origin_has_half, each_origin_has_half]
  norm_num [originPrice]

theorem common_price_preserves_the_unit_mass :
    pushed observe (gatedShare observe weight (fun _ => 1) 1) () = 1 := by
  rw [pushed_gatedShare observe weight (fun _ => 1) 1 () fibre_inhabited]
  rfl

theorem origin_sensitive_prices_are_not_a_common_outcome_gate :
    pushed observe (fundedOrigins 1) () ≠
      pushed observe (gatedShare observe weight (fun _ => 1) 1) () := by
  rw [origin_sensitive_budget_has_half_mass, common_price_preserves_the_unit_mass]
  norm_num

end Mettapedia.GSLT.Weighting.OutcomeFibreRates.Controls
