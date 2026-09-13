import Mettapedia.Analysis.QuarticTensorEnergy

/-! # Radial, tangential, and zero-field normalization checks -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.QuarticTensorEnergyTests

open scoped RealInnerProductSpace
open QuarticTensorEnergy PeriodicRadialRiesz
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

theorem radial_rate (a : Rd) :
    (∑ i, ∑ j, quarticTensorRate a a i j ^ 2) = 16 * ‖a‖ ^ 8 := by
  rw [sum_quarticTensorRate_sq, real_inner_self_eq_norm_sq]
  ring

theorem tangential_rate (a v : Rd) (hv : ⟪a, v⟫ = 0) :
    (∑ i, ∑ j, quarticTensorRate a v i j ^ 2) = 2 * ‖a‖ ^ 6 * ‖v‖ ^ 2 := by
  rw [sum_quarticTensorRate_sq, hv]
  ring

theorem zero_field_rate (v : Rd) :
    (∑ i, ∑ j, quarticTensorRate (0 : Rd) v i j ^ 2) = 0 := by
  simp [sum_quarticTensorRate_sq]

end Mettapedia.Analysis.QuarticTensorEnergyTests
