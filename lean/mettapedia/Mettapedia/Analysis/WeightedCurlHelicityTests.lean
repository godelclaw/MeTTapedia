import Mettapedia.Analysis.WeightedCurlHelicity
import Mettapedia.Analysis.WeightedCurlCancellationTests

/-! # First-jet checks of helicity absorption, including the sharp Young constant -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedCurlHelicityTests

open WeightedCurlHelicity WeightedCurlCancellationTests
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem helicity_one : helicity a D = 1 := by
  rw [helicity, curlJet_D, real_inner_self_eq_norm_sq, norm_a_sq]

theorem longitudinalDefect_one : longitudinalDefect a D = 1 := by
  have h4 : ‖a‖ ^ 4 = 1 := by
    rw [show ‖a‖ ^ 4 = (‖a‖ ^ 2) ^ 2 by ring, norm_a_sq, one_pow]
  simp only [longitudinalDefect, helicity_one, h4]
  norm_num [a, D, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

theorem radialDensity_one : radialDensity a D = 1 := by
  have h4 : ‖a‖ ^ 4 = 1 := by
    rw [show ‖a‖ ^ 4 = (‖a‖ ^ 2) ^ 2 by ring, norm_a_sq, one_pow]
  simp only [radialDensity, h4]
  norm_num [a, D, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem helicityDensity_one : helicityDensity a D = 1 := by
  rw [helicityDensity, helicity_one, one_pow, mul_one]
  calc
    ‖a‖ ^ 6 = (‖a‖ ^ 2) ^ 3 := by ring
    _ = 1 := by rw [norm_a_sq]; norm_num

/-- This is equality for a divergence-free jet, not a global NS solution. -/
theorem absorption_sharp :
    |longitudinalDefect a D| = (1 / 2 : ℝ) * radialDensity a D +
      helicityDensity a D / (4 * (1 / 2 : ℝ)) := by
  rw [longitudinalDefect_one, radialDensity_one, helicityDensity_one]
  norm_num

theorem zero_vorticity (D : Fin 3 → R3) :
    longitudinalDefect 0 D = 0 ∧ radialDensity 0 D = 0 ∧ helicityDensity 0 D = 0 := by
  simp [longitudinalDefect, radialDensity, helicityDensity]

end Mettapedia.Analysis.WeightedCurlHelicityTests
