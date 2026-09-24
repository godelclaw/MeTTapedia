import Mettapedia.Analysis.LongitudinalHelicityBudget
import Mettapedia.Analysis.WeightedCurlHelicityTests

/-!
# Sharp and strictly depleted first-jet tests

Both jets are divergence free. These are checks of the pointwise estimate,
not global periodic solutions or examples of Navier–Stokes blowup.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.LongitudinalHelicityBudgetTests

open LongitudinalHelicityBudget WeightedCurlHelicity
open WeightedCurlCancellationTests (a norm_a_sq)
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def transverseJet : Fin 3 → R3 := ![0, WithLp.toLp 2 ![-1, 0, 1], 0]

theorem transverseJet_divergence_zero : (∑ j : Fin 3, transverseJet j j) = 0 := by
  norm_num [transverseJet, Fin.sum_univ_three, Matrix.cons_val_two]

theorem transverseJet_amplitudeGradientSquare_one : amplitudeGradientSquare a transverseJet = 1 := by
  norm_num [amplitudeGradientSquare, a, transverseJet, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem transverseJet_longitudinalAmplitude_zero : longitudinalAmplitude a transverseJet = 0 := by
  norm_num [longitudinalAmplitude, a, transverseJet, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem transverseJet_helicity_one : helicity a transverseJet = 1 := by
  norm_num [helicity, WeightedCurlCancellation.curlJet, a, transverseJet,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem transverseJet_directionalHelicity_zero : directionalHelicityDensity a transverseJet = 0 :=
  directionalHelicityDensity_eq_zero_of_longitudinalAmplitude_eq_zero _ _
    transverseJet_longitudinalAmplitude_zero

theorem transverseJet_helicityDensity_one : helicityDensity a transverseJet = 1 := by
  rw [helicityDensity, transverseJet_helicity_one, one_pow, mul_one,
    show ‖a‖ ^ 6 = (‖a‖ ^ 2) ^ 3 by ring, norm_a_sq, one_pow]

/-- Strict improvement despite nonzero amplitude gradient and nonzero helicity. -/
theorem transverseJet_strict_improvement :
    directionalHelicityDensity a transverseJet < helicityDensity a transverseJet := by
  rw [transverseJet_directionalHelicity_zero, transverseJet_helicityDensity_one]
  norm_num

/-- The aligned jet retains the sharp constant from the coarser estimate. -/
theorem alignedJet_directionalHelicity_one :
    directionalHelicityDensity a WeightedCurlCancellationTests.D = 1 := by
  have hp := longitudinalDefect_sq a WeightedCurlCancellationTests.D
  rw [WeightedCurlHelicityTests.longitudinalDefect_one,
    WeightedCurlHelicityTests.radialDensity_one, one_pow, one_mul] at hp
  exact hp.symm

theorem zero_vorticity (D : Fin 3 → R3) : directionalHelicityDensity 0 D = 0 := by
  simp [directionalHelicityDensity]

end Mettapedia.Analysis.LongitudinalHelicityBudgetTests
