import Mettapedia.Analysis.CurlHelicityCentering
import Mettapedia.Analysis.LongitudinalHelicityBudgetTests

/-!
# Center selection and the pointwise limit of helicity centering

The divergence-free test jet has nonzero longitudinal variation and helicity.
A matching center removes its cost; the opposite center increases it. The
signed density changes pointwise, so centering requires the proved spatial
integral identity. These jets are not asserted to be periodic solutions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.CurlHelicityCenteringTests

open CurlHelicityCentering LongitudinalHelicityBudget WeightedCurlHelicity
open WeightedCurlCancellationTests WeightedCurlHelicityTests
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem alignedJet_centeredDirectionalDensity (ρ : ℝ) :
    centeredDirectionalDensity ρ a D = (1 - ρ) ^ 2 := by
  have h4 : ‖a‖ ^ 4 = 1 := by
    rw [show ‖a‖ ^ 4 = (‖a‖ ^ 2) ^ 2 by ring, norm_a_sq, one_pow]
  simp only [centeredDirectionalDensity, helicity_one, norm_a_sq, h4, mul_one, one_mul]
  norm_num [longitudinalAmplitude, amplitudeGradientSquare, a, D,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem matching_center_removes_cost : centeredDirectionalDensity 1 a D = 0 := by
  rw [alignedJet_centeredDirectionalDensity]
  norm_num

theorem opposite_center_increases_cost :
    directionalHelicityDensity a D < centeredDirectionalDensity (-1) a D := by
  rw [LongitudinalHelicityBudgetTests.alignedJet_directionalHelicity_one,
    alignedJet_centeredDirectionalDensity]
  norm_num

/-- The valid integrated cancellation cannot be promoted to a pointwise one. -/
theorem centeredDefect_ne_original : centeredDefect 1 a D ≠ longitudinalDefect a D := by
  simp [centeredDefect, helicity_one, norm_a_sq, longitudinalDefect_one]

theorem zero_vorticity (ρ : ℝ) (D : Fin 3 → R3) : centeredDirectionalDensity ρ 0 D = 0 := by
  simp [centeredDirectionalDensity]

end Mettapedia.Analysis.CurlHelicityCenteringTests
