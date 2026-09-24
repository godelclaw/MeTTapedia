import Mettapedia.Analysis.WeightedProjectionParabolic
import Mettapedia.Analysis.WeightedCurlCancellation

/-!
# Signed weighted curvature on curl-compatible jets

Both first jets are trace-free and the second field is the curl of the
first jet. Their weighted curvature can still be negative, even with
zero first derivative of the projection coefficient. These are algebraic
compatibility tests, not constructed periodic solutions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedProjectionParabolicTests

open scoped RealInnerProductSpace
open WeightedProjectionParabolic RegularizedProjectionParabolic RegularizedProjection
open WeightedCurlCancellation
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def vorticityJet : Fin 3 → R3 :=
  ![WithLp.toLp 2 ![1, 1, 0], WithLp.toLp 2 ![0, -1, 0], 0]

def curlVorticityJet : Fin 3 → R3 := ![WithLp.toLp 2 ![0, 0, -6], 0, 0]

theorem vorticityJet_trace : (∑ j : Fin 3, vorticityJet j j) = 0 := by
  norm_num [vorticityJet, Fin.sum_univ_three, Matrix.cons_val_two]

theorem curlVorticityJet_trace : (∑ j : Fin 3, curlVorticityJet j j) = 0 := by
  norm_num [curlVorticityJet, Fin.sum_univ_three, Matrix.cons_val_two]

theorem vorticityJet_curl : curlJet vorticityJet = EuclideanSpace.single 2 1 := by
  ext i
  fin_cases i <;> simp [curlJet, vorticityJet, Matrix.cons_val_two]

theorem centerRate_zero (j : Fin 3) :
    coefficientRate 1 (EuclideanSpace.single 0 1) (curlJet vorticityJet)
      (vorticityJet j) (curlVorticityJet j) = 0 := by
  rw [vorticityJet_curl]
  fin_cases j <;>
    simp [coefficientRate, coefficient, vorticityJet, curlVorticityJet,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem weightedCurvature_sum_negative :
    (∑ j : Fin 3, weightedCurvature 1 (EuclideanSpace.single 0 1) (curlJet vorticityJet)
      (vorticityJet j) (curlVorticityJet j)) = -30 := by
  rw [vorticityJet_curl]
  norm_num [weightedCurvature, energyCurvature, energyRate, coefficientRate, energy,
    RegularizedProjection.residual, coefficient, vorticityJet, curlVorticityJet,
    PiLp.norm_single, Pi.single_apply, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  simp
  norm_num

theorem weightedCurvature_zero_first_field (δ : ℝ) (b v z : R3) :
    weightedCurvature δ (0 : R3) b v z = 0 := by
  simp [weightedCurvature]

end Mettapedia.Analysis.WeightedProjectionParabolicTests
