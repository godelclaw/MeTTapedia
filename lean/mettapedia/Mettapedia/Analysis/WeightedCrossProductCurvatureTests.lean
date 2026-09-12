import Mettapedia.Analysis.WeightedCrossProductCurvature

/-!
# Negative curvature of the positive weighted angular energy

An explicit affine endpoint curve has negative second variation. This
refutes pointwise convexity, not the sign of a spatially integrated NS
diffusion term. No spatial solution is asserted by this test.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedCrossProductCurvatureTests

open WeightedCrossProduct EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def leftVector : R3 := WithLp.toLp 2 ![3, 1, 0]
def rightVector : R3 := WithLp.toLp 2 ![1, 0, 0]
def leftVariation : R3 := WithLp.toLp 2 ![1, -1, 0]

theorem endpoint_norm_sq : ‖leftVector‖ ^ 2 = 10 ∧ ‖rightVector‖ ^ 2 = 1 := by
  norm_num [leftVector, rightVector, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]

theorem curvature_value : curvature 1 leftVector rightVector leftVariation 0 = -638 := by
  have ha (n : ℕ) : ‖leftVector‖ ^ (2 * n) = 10 ^ n := by rw [pow_mul, endpoint_norm_sq.1]
  have hb (n : ℕ) : ‖rightVector‖ ^ (2 * n) = 1 := by rw [pow_mul, endpoint_norm_sq.2]; simp
  simp only [curvature, amplitudeCurvature, amplitudeRate, amplitudeWeight, ha, hb]
  norm_num [leftVector, rightVector, leftVariation, cross, cross_apply,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two]

theorem rate_zero (n : ℕ) (a b : R3) : rate n a b 0 0 = 0 := by
  simp [rate, amplitudeRate]

theorem negative_secondVariation :
    HasDerivAt (fun t : ℝ ↦ rate 2 (leftVector + t • leftVariation) rightVector leftVariation 0)
      (-638 : ℝ) 0 := by
  have ha := ((hasDerivAt_id (0 : ℝ)).smul_const leftVariation).const_add leftVector
  have hd := hasDerivAt_rate 1
    (by simpa only [id_eq, one_smul] using ha) (hasDerivAt_const 0 rightVector)
    (hasDerivAt_const 0 leftVariation) (hasDerivAt_const 0 (0 : R3))
  simpa only [zero_smul, add_zero, rate_zero, zero_add, curvature_value] using hd

theorem not_curvature_nonneg : ¬ ∀ a b v w : R3, 0 ≤ curvature 1 a b v w := by
  intro h
  have hh := h leftVector rightVector leftVariation 0
  rw [curvature_value] at hh
  norm_num at hh

end Mettapedia.Analysis.WeightedCrossProductCurvatureTests
