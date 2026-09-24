import Mettapedia.Analysis.SquaredWeightLocalization
import Mettapedia.Analysis.ScaledPartitionDerivative

/-! Regressions for the sign condition, nonzero complex errors, and the gate derivative. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SquaredWeightLocalizationTests

open SquaredWeightLocalization ScaledPartitionDerivative

local notation "Op" => ℂ →L[ℂ] ℂ →L[ℂ] ℂ
local instance : NormedAddCommGroup (ℂ →L[ℂ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (ℂ →L[ℂ] ℂ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup

/-- The scalar inequality allows a zero input weight and is sharp there. -/
example : (1 - (0 : ℝ) * 1) ^ 2 ≤ (1 - (0 : ℝ) ^ 2) ^ 2 + (1 - (1 : ℝ) ^ 2) ^ 2 :=
  sq_sub_mul_le 1 0 1 (by norm_num)

/-- Opposite signs invalidate the estimate: the left side is four and the right side zero. -/
example : ¬((1 - (1 : ℝ) * (-1)) ^ 2 ≤
    (1 - (1 : ℝ) ^ 2) ^ 2 + (1 - (-1 : ℝ) ^ 2) ^ 2) := by norm_num

/-- Multiplication on complex inputs has a genuinely nonzero localization error. -/
example : ‖((1 : ℂ) * 1) • (ContinuousLinearMap.mul ℂ ℂ) Complex.I 1 -
    (ContinuousLinearMap.mul ℂ ℂ) ((0 : ℂ) • Complex.I) ((1 : ℂ) • 1)‖ ^ 2 = 1 := by
  simp

/-- Both patches contribute; summing the squared errors does not introduce another factor two. -/
example : (∑ _i : Fin 2, ‖((1 : ℂ) * 1) • (ContinuousLinearMap.mul ℂ ℂ) Complex.I 1 -
    (ContinuousLinearMap.mul ℂ ℂ) ((0 : ℂ) • Complex.I) ((1 : ℂ) • 1)‖ ^ 2) =
      ∑ _i : Fin 2, ((1 - (0 : ℝ) ^ 2) ^ 2 + (1 - (1 : ℝ) ^ 2) ^ 2) := by
  simp

/-- The operator theorem also applies to two imaginary inputs. -/
example : ‖((2 : ℂ) * 2) • (ContinuousLinearMap.mul ℂ ℂ) Complex.I Complex.I -
    (ContinuousLinearMap.mul ℂ ℂ) ((1 : ℂ) • Complex.I) ((3 : ℂ) • Complex.I)‖ ^ 2 ≤
      ‖ContinuousLinearMap.mul ℂ ℂ‖ ^ 2 * ‖Complex.I‖ ^ 2 * ‖Complex.I‖ ^ 2 *
        ((2 ^ 2 - (1 : ℝ) ^ 2) ^ 2 + (2 ^ 2 - (3 : ℝ) ^ 2) ^ 2) :=
  norm_localization_sq_le (ContinuousLinearMap.mul ℂ ℂ) 2 1 3 (by norm_num) Complex.I Complex.I

/-- Both the common gate and each patch vary, so both derivative costs are present. -/
example : (∑ _i : Fin 2, deriv (fun t : ℝ ↦ t * t) 1 ^ 2) ≤ 8 := by
  convert! sum_deriv_mul_sq_le (Finset.univ : Finset (Fin 2))
    (hasDerivAt_id (1 : ℝ)) (fun _ _ ↦ hasDerivAt_id (1 : ℝ)) using 1
  norm_num

/-- The preceding derivative bound is attained. -/
example : (∑ _i : Fin 2, deriv (fun t : ℝ ↦ t * t) 1 ^ 2) = 8 := by
  have hd : deriv (fun t : ℝ ↦ t * t) 1 = 2 := by
    convert! ((hasDerivAt_id (1 : ℝ)).fun_mul (hasDerivAt_id 1)).deriv using 1
    norm_num
  rw [hd]
  norm_num

end Mettapedia.Analysis.SquaredWeightLocalizationTests

#print axioms Mettapedia.Analysis.SquaredWeightLocalization.squaredWeight_defect_identity
#print axioms Mettapedia.Analysis.SquaredWeightLocalization.sq_sub_mul_le
#print axioms Mettapedia.Analysis.SquaredWeightLocalization.sum_sq_sub_mul_le
#print axioms Mettapedia.Analysis.SquaredWeightLocalization.norm_localization_sq_le
#print axioms Mettapedia.Analysis.SquaredWeightLocalization.sum_norm_localization_sq_le
#print axioms Mettapedia.Analysis.ScaledPartitionDerivative.sum_deriv_mul_sq_le
