import Mettapedia.Analysis.SignedCrossKernelCurvatureIncrement

/-!
# Curvature signs at equal endpoint values

Positive rank-one kernels give both signs, even with equal unit endpoint
values and a transverse gradient increment. These are algebraic tests,
not self-consistent fluid solutions or claims about an integrated source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernelCurvatureSignTests

open SignedCrossKernel EuclideanCrossProduct RadialPower
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def direction : R3 := WithLp.toLp 2 ![1, 0, 0]
def increment : R3 := WithLp.toLp 2 ![0, 1, 0]
def axis (c : ℝ) : R3 := WithLp.toLp 2 ![0, 1, c]
def kernel (c : ℝ) : R3 →L[ℝ] R3 := InnerProductSpace.rankOne ℝ (axis c) (axis c)

theorem kernel_nonneg (c : ℝ) (v : R3) : 0 ≤ ⟪v, kernel c v⟫ := by
  simp only [kernel, InnerProductSpace.rankOne_apply, real_inner_smul_right]
  rw [real_inner_comm (axis c) v]
  exact mul_self_nonneg _

theorem direction_norm : ‖direction‖ = 1 := by
  have hs : ‖direction‖ ^ 2 = 1 := by
    norm_num [direction, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  nlinarith [norm_nonneg direction]

theorem transverse_increment : ⟪direction, increment⟫ = 0 := by
  norm_num [direction, increment, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]

theorem curvature_value (c : ℝ) :
    pairedCurvature 1 (kernel c) direction direction increment 0 = -2 * c := by
  rw [pairedCurvature_same_value]
  simp only [sub_zero, evenRadialRate, direction_norm, one_pow, one_smul,
    transverse_increment, mul_zero, zero_smul, add_zero]
  norm_num [direction, increment, kernel, axis, cross, cross_apply,
    InnerProductSpace.rankOne_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem exists_positive_kernel_negative_curvature :
    ∃ H : R3 →L[ℝ] R3, (∀ v, 0 ≤ ⟪v, H v⟫) ∧
      pairedCurvature 1 H direction direction increment 0 < 0 := by
  refine ⟨kernel 1, kernel_nonneg 1, ?_⟩
  rw [curvature_value]
  norm_num

theorem exists_positive_kernel_positive_curvature :
    ∃ H : R3 →L[ℝ] R3, (∀ v, 0 ≤ ⟪v, H v⟫) ∧
      0 < pairedCurvature 1 H direction direction increment 0 := by
  refine ⟨kernel (-1), kernel_nonneg (-1), ?_⟩
  rw [curvature_value]
  norm_num

end Mettapedia.Analysis.SignedCrossKernelCurvatureSignTests
