import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic.Module

/-!
# Rank-one commutators with symmetric operators

Only the part of `T q` transverse to `q` contributes to the commutator
with `rankOne ℝ q q`. Subtracting any scalar multiple of `q` is exact.
No finite-dimensionality, completeness or spectral-gap assumption is used.
-/

set_option autoImplicit false
noncomputable section

namespace InnerProductSpace

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem rankOne_commutator (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) (x y : E) :
    T * rankOne ℝ x y - rankOne ℝ x y * T =
      rankOne ℝ (T x) y - rankOne ℝ x (T y) := by
  ext z
  simp only [sub_apply, mul_apply_eq_comp, rankOne_apply, map_smul]
  have h : ⟪T y, z⟫ = ⟪y, T z⟫ := hT y z
  rw [h]

theorem rankOne_self_commutator_eq_shifted (T : E →L[ℝ] E)
    (hT : T.toLinearMap.IsSymmetric) (q : E) (a : ℝ) :
    T * rankOne ℝ q q - rankOne ℝ q q * T =
      rankOne ℝ (T q - a • q) q - rankOne ℝ q (T q - a • q) := by
  rw [rankOne_commutator T hT]
  ext z
  simp only [sub_apply, rankOne_apply, inner_sub_left, real_inner_smul_left, smul_sub,
    sub_smul, smul_smul]
  module

theorem norm_rankOne_self_commutator_le (T : E →L[ℝ] E)
    (hT : T.toLinearMap.IsSymmetric) (q : E) (a : ℝ) :
    ‖T * rankOne ℝ q q - rankOne ℝ q q * T‖ ≤ 2 * ‖q‖ * ‖T q - a • q‖ := by
  rw [rankOne_self_commutator_eq_shifted T hT q a]
  calc
    _ ≤ ‖rankOne ℝ (T q - a • q) q‖ + ‖rankOne ℝ q (T q - a • q)‖ := norm_sub_le _ _
    _ = _ := by simp only [norm_rankOne]; ring

theorem rankOne_self_commutes_of_eigenvector (T : E →L[ℝ] E)
    (hT : T.toLinearMap.IsSymmetric) (q : E) (a : ℝ) (hq : T q = a • q) :
    T * rankOne ℝ q q = rankOne ℝ q q * T := by
  apply sub_eq_zero.mp
  rw [rankOne_self_commutator_eq_shifted T hT q a, hq, sub_self]
  simp

end InnerProductSpace
