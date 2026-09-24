import Mettapedia.Analysis.OrthonormalOperatorBound
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Euclidean coordinates for real operators

Flattening the matrix in an orthonormal basis produces a genuine Hilbert
space target. Its norm dominates the operator norm; its squared norm is
at most the dimension times the squared operator norm. No matrix-norm
instance is changed in the surrounding development.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.EuclideanOperatorCoordinates

open scoped BigOperators RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => EuclideanSpace ℝ ι

def coordinatesLinear : (E →L[ℝ] E) →ₗ[ℝ] EuclideanSpace ℝ (ι × ι) where
  toFun A := WithLp.toLp 2 (fun ij ↦ A ((EuclideanSpace.basisFun ι ℝ) ij.1) ij.2)
  map_add' A B := by ext ij; simp
  map_smul' r A := by ext ij; simp

def coordinates : (E →L[ℝ] E) →L[ℝ] EuclideanSpace ℝ (ι × ι) :=
  coordinatesLinear.toContinuousLinearMap

theorem norm_coordinates_sq (A : E →L[ℝ] E) :
    ‖coordinates A‖ ^ 2 = ∑ i, ‖A ((EuclideanSpace.basisFun ι ℝ) i)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.norm_sq_eq]
  rfl

theorem norm_le_coordinates (A : E →L[ℝ] E) : ‖A‖ ≤ ‖coordinates A‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_coordinates_sq]
  exact A.norm_sq_le_sum_orthonormalBasis (EuclideanSpace.basisFun ι ℝ)

theorem norm_coordinates_sq_le (A : E →L[ℝ] E) :
    ‖coordinates A‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ‖A‖ ^ 2 := by
  rw [norm_coordinates_sq]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm ((EuclideanSpace.basisFun ι ℝ) i)) 2)
  simpa only [(EuclideanSpace.basisFun ι ℝ).norm_eq_one, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

theorem norm_coordinates_rankOne (e : E) (he : ‖e‖ = 1) :
    ‖coordinates (InnerProductSpace.rankOne ℝ e e)‖ = 1 := by
  have hid : ‖coordinates (InnerProductSpace.rankOne ℝ e e)‖ ^ 2 = 1 := by
    rw [norm_coordinates_sq]
    simp only [InnerProductSpace.rankOne_apply, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
    rw [(EuclideanSpace.basisFun ι ℝ).sum_sq_inner_left, he, one_pow]
  nlinarith only [hid, norm_nonneg (coordinates (InnerProductSpace.rankOne ℝ e e))]

end Mettapedia.Analysis.EuclideanOperatorCoordinates
