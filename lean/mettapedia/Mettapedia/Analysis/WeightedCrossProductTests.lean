import Mettapedia.Analysis.WeightedCrossProductEvolution

/-!
# Angle damping does not imply weighted angular damping

A symmetric trace-free common strain decreases the normalized angle but
increases the weighted angular energy. These are derivatives of explicit
curves, not asserted to be a spatially self-consistent NS solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedCrossProductTests

open EuclideanCrossProduct WeightedCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def strainMatrix : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 0, -1]
def strain : R3 →L[ℝ] R3 := strainMatrix.toEuclideanLin.toContinuousLinearMap
def leftVector : R3 := WithLp.toLp 2 ![1, 0, 0]
def rightVector : R3 := WithLp.toLp 2 ![1, 1, 0]

theorem strainMatrix_symmetric : strainMatrix.transpose = strainMatrix := by simp [strainMatrix]
theorem strainMatrix_trace : strainMatrix.trace = 0 := by
  norm_num [strainMatrix, Matrix.trace, Fin.sum_univ_succ]

theorem endpoint_norm_sq : ‖leftVector‖ ^ 2 = 1 ∧ ‖rightVector‖ ^ 2 = 2 := by
  norm_num [leftVector, rightVector, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]

theorem cross_norm_sq : ‖cross leftVector rightVector‖ ^ 2 = 1 := by
  norm_num [leftVector, rightVector, cross, cross_apply, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_succ, Matrix.cons_val_two]

theorem energy_value : energy 2 leftVector rightVector = 9 := by
  simp only [energy, amplitudeWeight, show 2 * (2 + 1) = 2 * 3 from rfl,
    pow_mul, endpoint_norm_sq.1, endpoint_norm_sq.2, cross_norm_sq]
  norm_num

theorem energy_rate : rate 2 leftVector rightVector (strain leftVector) (strain rightVector) = 48 := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have ha (n : ℕ) : ‖leftVector‖ ^ (2 * n) = 1 := by rw [pow_mul, endpoint_norm_sq.1]; simp
  have hb (n : ℕ) : ‖rightVector‖ ^ (2 * n) = 2 ^ n := by rw [pow_mul, endpoint_norm_sq.2]
  simp only [rate, amplitudeRate, amplitudeWeight, ha, hb, cross_norm_sq]
  norm_num [strain, strainMatrix, leftVector, rightVector, cross, cross_apply,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, Matrix.mulVec, Matrix.diagonal, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk, h02]

theorem angle_rate : angleRate strain strain leftVector rightVector 0 0 = -(1 / 2 : ℝ) := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  norm_num [angleRate, angleEnergy, pairForcing, strain, strainMatrix, leftVector, rightVector,
    cross, cross_apply, EuclideanSpace.norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, Matrix.mulVec, Matrix.diagonal, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk, h02]

theorem growing_energy_firstVariation :
    HasDerivAt (fun t : ℝ ↦ energy 2
      (leftVector + t • strain leftVector) (rightVector + t • strain rightVector)) 48 0 := by
  have ha := ((hasDerivAt_id (0 : ℝ)).smul_const (strain leftVector)).const_add leftVector
  have hb := ((hasDerivAt_id (0 : ℝ)).smul_const (strain rightVector)).const_add rightVector
  simpa only [id_eq, zero_smul, one_smul, add_zero, energy_rate] using hasDerivAt_energy 2 ha hb

theorem decreasing_angle_firstVariation :
    HasDerivAt (fun t : ℝ ↦ angleEnergy
      (leftVector + t • strain leftVector) (rightVector + t • strain rightVector)) (-(1 / 2 : ℝ)) 0 := by
  have ha0 : leftVector ≠ 0 := by
    intro h
    have hh := endpoint_norm_sq.1
    simp [h] at hh
  have hb0 : rightVector ≠ 0 := by
    intro h
    have hh := endpoint_norm_sq.2
    simp [h] at hh
  have ha := ((hasDerivAt_id (0 : ℝ)).smul_const (strain leftVector)).const_add leftVector
  have hb := ((hasDerivAt_id (0 : ℝ)).smul_const (strain rightVector)).const_add rightVector
  have hc := cross_mulVec_add_mulVec_cross_of_symmetric_trace_zero strainMatrix
    strainMatrix_symmetric strainMatrix_trace leftVector rightVector
  have h := hasDerivAt_angleEnergy_of_strainEquations strain strain 0 0
    (t := 0) (a := fun t : ℝ ↦ leftVector + t • strain leftVector)
    (b := fun t : ℝ ↦ rightVector + t • strain rightVector)
    (by simpa using ha) (by simpa using hb)
    (by simpa using ha0) (by simpa using hb0) (by simpa [strain] using hc)
  simpa only [zero_smul, add_zero, angle_rate] using h

theorem not_weighted_damping_of_angle_damping :
    ¬ ∀ a b : R3, angleRate strain strain a b 0 0 ≤ 0 →
      rate 2 a b (strain a) (strain b) ≤ 0 := by
  intro h
  have hh := h leftVector rightVector (by rw [angle_rate]; norm_num)
  rw [energy_rate] at hh
  norm_num at hh

end Mettapedia.Analysis.WeightedCrossProductTests
