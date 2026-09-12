import Mettapedia.Analysis.CrossProductStrain

/-!
# A growing angle under common incompressible strain

Both endpoint vectors stretch, yet their squared sine increases. This is an
algebraic counterexample to universal angle damping under a prescribed
symmetric trace-free strain, not a Navier–Stokes solution or blowup example.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.CrossProductStrainTests

open EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def strainMatrix : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![2, -1, -1]
def strain : R3 →L[ℝ] R3 := strainMatrix.toEuclideanLin.toContinuousLinearMap
def leftVector : R3 := WithLp.toLp 2 ![3 / 5, 0, 4 / 5]
def rightVector : R3 := WithLp.toLp 2 ![-3 / 5, 0, 4 / 5]

theorem strainMatrix_symmetric : strainMatrix.transpose = strainMatrix := by
  simp [strainMatrix]

theorem strainMatrix_trace : strainMatrix.trace = 0 := by
  norm_num [strainMatrix, Matrix.trace, Fin.sum_univ_succ]

theorem endpoint_norm_sq : ‖leftVector‖ ^ 2 = 1 ∧ ‖rightVector‖ ^ 2 = 1 := by
  norm_num [EuclideanSpace.norm_sq_eq, leftVector, rightVector, Fin.sum_univ_succ]

theorem endpoint_stretch :
    ⟪leftVector, strain leftVector⟫ = 2 / 25 ∧
      ⟪rightVector, strain rightVector⟫ = 2 / 25 := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  norm_num [strain, strainMatrix, leftVector, rightVector, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, Matrix.mulVec, Matrix.diagonal, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk, h02]

theorem angleRate_positive_exact :
    angleRate strain strain leftVector rightVector 0 0 = 24192 / 15625 := by
  have ha : ‖leftVector‖ = 1 := by nlinarith [endpoint_norm_sq.1, norm_nonneg leftVector]
  have hb : ‖rightVector‖ = 1 := by nlinarith [endpoint_norm_sq.2, norm_nonneg rightVector]
  rw [angleRate_common_strain_unit _ _ _ ha hb]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  norm_num [strain, strainMatrix, leftVector, rightVector, cross, cross_apply,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, Matrix.mulVec, Matrix.diagonal, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk, h02]

theorem not_universal_commonStrain_angle_damping :
    ¬ ∀ a b : R3, 0 < ⟪a, strain a⟫ → 0 < ⟪b, strain b⟫ →
      angleRate strain strain a b 0 0 ≤ 0 := by
  intro h
  have hh := h leftVector rightVector (by rw [endpoint_stretch.1]; norm_num)
    (by rw [endpoint_stretch.2]; norm_num)
  rw [angleRate_positive_exact] at hh
  norm_num at hh

/-- The algebraic rate is an actual derivative for curves with the prescribed
strain velocities at zero. These linear curves are only a first-order test;
they are not asserted to solve a fluid equation. -/
theorem growing_angle_firstVariation :
    HasDerivAt (fun t : ℝ ↦ angleEnergy
      (leftVector + t • strain leftVector) (rightVector + t • strain rightVector))
      (24192 / 15625) 0 := by
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
  have hh := hasDerivAt_angleEnergy_of_strainEquations strain strain 0 0
    (t := 0)
    (a := fun t : ℝ ↦ leftVector + t • strain leftVector)
    (b := fun t : ℝ ↦ rightVector + t • strain rightVector)
    (by simpa using ha) (by simpa using hb)
    (by simpa using ha0) (by simpa using hb0) (by simpa [strain] using hc)
  simpa only [zero_smul, add_zero, angleRate_positive_exact] using hh

#print axioms strainMatrix_symmetric
#print axioms strainMatrix_trace
#print axioms endpoint_stretch
#print axioms angleRate_positive_exact
#print axioms not_universal_commonStrain_angle_damping
#print axioms growing_angle_firstVariation

end Mettapedia.Analysis.CrossProductStrainTests
