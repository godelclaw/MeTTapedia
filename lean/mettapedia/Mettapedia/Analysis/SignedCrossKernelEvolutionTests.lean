import Mettapedia.Analysis.SignedCrossKernelEvolution
import Mettapedia.Analysis.CrossProductStrainTests

/-!
# Decreasing angle with an increasing radial-weighted source

An exact first-order test under prescribed common trace-free strain and a
fixed positive rank-one kernel. This is not a self-consistent NS solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernelEvolutionTests

open SignedCrossKernel EuclideanCrossProduct RadialPower
open CrossProductStrainTests (strain strainMatrix strainMatrix_symmetric strainMatrix_trace)
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def a : R3 := WithLp.toLp 2 ![4 / 5, 0, 3 / 5]
def b : R3 := WithLp.toLp 2 ![4 / 5, 0, -3 / 5]
def e : R3 := WithLp.toLp 2 ![0, 1, 1]
def H : R3 →L[ℝ] R3 := InnerProductSpace.rankOne ℝ e e

theorem endpoint_norms : ‖a‖ = 1 ∧ ‖b‖ = 1 := by
  have ha : ‖a‖ ^ 2 = 1 := by norm_num [a, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  have hb : ‖b‖ ^ 2 = 1 := by norm_num [b, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  constructor <;> nlinarith [norm_nonneg a, norm_nonneg b]

theorem endpoint_rayleigh : ⟪a, strain a⟫ = 23 / 25 ∧ ⟪b, strain b⟫ = 23 / 25 := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  norm_num [a, b, strain, strainMatrix, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, Matrix.mulVec, Matrix.diagonal, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk, h02]

theorem kernel_commutes_strain : H * strain = strain * H := by
  ext v i
  fin_cases i <;>
    simp [H, e, strain, strainMatrix, InnerProductSpace.rankOne_apply, Matrix.toLpLin_apply,
      EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.diagonal, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem source_value : pairedStretch 6 H a b = 144 / 125 := by
  simp only [pairedStretch, radialPower, endpoint_norms.1, endpoint_norms.2, one_pow, one_smul]
  norm_num [a, b, H, e, cross, cross_apply, InnerProductSpace.rankOne_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk]

theorem angle_rate_negative : angleRate strain strain a b 0 0 = -24192 / 15625 := by
  rw [angleRate_common_strain_unit _ _ _ endpoint_norms.1 endpoint_norms.2]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  norm_num [strain, strainMatrix, a, b, cross, cross_apply, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, Matrix.mulVec, Matrix.diagonal,
    dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk, h02]

theorem weighted_source_rate_positive : pairedStretchRate 2 strain strain H 0 a b 0 0 = 19872 / 3125 := by
  rw [pairedStretchRate_common_of_equal_rayleigh 2 strain H a b (23 / 25)
    kernel_commutes_strain (by simp only [endpoint_norms.1, one_pow, mul_one]; exact endpoint_rayleigh.1)
      (by simp only [endpoint_norms.2, one_pow, mul_one]; exact endpoint_rayleigh.2)]
  norm_num [source_value]

def aCurve (t : ℝ) : R3 := a + t • strain a
def bCurve (t : ℝ) : R3 := b + t • strain b

theorem hasDerivAt_aCurve : HasDerivAt aCurve (strain a) 0 := by
  unfold aCurve
  simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (strain a)).const_add a

theorem hasDerivAt_bCurve : HasDerivAt bCurve (strain b) 0 := by
  unfold bCurve
  simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (strain b)).const_add b

theorem meanStrain_symmetric (v w : R3) : ⟪meanStrain strain strain v, w⟫ = ⟪v, meanStrain strain strain w⟫ := by
  rw [meanStrain_self]
  simp [strain, strainMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.diagonal, Fin.sum_univ_succ]
  ring

theorem source_firstVariation :
    HasDerivAt (fun t : ℝ ↦ pairedStretch 6 H (aCurve t) (bCurve t)) (19872 / 3125) 0 := by
  have h := hasDerivAt_pairedStretch 2 (t := 0) strain strain 0 0 0
    (a := aCurve) (b := bCurve) (H := fun _ ↦ H)
    (by simpa [aCurve] using hasDerivAt_aCurve) (by simpa [bCurve] using hasDerivAt_bCurve)
    (hasDerivAt_const 0 H)
    (by simpa [aCurve, bCurve, strain] using
      cross_mulVec_add_mulVec_cross_of_symmetric_trace_zero strainMatrix strainMatrix_symmetric strainMatrix_trace a b)
    (by simpa [aCurve, bCurve, strain] using
      cross_mulVec_add_mulVec_cross_of_symmetric_trace_zero strainMatrix strainMatrix_symmetric strainMatrix_trace b a)
    meanStrain_symmetric
  simpa only [aCurve, bCurve, zero_smul, add_zero, weighted_source_rate_positive] using h

theorem angle_firstVariation :
    HasDerivAt (fun t : ℝ ↦ angleEnergy (aCurve t) (bCurve t)) (-24192 / 15625) 0 := by
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [endpoint_norms.1]; norm_num)
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (by rw [endpoint_norms.2]; norm_num)
  have h := hasDerivAt_angleEnergy_of_strainEquations strain strain 0 0 (t := 0)
    (a := aCurve) (b := bCurve)
    (by simpa [aCurve] using hasDerivAt_aCurve) (by simpa [bCurve] using hasDerivAt_bCurve)
    (by simpa [aCurve] using ha0) (by simpa [bCurve] using hb0)
    (by simpa [aCurve, bCurve, strain] using
      cross_mulVec_add_mulVec_cross_of_symmetric_trace_zero strainMatrix strainMatrix_symmetric strainMatrix_trace a b)
  simpa only [aCurve, bCurve, zero_smul, add_zero, angle_rate_negative] using h

theorem not_source_damping_of_angle_damping :
    ¬ ∀ v w : R3, angleRate strain strain v w 0 0 < 0 →
      pairedStretchRate 2 strain strain H 0 v w 0 0 ≤ 0 := by
  intro h
  have hh := h a b (by rw [angle_rate_negative]; norm_num)
  rw [weighted_source_rate_positive] at hh
  norm_num at hh

#print axioms kernel_commutes_strain
#print axioms source_value
#print axioms angle_rate_negative
#print axioms weighted_source_rate_positive
#print axioms source_firstVariation
#print axioms angle_firstVariation
#print axioms not_source_damping_of_angle_damping

end Mettapedia.Analysis.SignedCrossKernelEvolutionTests
