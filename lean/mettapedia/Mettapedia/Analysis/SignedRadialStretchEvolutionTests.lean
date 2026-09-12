import Mettapedia.Analysis.SignedRadialStretchEvolution
import Mettapedia.Analysis.WeightedCrossProductTests
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Conservation of the triple product is not damping of the full source

A trace-free common strain keeps the scalar triple product fixed while
the full signed radial density grows. This is a finite-dimensional product
rule test with a fixed scalar coefficient, not a spatial NS solution or
an asserted value of the constructed Fourier kernel.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedRadialStretchEvolutionTests

open EuclideanCrossProduct WeightedCrossProductTests SignedRadialStretch
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def separationVector : R3 := WithLp.toLp 2 ![0, -1, 1]

theorem tripleProduct_value : tripleProduct leftVector rightVector separationVector = 1 := by
  norm_num [tripleProduct, cross, cross_apply, leftVector, rightVector, separationVector,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two]

theorem amplitudePair_value : amplitudePair 6 leftVector rightVector separationVector = 8 := by
  have ha : ‖leftVector‖ ^ 6 = 1 := by rw [show 6 = 2 * 3 from rfl, pow_mul, endpoint_norm_sq.1]; norm_num
  have hb : ‖rightVector‖ ^ 6 = 8 := by
    calc
      _ = (‖rightVector‖ ^ 2) ^ 3 := (pow_mul _ _ _)
      _ = 8 := by rw [endpoint_norm_sq.2]; norm_num
  simp only [amplitudePair, RadialPower.radialPower, ha, hb]
  norm_num [leftVector, rightVector, separationVector, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_succ]

theorem amplitudeRate_value :
    amplitudeRate 2 leftVector rightVector separationVector
      (strain leftVector) (strain rightVector) (strain separationVector) = 24 := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have ha (n : ℕ) : ‖leftVector‖ ^ (2 * n) = 1 := by rw [pow_mul, endpoint_norm_sq.1]; simp
  have hb (n : ℕ) : ‖rightVector‖ ^ (2 * n) = 2 ^ n := by rw [pow_mul, endpoint_norm_sq.2]
  simp only [amplitudeRate, RadialPower.radialPower, RadialPower.evenRadialRate, ha, hb]
  norm_num [strain, strainMatrix, leftVector, rightVector, separationVector,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, Matrix.mulVec, Matrix.diagonal,
    dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk, h02]
  decide

theorem rate_value (k dk : ℝ) :
    SignedRadialStretch.rate 2 k dk leftVector rightVector separationVector
      (strain leftVector) (strain rightVector) (strain separationVector) = 8 * dk + 24 * k := by
  have ht : tripleRate leftVector rightVector separationVector
      (strain leftVector) (strain rightVector) (strain separationVector) = 0 := by
    simpa only [strain, LinearMap.coe_toContinuousLinearMap', strainMatrix_trace, zero_mul] using
      tripleRate_common strainMatrix leftVector rightVector separationVector
  simp only [SignedRadialStretch.rate, residualRate, ht, tripleProduct_value, amplitudeRate_value,
    show 2 * (2 + 1) = 6 from rfl, amplitudePair_value]
  ring

theorem conserved_tripleProduct_growing_density :
    tripleRate leftVector rightVector separationVector
      (strain leftVector) (strain rightVector) (strain separationVector) = 0 ∧
    SignedRadialStretch.rate 2 1 0 leftVector rightVector separationVector
      (strain leftVector) (strain rightVector) (strain separationVector) = 24 := by
  constructor
  · simpa only [strain, LinearMap.coe_toContinuousLinearMap', strainMatrix_trace, zero_mul] using
      tripleRate_common strainMatrix leftVector rightVector separationVector
  · norm_num [rate_value]

theorem growing_density_firstVariation :
    HasDerivAt (fun t : ℝ ↦ density 6 1
      (leftVector + t • strain leftVector) (rightVector + t • strain rightVector)
      (separationVector + t • strain separationVector)) 24 0 := by
  have ha := ((hasDerivAt_id (0 : ℝ)).smul_const (strain leftVector)).const_add leftVector
  have hb := ((hasDerivAt_id (0 : ℝ)).smul_const (strain rightVector)).const_add rightVector
  have hh := ((hasDerivAt_id (0 : ℝ)).smul_const (strain separationVector)).const_add separationVector
  simpa only [id_eq, zero_smul, one_smul, add_zero, rate_value, mul_zero, mul_one, zero_add] using
    hasDerivAt_density 2 ha hb hh (hasDerivAt_const (0 : ℝ) (1 : ℝ))

def homogeneousSeparation : R3 := WithLp.toLp 2 ![0, 1, 1]

/-- A negative inverse-fifth-power coefficient, normalized to `-1` at
the test separation. It is not the cutoff-dependent Fourier kernel. -/
def homogeneousCoefficient (h : R3) : ℝ := -(‖h‖ ^ 2 / 2) ^ (-(5 / 2 : ℝ))

theorem homogeneous_initial_values :
    tripleProduct leftVector rightVector homogeneousSeparation = 1 ∧
    amplitudePair 6 leftVector rightVector homogeneousSeparation = -8 ∧
    amplitudeRate 2 leftVector rightVector homogeneousSeparation
      (strain leftVector) (strain rightVector) (strain homogeneousSeparation) = -24 ∧
    ‖homogeneousSeparation‖ ^ 2 = 2 ∧
    ⟪homogeneousSeparation, strain homogeneousSeparation⟫ = -1 := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have ha (n : ℕ) : ‖leftVector‖ ^ (2 * n) = 1 := by rw [pow_mul, endpoint_norm_sq.1]; simp
  have hb (n : ℕ) : ‖rightVector‖ ^ (2 * n) = 2 ^ n := by rw [pow_mul, endpoint_norm_sq.2]
  simp only [amplitudePair, amplitudeRate, RadialPower.radialPower, RadialPower.evenRadialRate,
    show 6 = 2 * 3 from rfl, ha, hb]
  norm_num [tripleProduct, cross, cross_apply, strain, strainMatrix, leftVector, rightVector,
    homogeneousSeparation, EuclideanSpace.norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, Matrix.mulVec, Matrix.diagonal, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk, h02]
  decide

theorem homogeneous_rate_value (k dk : ℝ) :
    SignedRadialStretch.rate 2 k dk leftVector rightVector homogeneousSeparation
      (strain leftVector) (strain rightVector) (strain homogeneousSeparation) = -8 * dk - 24 * k := by
  have ht : tripleRate leftVector rightVector homogeneousSeparation
      (strain leftVector) (strain rightVector) (strain homogeneousSeparation) = 0 := by
    simpa only [strain, LinearMap.coe_toContinuousLinearMap', strainMatrix_trace, zero_mul] using
      tripleRate_common strainMatrix leftVector rightVector homogeneousSeparation
  simp only [SignedRadialStretch.rate, residualRate, ht, homogeneous_initial_values.1,
    homogeneous_initial_values.2.2.1, show 2 * (2 + 1) = 6 from rfl,
    homogeneous_initial_values.2.1]
  ring

theorem homogeneous_coefficient_firstVariation :
    HasDerivAt (fun t : ℝ ↦ homogeneousCoefficient
      (homogeneousSeparation + t • strain homogeneousSeparation)) (-(5 / 2 : ℝ)) 0 := by
  have hh := ((hasDerivAt_id (0 : ℝ)).smul_const (strain homogeneousSeparation)).const_add homogeneousSeparation
  have hn : HasDerivAt (fun t : ℝ ↦ ‖homogeneousSeparation + t • strain homogeneousSeparation‖ ^ 2 / 2)
      (-1 : ℝ) 0 := by
    apply (hh.norm_sq.div_const 2).congr_deriv
    norm_num [homogeneous_initial_values.2.2.2.2]
  have hk := (hn.rpow_const (p := -(5 / 2 : ℝ)) (Or.inl (by
    norm_num [homogeneous_initial_values.2.2.2.1]))).const_mul (-1 : ℝ)
  simpa [homogeneousCoefficient, homogeneous_initial_values.2.2.2.1] using hk

theorem homogeneous_density_value :
    density 6 (homogeneousCoefficient homogeneousSeparation) leftVector rightVector homogeneousSeparation = 8 := by
  norm_num [density, homogeneousCoefficient, homogeneous_initial_values.1,
    homogeneous_initial_values.2.1, homogeneous_initial_values.2.2.2.1]

/-- Kernel motion reinforces, rather than cancels, growth in this
homogeneous radial example. This remains an algebraic test, not NS data. -/
theorem homogeneous_growing_density_firstVariation :
    HasDerivAt (fun t : ℝ ↦ density 6
      (homogeneousCoefficient (homogeneousSeparation + t • strain homogeneousSeparation))
      (leftVector + t • strain leftVector) (rightVector + t • strain rightVector)
      (homogeneousSeparation + t • strain homogeneousSeparation)) 44 0 := by
  have ha := ((hasDerivAt_id (0 : ℝ)).smul_const (strain leftVector)).const_add leftVector
  have hb := ((hasDerivAt_id (0 : ℝ)).smul_const (strain rightVector)).const_add rightVector
  have hh := ((hasDerivAt_id (0 : ℝ)).smul_const (strain homogeneousSeparation)).const_add homogeneousSeparation
  have h := hasDerivAt_density 2 ha hb hh homogeneous_coefficient_firstVariation
  norm_num only [id_eq, zero_smul, one_smul, add_zero, homogeneous_rate_value, homogeneousCoefficient,
    homogeneous_initial_values.2.2.2.1, Real.one_rpow] at h
  exact h

end Mettapedia.Analysis.SignedRadialStretchEvolutionTests
