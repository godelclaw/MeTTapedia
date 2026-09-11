import Mettapedia.Analysis.OrthonormalOperatorBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBoundaryEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMaterialDiffusionBudget

/-!
# Spatial operator energy of finite matrix Fourier fields

Applying Parseval to matrix columns bounds the squared real operator norm
by the sum of squared complex coefficients. Neither the number of modes
nor the matrix dimension appears as an additional multiplier.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierMatrixEnergy

open MeasureTheory
open scoped Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFourierPressureStrain
open PancakeFourierMaterialPaths PancakeFrequencyProjectorCommutator
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakeBoundaryEnergy PancakeViscousMisalignmentAbsorption

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def matrixEnergy (A : MatrixCoefficient) : ℝ := ∑ j : Fin 3, ∑ i : Fin 3, ‖A i j‖ ^ 2

theorem matrixEnergy_nonneg (A : MatrixCoefficient) : 0 ≤ matrixEnergy A :=
  Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

theorem matrixEnergy_smul (c : ℂ) (A : MatrixCoefficient) :
    matrixEnergy (c • A) = ‖c‖ ^ 2 * matrixEnergy A := by
  simp only [matrixEnergy, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem matrixEnergy_transpose (A : MatrixCoefficient) : matrixEnergy A.transpose = matrixEnergy A := by
  exact Finset.sum_comm

theorem matrixEnergy_symmetrize_le (A : MatrixCoefficient) :
    matrixEnergy ((1 / 2 : ℂ) • (A + A.transpose)) ≤ matrixEnergy A := by
  have he (a b : ℂ) : ‖(1 / 2 : ℂ) * (a + b)‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
    rw [norm_mul]
    norm_num
    have h := pow_le_pow_left₀ (norm_nonneg (a + b)) (norm_add_le a b) 2
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  calc
    _ ≤ ∑ j : Fin 3, ∑ i : Fin 3, (‖A i j‖ ^ 2 + ‖A j i‖ ^ 2) / 2 :=
      Finset.sum_le_sum (fun j _ ↦ Finset.sum_le_sum (fun i _ ↦ he _ _))
    _ = (matrixEnergy A + matrixEnergy A.transpose) / 2 := by
      simp only [matrixEnergy, Matrix.transpose_apply, ← Finset.sum_div, Finset.sum_add_distrib]
    _ = _ := by rw [matrixEnergy_transpose]; ring

theorem realMatrixOperator_basisFun (A : MatrixCoefficient) (j : Fin 3) :
    realMatrixOperator A (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      complexRealPartEuclidean (fun i ↦ A i j) := by
  ext i
  simp [realMatrixOperator_apply, EuclideanSpace.basisFun_apply,
    complexRealPartEuclidean]

theorem matrixReconstruction_column (modes : Finset Wavevector) (A : FourierMatrix)
    (x : T3) (j : Fin 3) :
    (fun i ↦ matrixReconstruction modes A x i j) =
      finiteFourierReconstruction modes (fun q i ↦ A q i j) x := by
  funext i
  simp [matrixReconstruction, finiteFourierReconstruction, Matrix.sum_apply]

theorem continuous_operatorField (modes : Finset Wavevector) (A : FourierMatrix) :
    Continuous (fun x : T3 ↦ realMatrixOperator (matrixReconstruction modes A x)) :=
  realMatrixOperatorCLM.continuous.comp
    (PancakeMaterialDiffusionBudget.continuous_matrixReconstruction modes A)

theorem integral_operator_norm_sq_le (modes : Finset Wavevector) (A : FourierMatrix) :
    (∫ x : T3, ‖realMatrixOperator (matrixReconstruction modes A x)‖ ^ 2) ≤
      ∑ q ∈ modes, matrixEnergy (A q) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hi : Integrable (fun x : T3 ↦ ‖realMatrixOperator (matrixReconstruction modes A x)‖ ^ 2) :=
    ((continuous_operatorField modes A).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiB (j : Fin 3) : Integrable (fun x : T3 ↦
      ‖realMatrixOperator (matrixReconstruction modes A x) (b j)‖ ^ 2) :=
    (((continuous_operatorField modes A).clm_apply continuous_const).norm.pow 2
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hi (integrable_finsetSum Finset.univ (fun j _ ↦ hiB j))
    (fun x ↦ (realMatrixOperator (matrixReconstruction modes A x)).norm_sq_le_sum_orthonormalBasis b)
  rw [integral_finsetSum _ (fun j _ ↦ hiB j)] at h
  apply h.trans
  calc
    _ ≤ ∑ j : Fin 3, fullEnergy modes (fun q i ↦ A q i j) := by
      apply Finset.sum_le_sum
      intro j _
      simp_rw [b, realMatrixOperator_basisFun, matrixReconstruction_column]
      exact integral_real_reconstruction_energy_le modes _
    _ = _ := by
      simp only [fullEnergy, coefficientEnergy, Complex.normSq_eq_norm_sq]
      rw [Finset.sum_comm]
      rfl

end Mettapedia.FluidDynamics.NavierStokes.FourierMatrixEnergy
