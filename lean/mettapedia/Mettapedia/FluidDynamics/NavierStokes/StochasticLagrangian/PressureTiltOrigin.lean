import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltDatum
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierFiniteSupport

/-!
# Physical first jet and pressure Hessian of the pressure-tilt datum

All fields are reconstructed from `PressureTiltDatum.velocity`. The full
spatial curl is identified through finite support, and the pressure is the
one determined by the Fourier Poisson operator.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTiltOrigin

open scoped BigOperators ComplexConjugate RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeGalerkinKineticEnergy
open PancakePeriodicVorticityEquation PancakePhysicalSpectralDefect
open PancakeTransverseEnergyFreezing LocalLowDiffusionBudget
open PancakePeriodicComplexStretch PancakeInfinitePressureHessian PancakeInfiniteSpatialPressure
open PancakeInfiniteFourierDerivative
open PancakeCurlOutputTail PancakeLocalProjectedEquation PancakeSpatialCoefficientRecovery
open PressureTiltDatum FourierFiniteSupport

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

def diagonalDirection : R3 := WithLp.toLp 2 ![1, 1, 1]

theorem mFourier_origin (q : Wavevector) : UnitAddTorus.mFourier q 0 = 1 := by
  simp [UnitAddTorus.mFourier]

theorem velocity_moments (epsilon : ℝ) (s : ℕ) : Summable (fourierMoment s (velocity epsilon)) :=
  summable_fourierMoment modes (velocity epsilon) (velocity_eq_zero_of_not_mem epsilon) s

theorem fullVelocity_real (epsilon : ℝ) (x : T3) (i : Fin 3) :
    (fullFourierField id (velocity epsilon) x i).im = 0 := by
  rw [fullFourierField_eq_sum modes _ (velocity_eq_zero_of_not_mem epsilon)]
  exact finiteFourierReconstruction_im_eq_zero_of_neg_closed modes (velocity epsilon)
    modes_neg_closed (velocity_conjugate epsilon) x i

theorem fullVelocity_divergence (epsilon : ℝ) (x : T3) :
    spatialDivergence (fullFourierField id (velocity epsilon)) x = 0 :=
  spatialDivergence_fullFourierField (velocity epsilon) (velocity_moments epsilon 2)
    (velocity_transverse epsilon) x

theorem fullVelocity_fourierCoeff (epsilon : ℝ) (q : Wavevector) (i : Fin 3) :
    UnitAddTorus.mFourierCoeff (fun x ↦ fullFourierField id (velocity epsilon) x i) q =
      velocity epsilon q i := by
  apply mFourierCoeff_fullFourierField_component
  apply summable_of_ne_finset_zero (s := modes)
  intro k hk
  rw [velocity_eq_zero_of_not_mem epsilon k hk, norm_zero]

theorem fullVelocity_zero_mean (epsilon : ℝ) (i : Fin 3) :
    UnitAddTorus.mFourierCoeff (fun x ↦ fullFourierField id (velocity epsilon) x i) 0 = 0 := by
  rw [fullVelocity_fourierCoeff, velocity_zero]
  rfl

set_option maxHeartbeats 400000 in
theorem strain_matrix_origin (epsilon : ℝ) :
    matrixReconstruction modes (strainCoeff (velocity epsilon)) 0 =
      (2 * (Real.pi : ℂ)) • !![0, 1, 1; 1, 0, 1; 1, 1, 0] := by
  obtain ⟨hX, hNX, hY, hNY, hZ, hNZ, hD, hND⟩ := velocity_values epsilon
  ext i j
  simp only [matrixReconstruction_apply, sum_modes, mFourier_origin, one_mul,
    strainCoeff, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    smul_eq_mul, gradientCoeff, hX, hNX, hY, hNY, hZ, hNZ, hD, hND]
  fin_cases i <;> fin_cases j <;>
    norm_num [axisX, axisY, axisZ, doubleY, unitTorusDerivativePhase,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, mul_assoc] <;>
    ring

set_option maxHeartbeats 400000 in
theorem spatialVorticity_origin (epsilon : ℝ) :
    spatialVorticity modes (velocity epsilon) 0 = (4 * Real.pi) • diagonalDirection := by
  obtain ⟨hX, hNX, hY, hNY, hZ, hNZ, hD, hND⟩ := velocity_values epsilon
  simp only [spatialVorticity, finiteFourierReconstruction, sum_modes, mFourier_origin,
    one_smul, fourierCurl, hX, hNX, hY, hNY, hZ, hNZ, hD, hND]
  ext i
  fin_cases i <;>
    norm_num [complexRealPartEuclidean, coefficientCross, wavevectorCoefficient,
      axisX, axisY, axisZ, doubleY, unitTorusDerivativePhase, diagonalDirection,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, mul_assoc] <;> ring

theorem fullVorticity_origin (epsilon : ℝ) :
    fullVorticity (velocity epsilon) 0 = (4 * Real.pi) • diagonalDirection := by
  rw [fullVorticity_eq_spatialVorticity modes (velocity epsilon)
    (velocity_eq_zero_of_not_mem epsilon)]
  exact spatialVorticity_origin epsilon

set_option maxHeartbeats 400000 in
theorem pressureHessian_origin (epsilon : ℝ) :
    spatialHessian (spatialPressure (velocity epsilon)) 0 =
      (48 * (Real.pi : ℂ) ^ 2 * (epsilon : ℂ) / 5) • !![1, 0, 0; 0, -1, 0; 0, 0, 0] := by
  have hm := summable_fourierMoment modes (velocity epsilon)
    (velocity_eq_zero_of_not_mem epsilon) 2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := pressureFormula_values epsilon
  ext i j
  rw [spatialHessian, scalarCoordinateDerivative2_spatialPressure _ hm]
  rw [fullFourierField_eq_sum pressureModes _ (fun q hq ↦ by
    simp [indexedDerivativeCoeff, infinitePressureCoeff_eq,
      pressureFormula_eq_zero epsilon q hq])]
  simp only [sum_pressureModes, mFourier_origin, one_smul, indexedDerivativeCoeff,
    infinitePressureCoeff_eq, h1, h2, h3, h4, h5, h6, h7, h8]
  fin_cases i <;> fin_cases j <;>
    norm_num [unitTorusDerivativePhase, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, mul_assoc] <;> ring_nf <;> norm_num [Complex.I_sq]

end Mettapedia.FluidDynamics.NavierStokes.PressureTiltOrigin
