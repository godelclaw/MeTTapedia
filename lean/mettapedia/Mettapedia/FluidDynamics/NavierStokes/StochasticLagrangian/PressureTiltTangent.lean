import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltAlignment
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierFiniteJets
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpatialNavierStokesTangent

/-!
# The actual Navier–Stokes tangent at the pressure-tilt datum

The gradient rate is formed by taking ordinary spatial derivatives of
the full infinite Fourier Navier–Stokes right-hand side. It retains
viscosity and pressure. The origin is a stagnation point, so no transport
term is omitted there. This module computes the vector-field tangent;
it does not assert that an affine tangent path is a solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTiltTangent

open scoped BigOperators Matrix.Norms.Elementwise RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeInfiniteFourierDerivative
open PancakeLocalGradientEquation PancakeCoefficientLimitEquation PancakeInfiniteSpatialCurl
open PressureTiltDatum PressureTiltOrigin PressureTiltAlignment FourierFiniteSupport FourierFiniteJets
open SpatialNavierStokesTangent

local notation "M3" => Matrix (Fin 3) (Fin 3) ℂ

theorem velocity_origin (epsilon : ℝ) : fullFourierField id (velocity epsilon) 0 = 0 := by
  obtain ⟨hX, hNX, hY, hNY, hZ, hNZ, hD, hND⟩ := velocity_values epsilon
  rw [fullFourierField_eq_sum modes _ (velocity_eq_zero_of_not_mem epsilon)]
  simp only [sum_modes, mFourier_origin, one_smul, hX, hNX, hY, hNY, hZ, hNZ, hD, hND]
  ext i
  fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

theorem gradient_origin (epsilon : ℝ) :
    spatialVelocityGradient (fullFourierField id (velocity epsilon)) 0 =
      (4 * (Real.pi : ℂ)) • !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
  obtain ⟨hX, hNX, hY, hNY, hZ, hNZ, hD, hND⟩ := velocity_values epsilon
  rw [spatialVelocityGradient_eq_matrixReconstruction modes _ (velocity_eq_zero_of_not_mem epsilon)]
  ext i j
  simp only [matrixReconstruction_apply, sum_modes, mFourier_origin, one_mul,
    gradientCoeff, hX, hNX, hY, hNY, hZ, hNZ, hD, hND]
  fin_cases i <;> fin_cases j <;>
    norm_num [axisX, axisY, axisZ, doubleY, unitTorusDerivativePhase,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, mul_assoc] <;> ring

set_option maxHeartbeats 400000 in
theorem laplacian_gradient_origin (epsilon : ℝ) :
    matrixLaplacian (spatialVelocityGradient (fullFourierField id (velocity epsilon))) 0 =
      (-16 * (Real.pi : ℂ) ^ 3) • !![0, 3 * (epsilon : ℂ), 1; 1, 0, 0; 0, 1, 0] := by
  obtain ⟨hX, hNX, hY, hNY, hZ, hNZ, hD, hND⟩ := velocity_values epsilon
  rw [laplacian_gradient_eq_matrixReconstruction modes _ (velocity_eq_zero_of_not_mem epsilon)]
  ext i j
  simp only [matrixReconstruction_apply, sum_modes, mFourier_origin, one_mul,
    Matrix.smul_apply, smul_eq_mul, gradientCoeff, hX, hNX, hY, hNY, hZ, hNZ, hD, hND]
  fin_cases i <;> fin_cases j <;>
    norm_num [axisX, axisY, axisZ, doubleY, unitTorusDerivativePhase, modeSquare,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, mul_assoc] <;>
    ring_nf <;> norm_num [Complex.I_sq]

/-- Ordinary gradient of the complete Navier–Stokes Fourier vector field. -/
def gradientRate (epsilon nu : ℝ) : M3 :=
  spatialVelocityGradient (fullFourierField id (infiniteVelocityRHS nu (velocity epsilon))) 0

theorem gradientRate_eq (epsilon nu : ℝ) :
    gradientRate epsilon nu =
      !![-48 * (Real.pi : ℂ)^2 * (epsilon : ℂ) / 5,
          -16 * (Real.pi : ℂ)^2 - 48 * (Real.pi : ℂ)^3 * (epsilon : ℂ) * (nu : ℂ),
          -16 * (Real.pi : ℂ)^3 * (nu : ℂ);
        -16 * (Real.pi : ℂ)^3 * (nu : ℂ),
          48 * (Real.pi : ℂ)^2 * (epsilon : ℂ) / 5, -16 * (Real.pi : ℂ)^2;
        -16 * (Real.pi : ℂ)^2, -16 * (Real.pi : ℂ)^3 * (nu : ℂ), 0] := by
  rw [gradientRate, gradient_infiniteVelocityRHS_of_stagnation nu _
    (velocity_moments epsilon 3) (velocity_transverse epsilon) 0 (velocity_origin epsilon),
    gradient_origin, pressureHessian_origin, laplacian_gradient_origin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring

end Mettapedia.FluidDynamics.NavierStokes.PressureTiltTangent
