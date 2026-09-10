import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltTangent
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMatrixCurlAlgebra

/-!
# Spectral-residual response to the full Navier–Stokes tangent

Strain and vorticity rates are ordinary derivatives of the actual
Navier–Stokes Fourier right-hand side. The simple leading eigenvalue
uses its Rayleigh derivative. No material source or viscous channel is
set to zero by assumption.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTiltResidualRate

open scoped BigOperators RealInnerProductSpace Matrix.Norms.Elementwise
open PressureTiltDatum PressureTiltOrigin PressureTiltAlignment PressureTiltTangent
open PancakeFourierMaterialPaths PancakeCoefficientLimitEquation PancakeInfiniteFourierDerivative
open PancakeFilteredStrainDynamics PancakeMatrixCurlAlgebra PancakeDyadicDirectionEvolution
open PancakeTransverseEnergyFreezing PancakeSpectralFiniteDifference
open PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralProjectorRegularity PancakeTopEigenvalueDerivative PancakeSpectralDefectEvolution
open LocalLowDiffusionBudget LocalAlignmentForcing

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def strainRate (epsilon nu : ℝ) : R3 →L[ℝ] R3 :=
  fullStrainOperator (infiniteVelocityRHS nu (velocity epsilon)) 0

def vorticityRate (epsilon nu : ℝ) : R3 :=
  fullVorticity (infiniteVelocityRHS nu (velocity epsilon)) 0

def eigenvalueRate (epsilon nu : ℝ) : ℝ :=
  ⟪topVector (originStrain epsilon), strainRate epsilon nu (topVector (originStrain epsilon))⟫

def residualRate (epsilon nu : ℝ) : R3 :=
  eigenvalueRate epsilon nu • fullVorticity (velocity epsilon) 0 -
    strainRate epsilon nu (fullVorticity (velocity epsilon) 0) +
    topEigenvalue (originStrain epsilon) • vorticityRate epsilon nu -
    (originStrain epsilon).1 (vorticityRate epsilon nu)

theorem strainRate_diagonalDirection (epsilon nu : ℝ) :
    strainRate epsilon nu diagonalDirection = WithLp.toLp 2
      ![-16 * Real.pi^2 - 16 * Real.pi^3 * nu - 24 * Real.pi^3 * epsilon * nu -
          48 * Real.pi^2 * epsilon / 5,
        -16 * Real.pi^2 - 16 * Real.pi^3 * nu - 24 * Real.pi^3 * epsilon * nu +
          48 * Real.pi^2 * epsilon / 5,
        -16 * Real.pi^2 - 16 * Real.pi^3 * nu] := by
  change realMatrixOperator (symmetrize (gradientRate epsilon nu)) diagonalDirection = _
  rw [gradientRate_eq]
  ext i
  fin_cases i <;>
    norm_num [realMatrixOperator_apply, symmetrize, diagonalDirection,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      pow_succ, Complex.mul_re] <;> ring

theorem vorticityRate_eq (epsilon nu : ℝ) :
    vorticityRate epsilon nu = WithLp.toLp 2
      ![16 * Real.pi^2 - 16 * Real.pi^3 * nu,
        16 * Real.pi^2 - 16 * Real.pi^3 * nu,
        16 * Real.pi^2 - 16 * Real.pi^3 * nu + 48 * Real.pi^3 * epsilon * nu] := by
  change complexRealPartEuclideanCLM
    (PancakeInfiniteSpatialCurl.spatialCurl
      (fullFourierField id (infiniteVelocityRHS nu (velocity epsilon))) 0) = _
  rw [← matrixCurl_velocityGradient]
  change complexRealPartEuclideanCLM (matrixCurl (gradientRate epsilon nu)) = _
  rw [gradientRate_eq]
  ext i
  fin_cases i <;>
    norm_num [complexRealPartEuclideanCLM_apply, complexRealPartEuclidean, matrixCurl,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, pow_succ, Complex.mul_re] <;> ring

theorem eigenvalueRate_eq (epsilon nu : ℝ) :
    eigenvalueRate epsilon nu = -16 * Real.pi^2 - 16 * Real.pi^3 * nu * (1 + epsilon) := by
  calc
    _ = (⟪diagonalDirection, topVector (originStrain epsilon)⟫^2 / 9) *
        ⟪diagonalDirection, strainRate epsilon nu diagonalDirection⟫ := by
      unfold eigenvalueRate
      conv_lhs => rw [topVector_eq_smul_diagonalDirection epsilon]
      simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    _ = (1 / 3 : ℝ) * ⟪diagonalDirection, strainRate epsilon nu diagonalDirection⟫ := by
      rw [inner_diagonalDirection_topVector_sq]
      ring
    _ = _ := by
      rw [strainRate_diagonalDirection]
      norm_num [diagonalDirection, PiLp.inner_apply, Fin.sum_univ_three,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
      ring

theorem residualRate_eq (epsilon nu : ℝ) :
    residualRate epsilon nu = (64 * Real.pi^3 * epsilon / 5) •
      (WithLp.toLp 2 ![-5 * Real.pi * nu + 3, -5 * Real.pi * nu - 3, 10 * Real.pi * nu] : R3) := by
  rw [residualRate, fullVorticity_origin, map_smul, strainRate_diagonalDirection,
    eigenvalueRate_eq, topEigenvalue_origin, vorticityRate_eq, strain_apply]
  ext i
  fin_cases i <;>
    norm_num [diagonalDirection, PiLp.inner_apply, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk] <;> ring!

theorem residualRate_coordinate_difference (epsilon nu : ℝ) :
    residualRate epsilon nu 0 - residualRate epsilon nu 1 = 384 * Real.pi^3 * epsilon / 5 := by
  rw [residualRate_eq]
  simp only [PiLp.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem residualRate_ne_zero (epsilon nu : ℝ) (he : epsilon ≠ 0) : residualRate epsilon nu ≠ 0 := by
  intro h
  have hc := residualRate_coordinate_difference epsilon nu
  rw [h] at hc
  norm_num at hc
  exact (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero 3 Real.pi_ne_zero)) he) (by norm_num)) hc.symm

theorem norm_residualRate_sq (epsilon nu : ℝ) :
    ‖residualRate epsilon nu‖ ^ 2 =
      (24576 / 25 : ℝ) * Real.pi^6 * epsilon^2 * (25 * Real.pi^2 * nu^2 + 3) := by
  rw [residualRate_eq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

/-- The computed response is forced for every curve with the physical first-order rates. -/
theorem hasDerivAt_residual_of_rates (epsilon nu t : ℝ)
    (S : ℝ → SymmetricStrain) (w : ℝ → R3)
    (hS : HasDerivAt (fun tau ↦ (S tau).1) (strainRate epsilon nu) t)
    (hw : HasDerivAt w (vorticityRate epsilon nu) t)
    (hS0 : S t = originStrain epsilon) (hw0 : w t = fullVorticity (velocity epsilon) 0) :
    HasDerivAt (fun tau ↦ spectralResidual (S tau).1 (topEigenvalue (S tau)) (w tau))
      (residualRate epsilon nu) t := by
  have hg : 0 < topGap (S t) := by rw [hS0, topGap_origin]; positivity
  have hl := hasDerivAt_topEigenvalue S (strainRate epsilon nu) t hS hg
  change HasDerivAt (fun tau ↦ topEigenvalue (S tau))
    ⟪topVector (S t), strainRate epsilon nu (topVector (S t))⟫ t at hl
  rw [hS0] at hl
  change HasDerivAt (fun tau ↦ topEigenvalue (S tau)) (eigenvalueRate epsilon nu) t at hl
  have hz := (hl.smul hw).sub (hS.clm_apply hw)
  apply hz.congr_deriv
  simp only [hS0, hw0, residualRate]
  module

end Mettapedia.FluidDynamics.NavierStokes.PressureTiltResidualRate
