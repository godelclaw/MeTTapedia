import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeReconstructionRegressionLocal
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeLinearMatrixExamples

/-!
# Linear Example Regression Tests for Finite-Mode Reconstruction

This module checks radial-linear, diagonal-linear, symmetric-shear, and
matrix-linear finite-mode examples and their affine-quadratic pressure closure.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped ContDiff
open scoped Laplacian

section FiniteModeReconstructionRegression

/-- The radial-linear reconstruction is the concrete field `u(t,x)=t x`. -/
theorem finiteModeRadialLinear_reconstructedVelocity_eq_regression
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve t x =
      t • x :=
  finiteModeRadialLinear_reconstructedVelocity_eq t x

/-- The projected acceleration for the radial-linear identity solution is `x`. -/
theorem finiteModeRadialLinear_reconstructedAcceleration_eq_regression
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x =
      x :=
  finiteModeRadialLinear_reconstructedAcceleration_eq t x

/-- The time derivative of the radial-linear reconstruction is `x`. -/
theorem finiteModeRadialLinear_timeVelocityDerivative_eq_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      x :=
  finiteModeRadialLinear_timeVelocityDerivative_eq t x

/-- The convection term for the radial-linear reconstruction is `t^2 x`. -/
theorem finiteModeRadialLinear_spatialConvection_eq_regression
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      (t * t) • x :=
  finiteModeRadialLinear_spatialConvection_eq t x

/-- The radial-linear reconstruction has zero spatial Laplacian. -/
theorem finiteModeRadialLinear_spatialLaplacian_zero_regression
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      0 :=
  finiteModeRadialLinear_spatialLaplacian_zero t x

/-- The radial-linear example has closing pressure gradient `-(1+t^2)x`. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_eq_regression
    (ν t : ℝ) (j : Fin 3) :
    finiteModePolynomialClosingPressureGradientComponents
        ν finiteModeRadialLinearPolynomialMode
          finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
          (fun s => finiteModePolynomialLaplacianComponents
            (finiteModePolynomialReconstructedVelocityComponents
              finiteModeRadialLinearPolynomialMode
              finiteModeIdentityCoefficientCurve s))
        t j =
      -(MvPolynomial.C (1 + t * t) * MvPolynomial.X j) :=
  finiteModeRadialLinearPolynomialClosingPressureGradient_eq ν t j

/-- The polynomial pressure primitive constructed for the radial-linear example
has the expected explicit pressure gradient. -/
theorem finiteModeRadialLinearPolynomialPressureGradient_eq_regression
    (ν ε : ℝ) {t : NSTime} (ht : t ∈ Ioo (-ε) ε) (x : NSSpace) :
    spatialPressureGradient
        (fun s y =>
          finiteModePolynomialPressureMode
            (finiteModePolynomialClosingPressureGradientComponents
              ν finiteModeRadialLinearPolynomialMode
                finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
                (fun r => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents
                    finiteModeRadialLinearPolynomialMode
                    finiteModeIdentityCoefficientCurve r))
              s) y)
        t x =
      -(1 + t * t) • x :=
  finiteModeRadialLinearPolynomialPressureGradient_eq ν ε ht x

/-- Direct pointwise momentum identity for the radial-linear reconstruction. -/
theorem finiteModeRadialLinear_reconstructed_momentum_explicit_regression
    (ν ε : ℝ) {t : NSTime} (ht : t ∈ Ioo (-ε) ε) (x : NSSpace) :
    timeVelocityDerivative
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
        spatialConvection
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
          spatialPressureGradient
            (fun s y =>
              finiteModePolynomialPressureMode
                (finiteModePolynomialClosingPressureGradientComponents
                  ν finiteModeRadialLinearPolynomialMode
                    finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
                    (fun r => finiteModePolynomialLaplacianComponents
                      (finiteModePolynomialReconstructedVelocityComponents
                        finiteModeRadialLinearPolynomialMode
                        finiteModeIdentityCoefficientCurve r))
                  s) y)
            t x =
      ν • spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x :=
  finiteModeRadialLinear_reconstructed_momentum_explicit ν ε ht x

/-- The finite diagonal-quadratic pressure ansatz realizes the explicit
radial-linear pressure gradient. -/
theorem finiteModeRadialLinearDiagonalPressureGradient_eq_regression
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient finiteModeRadialLinearDiagonalPressure t x =
      -(1 + t * t) • x :=
  finiteModeRadialLinearDiagonalPressureGradient_eq t x

/-- The radial-linear reconstruction closes pointwise momentum with the finite
diagonal-quadratic pressure ansatz. -/
theorem finiteModeRadialLinear_diagonalPressure_reconstructed_momentum_regression
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
        spatialConvection
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
          spatialPressureGradient finiteModeRadialLinearDiagonalPressure t x =
      ν • spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x :=
  finiteModeRadialLinear_diagonalPressure_reconstructed_momentum ν t x

/-- The finite diagonal-quadratic pressure ansatz gives zero reconstructed
finite-mode momentum residual for the radial-linear example. -/
theorem finiteModeRadialLinear_diagonalPressure_reconstructedResidualZeroOn_univ_regression
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeDiagonalQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearDiagonalPressureCoefficients :=
  finiteModeRadialLinear_diagonalPressure_reconstructedResidualZeroOn_univ ν

/-- Concrete nonconstant radial-linear reconstruction closed by the finite
diagonal-quadratic pressure basis. -/
theorem finiteModeRadialLinear_reconstructed_velocityDiagonalPressure_momentum_exists_regression
    (ν : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeRadialLinearDiagonalPressure ∧
        ∀ t x,
          timeVelocityDerivative u t x +
              spatialConvection u t x +
                spatialPressureGradient p t x =
            ν • spatialLaplacian u t x :=
  finiteModeRadialLinear_reconstructed_velocityDiagonalPressure_momentum_exists ν

/-- The computed radial-linear polynomial closing gradient is represented by
the finite affine-quadratic pressure-gradient space. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_affine_eq_regression
    (ν t : ℝ) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν finiteModeRadialLinearPolynomialMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                finiteModeRadialLinearPolynomialMode
                finiteModeIdentityCoefficientCurve s))
          t) =
      finiteModeAffineGradientField
        (finiteModeRadialLinearAffinePressureConstant t)
        (finiteModeRadialLinearAffinePressureMatrix t) :=
  finiteModeRadialLinearPolynomialClosingPressureGradient_affine_eq ν t

/-- The explicit affine-quadratic pressure has the radial-linear closing
gradient. -/
theorem finiteModeRadialLinearAffineQuadraticPressureGradient_eq_regression
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient finiteModeRadialLinearAffineQuadraticPressure t x =
      -(1 + t * t) • x :=
  finiteModeRadialLinearAffineQuadraticPressureGradient_eq t x

/-- The radial-linear reconstruction closes pointwise momentum with the
explicit affine-quadratic pressure field. -/
theorem finiteModeRadialLinear_affineQuadraticPressure_reconstructed_momentum_regression
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
        spatialConvection
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
          spatialPressureGradient finiteModeRadialLinearAffineQuadraticPressure t x =
      ν • spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x :=
  finiteModeRadialLinear_affineQuadraticPressure_reconstructed_momentum ν t x

/-- The explicit affine-quadratic pressure coefficients give zero reconstructed
finite-mode momentum residual for the radial-linear example. -/
theorem finiteModeRadialLinear_affineQuadraticPressure_reconstructedResidualZeroOn_univ_regression
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeAffineQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearAffineQuadraticPressureCoefficients :=
  finiteModeRadialLinear_affineQuadraticPressure_reconstructedResidualZeroOn_univ ν

/-- Concrete radial-linear reconstruction closed by the explicit
affine-quadratic pressure field. -/
theorem finiteModeRadialLinear_reconstructed_velocityExplicitAffineQuadraticPressure_momentum_exists_regression
    (ν : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeRadialLinearAffineQuadraticPressure ∧
        ∀ t x,
          timeVelocityDerivative u t x +
              spatialConvection u t x +
                spatialPressureGradient p t x =
            ν • spatialLaplacian u t x :=
  finiteModeRadialLinear_reconstructed_velocityExplicitAffineQuadraticPressure_momentum_exists ν

/-- Concrete radial-linear reconstruction closed by the finite
affine-quadratic pressure basis through the polynomial-to-affine bridge. -/
theorem finiteModeRadialLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists_regression
    (ν ε : ℝ) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeRadialLinearPolynomialMode i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeRadialLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists ν ε

/-- The diagonal-linear multi-mode coefficient curve solves its forced
projected ODE. -/
theorem finiteModeDiagonalLinearCoefficientCurve_hasDerivAt_regression
    (lam : Fin 3 → ℝ) (t : NSTime) :
    HasDerivAt (finiteModeDiagonalLinearCoefficientCurve lam)
      (finiteModeProjectedNSRHS (finiteModeDiagonalLinearForcingCoefficients lam)
        (finiteModeDiagonalLinearCoefficientCurve lam t)) t :=
  finiteModeDiagonalLinearCoefficientCurve_hasDerivAt lam t

/-- The diagonal-linear multi-mode reconstruction has component formula
`u_j(t,x)=lam_j t x_j`. -/
theorem finiteModeDiagonalLinear_reconstructedVelocity_apply_regression
    (lam : Fin 3 → ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y)
        (finiteModeDiagonalLinearCoefficientCurve lam) t x j =
      lam j * t * x j :=
  finiteModeDiagonalLinear_reconstructedVelocity_apply lam t x j

/-- The computed closing pressure gradient for the diagonal-linear multi-mode
family is affine with symmetric diagonal linear part. -/
theorem finiteModeDiagonalLinearPolynomialClosingPressureGradient_affine_eq_regression
    (ν : ℝ) (lam : Fin 3 → ℝ) (t : NSTime) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν finiteModeDiagonalLinearPolynomialMode
            (finiteModeDiagonalLinearForcingCoefficients lam)
            (finiteModeDiagonalLinearCoefficientCurve lam)
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                finiteModeDiagonalLinearPolynomialMode
                (finiteModeDiagonalLinearCoefficientCurve lam) s))
          t) =
      finiteModeAffineGradientField 0
        (finiteModeDiagonalLinearAffinePressureMatrix lam t) :=
  finiteModeDiagonalLinearPolynomialClosingPressureGradient_affine_eq ν lam t

/-- Multi-mode diagonal-linear velocity families close through the finite
affine-quadratic pressure basis. -/
theorem finiteModeDiagonalLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists_regression
    (ν ε : ℝ) (lam : Fin 3 → ℝ) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y)
        (finiteModeDiagonalLinearCoefficientCurve lam) ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeDiagonalLinearPolynomialMode i) y)
              finiteModeAffineQuadraticPressureMode
              (finiteModeDiagonalLinearForcingCoefficients lam)
              (finiteModeDiagonalLinearCoefficientCurve lam) b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeDiagonalLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists ν ε lam

/-- Regression: each diagonal-linear mode has divergence `1`. -/
theorem finiteModeDiagonalLinearPolynomialMode_spatialDivergence_regression
    (i : Fin 3) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (fun _ : NSTime => fun y : NSSpace =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y) t x = 1 :=
  finiteModeDiagonalLinearPolynomialMode_spatialDivergence i t x

/-- Regression: the diagonal-linear reconstructed divergence is the time-scaled
coefficient trace. -/
theorem finiteModeDiagonalLinear_spatialDivergence_eq_regression
    (lam : Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeDiagonalLinearPolynomialMode i) y)
          (finiteModeDiagonalLinearCoefficientCurve lam)) t x =
      t * ∑ i : Fin 3, lam i :=
  finiteModeDiagonalLinear_spatialDivergence_eq lam t x

/-- Regression: trace-free diagonal-linear coefficients reconstruct a
divergence-free velocity. -/
theorem finiteModeDiagonalLinear_spatialDivergence_zero_of_trace_regression
    (lam : Fin 3 → ℝ) (htrace : ∑ i : Fin 3, lam i = 0) :
    ∀ t x,
      spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeDiagonalLinearPolynomialMode i) y)
          (finiteModeDiagonalLinearCoefficientCurve lam)) t x = 0 :=
  finiteModeDiagonalLinear_spatialDivergence_zero_of_trace lam htrace

/-- Regression: trace-free diagonal-linear velocity families close momentum and
are incompressible. -/
theorem finiteModeDiagonalLinear_traceFree_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists_regression
    (ν ε : ℝ) (lam : Fin 3 → ℝ) (htrace : ∑ i : Fin 3, lam i = 0) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y)
        (finiteModeDiagonalLinearCoefficientCurve lam) ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeDiagonalLinearPolynomialMode i) y)
              finiteModeAffineQuadraticPressureMode
              (finiteModeDiagonalLinearForcingCoefficients lam)
              (finiteModeDiagonalLinearCoefficientCurve lam) b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeDiagonalLinear_traceFree_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    ν ε lam htrace

/-- Regression: the symmetric off-diagonal shear reconstruction has the
expected component formula. -/
theorem finiteModeSymmetricShear_reconstructedVelocity_apply_regression
    (α : ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α i) y)
        finiteModeIdentityCoefficientCurve t x j =
      if j = (0 : Fin 3) then α * t * x (1 : Fin 3)
      else if j = (1 : Fin 3) then α * t * x (0 : Fin 3)
      else 0 :=
  finiteModeSymmetricShear_reconstructedVelocity_apply α t x j

/-- Regression: the symmetric off-diagonal shear closing pressure gradient is
affine-quadratic. -/
theorem finiteModeSymmetricShearPolynomialClosingPressureGradient_affine_eq_regression
    (ν α : ℝ) (t : NSTime) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν (finiteModeSymmetricShearPolynomialMode α)
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                (finiteModeSymmetricShearPolynomialMode α)
                finiteModeIdentityCoefficientCurve s))
          t) =
      finiteModeAffineGradientField 0
        (finiteModeSymmetricShearAffinePressureMatrix α t) :=
  finiteModeSymmetricShearPolynomialClosingPressureGradient_affine_eq ν α t

/-- Regression: the symmetric off-diagonal shear reconstruction is
divergence-free. -/
theorem finiteModeSymmetricShear_reconstructed_spatialDivergence_zero_regression
    (α : ℝ) :
    ∀ t x,
      spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeSymmetricShearPolynomialMode α i) y)
          finiteModeIdentityCoefficientCurve) t x = 0 :=
  finiteModeSymmetricShear_reconstructed_spatialDivergence_zero α

/-- Regression: the symmetric off-diagonal shear mode closes momentum through
finite affine-quadratic pressure and is incompressible. -/
theorem finiteModeSymmetricShear_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists_regression
    (ν ε α : ℝ) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeSymmetricShearPolynomialMode α i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeSymmetricShear_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    ν ε α

/-- Regression: the matrix-linear reconstruction has component formula
`u_j(t,x)=t Σ_k A_{jk}x_k`. -/
theorem finiteModeLinearMatrix_reconstructedVelocity_apply_regression
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A i) y)
        finiteModeIdentityCoefficientCurve t x j =
      t * ∑ k : Fin 3, A j k * x k :=
  finiteModeLinearMatrix_reconstructedVelocity_apply A t x j

/-- Regression: the matrix-linear computed closing gradient is affine with
matrix `-(A+t^2A^2)`. -/
theorem finiteModeLinearMatrixPolynomialClosingPressureGradient_affine_eq_regression
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν (finiteModeLinearMatrixPolynomialMode A)
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                (finiteModeLinearMatrixPolynomialMode A)
                finiteModeIdentityCoefficientCurve s))
          t) =
      finiteModeAffineGradientField 0
        (finiteModeLinearMatrixAffinePressureMatrix A t) :=
  finiteModeLinearMatrixPolynomialClosingPressureGradient_affine_eq ν A t

/-- Regression: matrix-linear reconstructed divergence is `t * trace A`. -/
theorem finiteModeLinearMatrix_spatialDivergence_eq_regression
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeLinearMatrixPolynomialMode A i) y)
          finiteModeIdentityCoefficientCurve) t x =
      t * ∑ i : Fin 3, A i i :=
  finiteModeLinearMatrix_spatialDivergence_eq A t x

/-- Regression: the exact affine-symmetry condition on the computed closing
matrix is sufficient for finite pressure closure and incompressibility. -/
theorem finiteModeLinearMatrix_traceFreeAffineSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists_regression
    (ν ε : ℝ) (A : Fin 3 → Fin 3 → ℝ)
    (hclosure : ∀ t ∈ Ioo (-ε) ε, ∀ i j,
      finiteModeLinearMatrixAffinePressureMatrix A t i j =
        finiteModeLinearMatrixAffinePressureMatrix A t j i)
    (htrace : ∑ i : Fin 3, A i i = 0) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeLinearMatrixPolynomialMode A i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeLinearMatrix_traceFreeAffineSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    ν ε A hclosure htrace

/-- Regression: symmetric trace-free matrix-linear fields close momentum
through finite affine-quadratic pressure and are incompressible. -/
theorem finiteModeLinearMatrix_traceFreeSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists_regression
    (ν ε : ℝ) (A : Fin 3 → Fin 3 → ℝ)
    (hA : ∀ i j, A i j = A j i) (htrace : ∑ i : Fin 3, A i i = 0) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeLinearMatrixPolynomialMode A i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeLinearMatrix_traceFreeSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    ν ε A hA htrace

/-- Concrete nonconstant polynomial-mode reconstruction closed by the explicit
polynomial pressure primitive. -/
theorem finiteModeRadialLinear_reconstructed_velocityPolynomialPressure_momentum_exists_regression
    (ν ε : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = (fun t x =>
          finiteModePolynomialPressureMode
            (finiteModePolynomialClosingPressureGradientComponents
              ν finiteModeRadialLinearPolynomialMode
                finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents
                    finiteModeRadialLinearPolynomialMode
                    finiteModeIdentityCoefficientCurve s))
              t) x) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeRadialLinear_reconstructed_velocityPolynomialPressure_momentum_exists ν ε

/-- A one-mode coefficient solution with an affine curl-free non-pressure defect
constructs affine-quadratic pressure coefficients and reconstructs local
pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_affineHelmholtz_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (c : NSTime → NSSpace)
    (A : NSTime → Fin 3 → Fin 3 → ℝ)
    (hA : ∀ t ∈ Ioo (-ε) ε, ∀ i j, A t i j = A t j i)
    (hdefect : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModeAffineGradientField (c t) (A t)) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν mode finiteModeAffineQuadraticPressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_affineHelmholtz
    ν mode C a ε ha c A hA hdefect

/-- For polynomial one-mode spatial modes, an affine symmetric computed
closing gradient constructs affine-quadratic finite pressure coefficients and
reconstructs local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (c : NSTime → NSSpace)
    (A : NSTime → Fin 3 → Fin 3 → ℝ)
    (hA : ∀ t ∈ Ioo (-ε) ε, ∀ i j, A t i j = A t j i)
    (hclosing : ∀ t ∈ Ioo (-ε) ε,
      finiteModePolynomialVectorFieldEval
          (finiteModePolynomialClosingPressureGradientComponents
            ν modePoly C a
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
            t) =
        finiteModeAffineGradientField (c t) (A t)) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y)
              finiteModeAffineQuadraticPressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
    ν modePoly C a ε ha c A hA hclosing

/-- A one-mode coefficient solution whose non-pressure residual is closed by a
constant-gradient coordinate pressure reconstructs to local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityCoordinatePressure_momentum_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (c : NSTime → NSSpace)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hbalance : ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            c t =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure finiteModeCoordinatePressureMode
          (finiteModeCoordinatePressureCoefficients c) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityCoordinatePressure_momentum_of_constantGradient_balance
    ν mode C a c ε ha hbalance

/-- A one-mode coefficient solution whose non-pressure residual is closed by a
diagonal linear-in-space pressure gradient reconstructs to local pointwise
momentum using the nonconstant quadratic pressure modes. -/
theorem oneModeProjectedNS_local_reconstructed_velocityDiagonalQuadraticPressure_momentum_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (d : NSTime → FiniteModeState (Fin 3))
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hbalance : ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            (∑ j : Fin 3, d t j • (x j • EuclideanSpace.single j (1 : ℝ))) =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
          (finiteModeDiagonalQuadraticPressureCoefficients d) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityDiagonalQuadraticPressure_momentum_of_diagonalLinearGradient_balance
    ν mode C a d ε ha hbalance

/-- Global time-dependent matrix-linear finite-mode velocities retain the
explicit pointwise momentum identity. -/
theorem finiteModeLinearMatrix_timeDependent_pointwise_momentum_regression
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (hg : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∀ t x,
      timeVelocityDerivative (finiteModeLinearMatrixTimeVelocity A g) t x +
          spatialConvection (finiteModeLinearMatrixTimeVelocity A g) t x +
            spatialPressureGradient (finiteModeLinearMatrixTimePressure A g gdot) t x =
        ν • spatialLaplacian (finiteModeLinearMatrixTimeVelocity A g) t x :=
  finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq ν A g gdot hA hg

/-- Global time-dependent matrix-linear finite-mode velocities remain
incompressible when the matrix is trace-free. -/
theorem finiteModeLinearMatrix_timeDependent_global_momentum_incompressible_exists_regression
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hg : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            (∀ t x,
              timeVelocityDerivative u t x +
                  spatialConvection u t x +
                    spatialPressureGradient p t x =
                ν • spatialLaplacian u t x) ∧
            ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeLinearMatrix_timeDependent_global_momentum_incompressible_exists
    ν A g gdot hA htrace hg

end FiniteModeReconstructionRegression

end NavierStokes
end FluidDynamics
end Mettapedia
