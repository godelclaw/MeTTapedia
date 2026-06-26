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

end FiniteModeReconstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
