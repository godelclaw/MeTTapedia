import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeReconstructionRegressionLinearExamplesPart1

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
