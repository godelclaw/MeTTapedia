import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeReconstructionRegressionPolynomial
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeShearPressureMomentumObstruction

/-!
# Obstruction Regression Tests for Finite-Mode Reconstruction

This module checks the shear-acceleration and projected-ODE obstruction
examples showing that projected finite modes do not force pressure closure.
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

/-- The abstract projected finite-mode RHS can produce a polynomial residual
that is not curl-free. -/
theorem finiteModeShearAcceleration_nonPressureDefect_eq_polynomial_regression
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
        finiteModeUnitForcingCoefficients finiteModeZeroCoefficientCurve t x =
      finiteModePolynomialVectorFieldEval
        finiteModeShearAccelerationPolynomialVectorField x :=
  finiteModeShearAcceleration_nonPressureDefect_eq_polynomial t x

/-- The identity coefficient curve is checked as a real solution of the
one-mode unit-forcing projected ODE. -/
theorem finiteModeIdentityCoefficientCurve_hasDerivAt_regression
    (t : NSTime) :
    HasDerivAt finiteModeIdentityCoefficientCurve
      (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
        (finiteModeIdentityCoefficientCurve t)) t :=
  finiteModeIdentityCoefficientCurve_hasDerivAt t

/-- The same shear obstruction persists for the actual identity coefficient
solution. -/
theorem finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial_regression
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x =
      finiteModePolynomialVectorFieldEval
        finiteModeShearAccelerationPolynomialVectorField x :=
  finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial t x

/-- The shear residual polynomial vector field is not a polynomial pressure
gradient. -/
theorem finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive_regression :
    ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
      MvPolynomial.pderiv j p =
        finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive

/-- The sign required to close momentum also has no polynomial pressure
primitive. -/
theorem finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive_regression :
    ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
      MvPolynomial.pderiv j p =
        -finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive

/-- No time-dependent scalar polynomial can primitive the sign-correct closing
gradient for the identity-coefficient shear residual. -/
theorem finiteModeShearAcceleration_solution_no_timeDependentPolynomialPressurePrimitive_regression :
    ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ, ∀ t j,
      MvPolynomial.pderiv j (P t) =
        -finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeShearAcceleration_solution_no_timeDependentPolynomialPressurePrimitive

/-- No time-dependent scalar polynomial pressure can close the identity-curve
shear residual through the pointwise pressure-gradient API. -/
theorem finiteModeShearAcceleration_solution_no_pointwisePolynomialPressureGradient_regression :
    ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
      ∀ t x,
        spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            -finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x :=
  finiteModeShearAcceleration_solution_no_pointwisePolynomialPressureGradient

/-- No time-dependent polynomial pressure can make the shear coefficient
solution satisfy pointwise momentum on any time set containing `0`. -/
theorem finiteModeShearAcceleration_solution_no_polynomialPressureMomentumOn_regression
    (I : Set NSTime) (h0 : (0 : NSTime) ∈ I) :
    ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
      ∀ t ∈ I, ∀ x : NSSpace,
        timeVelocityDerivative
              (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                finiteModeIdentityCoefficientCurve)
              t x +
            spatialConvection
              (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                finiteModeIdentityCoefficientCurve)
              t x +
              spatialPressureGradient
                (fun s y => MvPolynomial.eval y (P s)) t x =
          (0 : ℝ) • spatialLaplacian
            (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
              finiteModeIdentityCoefficientCurve)
            t x :=
  finiteModeShearAcceleration_solution_no_polynomialPressureMomentumOn I h0

/-- The finite-mode projection interface alone does not force residual
curl-freeness. -/
theorem finiteModeProjectedNS_nonPressureDefect_curlFree_not_forced_obstruction_regression :
    (∀ t : NSTime,
      finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
          finiteModeUnitForcingCoefficients finiteModeZeroCoefficientCurve t =
        finiteModePolynomialVectorFieldEval
          finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
        MvPolynomial.pderiv j p =
          finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeProjectedNS_nonPressureDefect_curlFree_not_forced_obstruction

/-- The sharpened obstruction uses an actual solution of the abstract
coefficient ODE. -/
theorem finiteModeProjectedNS_coefficientSolution_nonPressureDefect_curlFree_not_forced_obstruction_regression :
    (∀ t : NSTime,
      HasDerivAt finiteModeIdentityCoefficientCurve
        (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
          (finiteModeIdentityCoefficientCurve t)) t) ∧
      (∀ t : NSTime,
        finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t =
          finiteModePolynomialVectorFieldEval
            finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
        MvPolynomial.pderiv j p =
          finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeProjectedNS_coefficientSolution_nonPressureDefect_curlFree_not_forced_obstruction

/-- The coefficient-solution obstruction rules out the sign-correct
time-dependent polynomial pressure primitive needed for momentum closure. -/
theorem finiteModeProjectedNS_coefficientSolution_no_polynomialPressurePrimitive_obstruction_regression :
    (∀ t : NSTime,
      HasDerivAt finiteModeIdentityCoefficientCurve
        (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
          (finiteModeIdentityCoefficientCurve t)) t) ∧
      (∀ t : NSTime,
        finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t =
          finiteModePolynomialVectorFieldEval
            finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ, ∀ t j,
        MvPolynomial.pderiv j (P t) =
          -finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeProjectedNS_coefficientSolution_no_polynomialPressurePrimitive_obstruction

/-- Pointwise pressure-gradient version of the coefficient-solution obstruction. -/
theorem finiteModeProjectedNS_coefficientSolution_no_pointwisePolynomialPressureGradient_obstruction_regression :
    (∀ t : NSTime,
      HasDerivAt finiteModeIdentityCoefficientCurve
        (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
          (finiteModeIdentityCoefficientCurve t)) t) ∧
      (∀ t : NSTime,
        finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t =
          finiteModePolynomialVectorFieldEval
            finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t x,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            -finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x :=
  finiteModeProjectedNS_coefficientSolution_no_pointwisePolynomialPressureGradient_obstruction

/-- The coefficient-solution obstruction reaches the actual pointwise momentum
equation on a concrete interval. -/
theorem finiteModeProjectedNS_coefficientSolution_no_polynomialPressureMomentum_obstruction_regression :
    (∀ t : NSTime,
      HasDerivAt finiteModeIdentityCoefficientCurve
        (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
          (finiteModeIdentityCoefficientCurve t)) t) ∧
      (∀ t : NSTime,
        finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t =
          finiteModePolynomialVectorFieldEval
            finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ Ioo (-(1 : ℝ)) (1 : ℝ), ∀ x : NSSpace,
          timeVelocityDerivative
                (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                  finiteModeIdentityCoefficientCurve)
                t x +
              spatialConvection
                (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                  finiteModeIdentityCoefficientCurve)
                t x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) t x =
            (0 : ℝ) • spatialLaplacian
              (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                finiteModeIdentityCoefficientCurve)
              t x :=
  finiteModeProjectedNS_coefficientSolution_no_polynomialPressureMomentum_obstruction

/-- The projected ODE condition alone cannot universally force polynomial
pressure closure of the reconstructed pointwise momentum equation. -/
theorem finiteModeProjectedNS_polynomialPressureMomentum_not_forced_regression :
    ¬ ∀ (mode : PUnit → NSSpace → NSSpace)
        (C : FiniteModeProjectedNSCoefficients PUnit)
        (a : ℝ → FiniteModeState PUnit),
      (∀ t : NSTime, HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t) →
        ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
          ∀ t ∈ Ioo (-(1 : ℝ)) (1 : ℝ), ∀ x : NSSpace,
            timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
                spatialConvection (finiteModeReconstructedVelocity mode a) t x +
                  spatialPressureGradient
                    (fun s y => MvPolynomial.eval y (P s)) t x =
              (0 : ℝ) • spatialLaplacian
                (finiteModeReconstructedVelocity mode a) t x :=
  finiteModeProjectedNS_polynomialPressureMomentum_not_forced

end FiniteModeReconstructionRegression

end NavierStokes
end FluidDynamics
end Mettapedia
