import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePressureClosureBridge

/-!
# Shear finite-mode pressure-momentum obstruction.

This module records the negative result that a projected one-mode shear
coefficient solution does not force a closing polynomial pressure for the
reconstructed pointwise Navier-Stokes momentum equation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped BigOperators
open scoped ContDiff
open scoped Laplacian

/-- The shear coefficient solution cannot be repaired by any time-dependent
polynomial pressure on a time set containing `0`: the actual pointwise momentum
equation would force the forbidden closing gradient `∇p(0) = -(X₁ e₀)`. -/
theorem finiteModeShearAcceleration_solution_no_polynomialPressureMomentumOn
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
            t x := by
  intro hP
  rcases hP with ⟨P, hmom⟩
  exact finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive
    ⟨P 0, by
      refine
        (finiteModePolynomialPressureGradient_eq_eval_iff_pderiv
          (P 0) (fun j => -finiteModeShearAccelerationPolynomialVectorField j) 0).mp ?_
      intro x
      have hmom0 := hmom 0 h0 x
      rw [finiteModeReconstructedVelocity_timeDerivative_at
        finiteModeShearAccelerationMode finiteModeUnitForcingCoefficients
        finiteModeIdentityCoefficientCurve 0
        (finiteModeIdentityCoefficientCurve_hasDerivAt 0) x] at hmom0
      have hres :
          finiteModeReconstructedAcceleration finiteModeShearAccelerationMode
                finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve 0 x +
              spatialConvection
                (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                  finiteModeIdentityCoefficientCurve) 0 x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) 0 x -
            (0 : ℝ) • spatialLaplacian
              (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                finiteModeIdentityCoefficientCurve) 0 x =
            0 :=
        sub_eq_zero.mpr hmom0
      have hsum :
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) 0 x +
              finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
                finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve 0 x =
            0 := by
        simpa [finiteModeNonPressureMomentumDefect, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm] using hres
      have hgrad :
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) 0 x =
            -finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve 0 x :=
        add_eq_zero_iff_eq_neg.mp hsum
      rw [finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial] at hgrad
      calc
        spatialPressureGradient (fun x y => MvPolynomial.eval y (P 0)) 0 x =
            -finiteModePolynomialVectorFieldEval
              finiteModeShearAccelerationPolynomialVectorField x := by
              simpa [spatialPressureGradient] using hgrad
        _ = finiteModePolynomialVectorFieldEval
              (fun j => -finiteModeShearAccelerationPolynomialVectorField j) x := by
              ext j
              simp [finiteModePolynomialVectorFieldEval_apply]⟩

/-- The abstract projected finite-mode ODE alone does not imply a local
Navier-Stokes momentum solution after reconstruction.  The identity coefficient
curve solves the one-mode projected ODE, but on the concrete interval
`(-1, 1)` no time-dependent polynomial pressure can make its reconstructed
shear field satisfy the pointwise momentum equation. -/
theorem finiteModeProjectedNS_coefficientSolution_no_polynomialPressureMomentum_obstruction :
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
              t x := by
  refine ⟨finiteModeIdentityCoefficientCurve_hasDerivAt, ?_, ?_⟩
  · intro t
    funext x
    exact finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial t x
  · exact
      finiteModeShearAcceleration_solution_no_polynomialPressureMomentumOn
        (Ioo (-(1 : ℝ)) (1 : ℝ)) (by norm_num)

/-- The tempting universal closure theorem is false: solving the abstract
finite-mode coefficient ODE does not, by itself, force existence of a
time-dependent polynomial pressure closing the reconstructed pointwise momentum
equation. -/
theorem finiteModeProjectedNS_polynomialPressureMomentum_not_forced :
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
                (finiteModeReconstructedVelocity mode a) t x := by
  intro h
  exact
    finiteModeShearAcceleration_solution_no_polynomialPressureMomentumOn
      (Ioo (-(1 : ℝ)) (1 : ℝ)) (by norm_num)
      (h finiteModeShearAccelerationMode finiteModeUnitForcingCoefficients
        finiteModeIdentityCoefficientCurve finiteModeIdentityCoefficientCurve_hasDerivAt)

end NavierStokes
end FluidDynamics
end Mettapedia
