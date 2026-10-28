import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeShearPressureMomentumObstruction

/-!
# Positive uniform-acceleration finite-mode reconstruction example.

This module isolates the explicit constant-in-space acceleration mode whose
coordinate pressure closes the reconstructed Navier-Stokes momentum equation.
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

/-- A one-mode spatial direction for the uniform acceleration field `e₀`. -/
def finiteModeUniformAccelerationMode (_ : PUnit) : NSSpace → NSSpace :=
  fun _ => EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- The constant pressure gradient `-e₀` that cancels the uniform acceleration
mode. -/
def finiteModeUniformAccelerationClosingGradient : NSTime → NSSpace :=
  fun _ => -EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- Coordinate pressure coefficients for the pressure `p(t,x) = -x₀`. -/
def finiteModeUniformAccelerationPressureCoefficients :
    NSTime → FiniteModeState (Fin 3) :=
  finiteModeCoordinatePressureCoefficients
    finiteModeUniformAccelerationClosingGradient

/-- The reconstructed coordinate pressure closing the uniform acceleration
field. -/
def finiteModeUniformAccelerationPressure : NSPressureField :=
  finiteModeReconstructedPressure finiteModeCoordinatePressureMode
    finiteModeUniformAccelerationPressureCoefficients

/-- The identity-coefficient reconstruction of the uniform mode is the
time-dependent constant-in-space velocity `u(t,x)=t e₀`. -/
theorem finiteModeUniformAcceleration_velocity_eq_constant
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
        finiteModeIdentityCoefficientCurve t x =
      constantVelocityField (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) t x := by
  simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
    finiteModeIdentityCoefficientCurve, finiteModeUniformAccelerationMode,
    constantVelocityField]

/-- The reconstructed uniform acceleration velocity has zero convection. -/
theorem finiteModeUniformAcceleration_spatialConvection_zero
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  unfold spatialConvection
  have hfderiv :
      spatialFDeriv
          (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
            finiteModeIdentityCoefficientCurve) t x =
        spatialFDeriv
          (constantVelocityField (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) t x := by
    unfold spatialFDeriv
    congr 1
    funext y
    exact finiteModeUniformAcceleration_velocity_eq_constant t y
  rw [hfderiv, finiteModeUniformAcceleration_velocity_eq_constant]
  exact spatialConvection_constantVelocityField
    (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) t x

/-- The reconstructed uniform acceleration velocity has zero spatial
Laplacian. -/
theorem finiteModeUniformAcceleration_spatialLaplacian_zero
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  unfold spatialLaplacian
  have hslice :
      (fun y : NSSpace =>
        finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
          finiteModeIdentityCoefficientCurve t y) =
      fun y : NSSpace =>
        constantVelocityField (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) t y := by
    funext y
    exact finiteModeUniformAcceleration_velocity_eq_constant t y
  rw [hslice]
  exact spatialLaplacian_constantVelocityField
    (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) t x

/-- The projected RHS reconstructs to the constant acceleration `e₀`. -/
theorem finiteModeUniformAcceleration_acceleration_eq
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration finiteModeUniformAccelerationMode
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x =
      EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
  simp [finiteModeReconstructedAcceleration,
    finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
    finiteModeProjectedNSRHS, finiteModeUnitForcingCoefficients,
    finiteModeIdentityCoefficientCurve, finiteModeUniformAccelerationMode]

/-- A positive finite-mode reconstruction: the coefficient solution `a(t)=t`
with uniform mode `e₀` and coordinate pressure `p=-x₀` satisfies the pointwise
Navier-Stokes momentum equation for every viscosity. -/
theorem finiteModeUniformAcceleration_reconstructed_momentum
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
          (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
            finiteModeIdentityCoefficientCurve) t x +
        spatialConvection
          (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
            finiteModeIdentityCoefficientCurve) t x +
          spatialPressureGradient finiteModeUniformAccelerationPressure t x =
      ν • spatialLaplacian
        (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
          finiteModeIdentityCoefficientCurve) t x := by
  rw [finiteModeReconstructedVelocity_timeDerivative_at finiteModeUniformAccelerationMode
    finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t
    (finiteModeIdentityCoefficientCurve_hasDerivAt t) x]
  rw [finiteModeUniformAcceleration_spatialConvection_zero t x,
    finiteModeUniformAcceleration_spatialLaplacian_zero t x]
  rw [finiteModeUniformAcceleration_acceleration_eq t x]
  rw [show spatialPressureGradient finiteModeUniformAccelerationPressure t x =
      finiteModeUniformAccelerationClosingGradient t from
    finiteModeCoordinatePressure_spatialPressureGradient
      finiteModeUniformAccelerationClosingGradient t x]
  simp [finiteModeUniformAccelerationClosingGradient]

/-- The positive uniform-acceleration reconstruction has zero finite-mode
momentum residual on all time. -/
theorem finiteModeUniformAcceleration_reconstructedResidualZeroOn_univ
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      finiteModeUniformAccelerationMode finiteModeCoordinatePressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeUniformAccelerationPressureCoefficients := by
  intro t _ht x
  exact
    (finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
      ν finiteModeUniformAccelerationMode finiteModeCoordinatePressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeUniformAccelerationPressureCoefficients t
      (finiteModeIdentityCoefficientCurve_hasDerivAt t) x).mpr
      (finiteModeUniformAcceleration_reconstructed_momentum ν t x)

/-- Existential packaging of the explicit uniform-acceleration reconstructed
velocity and pressure.  This is a pointwise PDE witness for the finite-mode
reconstruction layer, not a Clay finite-energy witness. -/
theorem finiteModeUniformAcceleration_reconstructed_velocityPressure_momentum_exists
    (ν : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeUniformAccelerationPressure ∧
        ∀ t x,
          timeVelocityDerivative u t x +
              spatialConvection u t x +
                spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  exact
    ⟨finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
        finiteModeIdentityCoefficientCurve,
      finiteModeUniformAccelerationPressure, rfl, rfl,
      finiteModeUniformAcceleration_reconstructed_momentum ν⟩

end NavierStokes
end FluidDynamics
end Mettapedia
