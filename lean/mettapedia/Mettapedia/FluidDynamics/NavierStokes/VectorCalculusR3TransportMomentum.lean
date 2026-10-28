import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportLaplacian

/-!
# Vector Calculus R3: Transport Momentum

This module contains convection, momentum-equation, and pressure-residual
identities for transported heat-shear fields.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped Gradient
open scoped Laplacian
open scoped BigOperators
open scoped ContDiff

section VectorCalculusR3

/-- The transported heat-shear field has the exact convection term generated
by the constant transport speed `b` along `x₁`. -/
theorem spatialConvection_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearTransportVelocityField ν a k b) t x =
      coord0Embedding
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  rw [spatialConvection, spatialFDeriv_heatShearTransportVelocityField,
    heatShearTransportVelocityField_apply]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- Transported arbitrary-amplitude shear has the same transport convection
term as the transported heat-shear slice with sampled amplitude `A t`. -/
theorem spatialConvection_amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (amplitudeShearTransportVelocityField A k b) t x =
      coord0Embedding
        (A t * (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearTransportVelocityField A k b t y =
          heatShearTransportVelocityField 0 (A t) k b t y := by
    intro y
    simp [amplitudeShearTransportVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField]
  rw [spatialConvection_congr_at hslice]
  simpa [heatShearTransportScalar, mul_assoc, mul_left_comm, mul_comm]
    using spatialConvection_heatShearTransportVelocityField 0 (A t) k b t x

/-- The transported full-drift heat-shear family has the same convection term
as the transported branch without the additional constant drifts, because the
added constant field has zero `x₁` component. -/
theorem spatialConvection_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearTransportFullDriftVelocityField ν a k b d c) t x =
      coord0Embedding
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  rw [heatShearTransportFullDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)) t x)]
  rw [spatialConvection_heatShearTransportVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_heatShearTransportVelocityField,
    spatialFDeriv_constantVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, constantVelocityField, nsCoord0, nsCoord1, nsCoord2,
      mul_assoc, mul_left_comm, mul_comm]

/-- The transported heat-shear field satisfies the exact zero-pressure momentum
identity. -/
theorem momentumEquation_heatShearTransportVelocityField_zeroPressure
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportVelocityField ν a k b) t x +
        spatialConvection (heatShearTransportVelocityField ν a k b) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearTransportVelocityField ν a k b) t x := by
  rw [timeVelocityDerivative_heatShearTransportVelocityField,
    spatialConvection_heatShearTransportVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearTransportVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- On a fixed time slice, the pressure residual of transported
arbitrary-amplitude shear is the transported sine profile with amplitude equal
to the scalar heat-ODE defect; the constant transport drift itself cancels out.
-/
theorem momentumPressureResidual_amplitudeShearTransportVelocityField_slice
    {A : NSTime → ℝ} {A' μ k b : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) :
    ∀ y : NSSpace,
      momentumPressureResidual μ (amplitudeShearTransportVelocityField A k b) t y =
        heatShearTransportVelocityField 0 (-(A' + μ * k ^ (2 : ℕ) * A t)) k b t y -
          constantVelocityField (EuclideanSpace.single nsCoord1 b) t y := by
  intro y
  ext i
  fin_cases i <;>
    simp [momentumPressureResidual,
      timeVelocityDerivative_amplitudeShearTransportVelocityField hA,
      spatialConvection_amplitudeShearTransportVelocityField,
      spatialLaplacian_amplitudeShearTransportVelocityField,
      heatShearTransportVelocityField_apply, constantVelocityField,
      coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]
  ring

/-- The transported full-drift heat-shear family satisfies the same exact
zero-pressure momentum identity. -/
theorem momentumEquation_heatShearTransportFullDriftVelocityField_zeroPressure
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportFullDriftVelocityField ν a k b d c) t x +
        spatialConvection (heatShearTransportFullDriftVelocityField ν a k b d c) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearTransportFullDriftVelocityField ν a k b d c) t x := by
  rw [timeVelocityDerivative_heatShearTransportFullDriftVelocityField,
    spatialConvection_heatShearTransportFullDriftVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearTransportFullDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
