import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportMomentum

/-!
# Vector Calculus R3: Transport Vorticity

This module contains vorticity formulas and pressure-obstruction results for
transported arbitrary-amplitude heat-shear fields.
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

/-- The transported heat-shear field has the same vorticity magnitude as pure
heat shear, but evaluated at the transported phase `x₁ - b * t`. -/
theorem spatialVorticity_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearTransportVelocityField ν a k b) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          Real.cos (k * (x nsCoord1 - b * t)) * k)) := by
  ext i
  fin_cases i <;>
  simp [spatialVorticity, spatialDerivativeComponent,
    spatialFDeriv_heatShearTransportVelocityField, coord0Embedding_apply,
    nsCoord0, nsCoord1, nsCoord2, mul_assoc, mul_left_comm, mul_comm]

/-- Transported arbitrary-amplitude shear has the transported heat-shear
vorticity formula with sampled amplitude `A t`. -/
theorem spatialVorticity_amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (amplitudeShearTransportVelocityField A k b) t x =
      EuclideanSpace.single nsCoord2
        (-(A t * Real.cos (k * (x nsCoord1 - b * t)) * k)) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearTransportVelocityField A k b t y =
          heatShearTransportVelocityField 0 (A t) k b t y := by
    intro y
    simp [amplitudeShearTransportVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField]
  rw [spatialVorticity_congr_at hslice]
  simpa [heatShearTransportScalar]
    using spatialVorticity_heatShearTransportVelocityField 0 (A t) k b t x

/-- At the phase-aligned point `x₁ = b * t`, a transported
arbitrary-amplitude shear residual has curl equal to the sampled scalar heat
ODE defect times `k`. -/
theorem spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint
    {A : NSTime → ℝ} {A' μ k b : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) :
    spatialVorticity
        (momentumPressureResidual μ (amplitudeShearTransportVelocityField A k b))
        t (EuclideanSpace.single nsCoord1 (b * t)) =
      EuclideanSpace.single nsCoord2 ((A' + μ * k ^ (2 : ℕ) * A t) * k) := by
  let B : ℝ := -(A' + μ * k ^ (2 : ℕ) * A t)
  rw [spatialVorticity_congr_at
    (u := momentumPressureResidual μ (amplitudeShearTransportVelocityField A k b))
    (v := heatShearTransportVelocityField 0 B k b -
      constantVelocityField (EuclideanSpace.single nsCoord1 b))
    (t := t) (x := EuclideanSpace.single nsCoord1 (b * t))
    (by
      intro y
      simpa [B] using
        momentumPressureResidual_amplitudeShearTransportVelocityField_slice
          (A := A) (A' := A') (μ := μ) (k := k) (b := b) (t := t) hA y)]
  rw [spatialVorticity_sub
    (u := heatShearTransportVelocityField 0 B k b)
    (v := constantVelocityField (EuclideanSpace.single nsCoord1 b))
    (t := t) (x := EuclideanSpace.single nsCoord1 (b * t))]
  · rw [spatialVorticity_heatShearTransportVelocityField,
      spatialVorticity_constantVelocityField]
    ext i
    fin_cases i <;>
      simp [B, nsCoord1, nsCoord2, mul_left_comm, mul_comm]
    ring
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField 0 B k b)
      t (EuclideanSpace.single nsCoord1 (b * t))
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField (EuclideanSpace.single nsCoord1 b))
      t (EuclideanSpace.single nsCoord1 (b * t))

/-- A nonzero sampled heat-ODE defect and nonzero wave number make the
transported arbitrary-amplitude pressure residual non-gradient by curl. -/
theorem spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint_ne_zero
    {A : NSTime → ℝ} {A' μ k b : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t)
    (hode : A' + μ * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0) :
    spatialVorticity
        (momentumPressureResidual μ (amplitudeShearTransportVelocityField A k b))
        t (EuclideanSpace.single nsCoord1 (b * t)) ≠ 0 := by
  rw [spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint hA]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord2) h
  have hprod : (A' + μ * k ^ (2 : ℕ) * A t) * k = 0 := by
    simpa [nsCoord2] using hcoord
  exact (mul_ne_zero hode hk) hprod

/-- No smooth pressure can repair a transported arbitrary-amplitude shear ansatz
at a time where its scalar amplitude violates the heat ODE.  The constant
transport drift cancels with the phase transport term, leaving the same scalar
ODE burden as for pure shear. -/
theorem not_exists_smoothPressure_momentumEquation_amplitudeShearTransportVelocityField_of_heatODE_mismatch_at
    {A : NSTime → ℝ} {A' μ k b : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t)
    (hode : A' + μ * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ s x,
          timeVelocityDerivative (amplitudeShearTransportVelocityField A k b) s x +
              spatialConvection (amplitudeShearTransportVelocityField A k b) s x +
              spatialPressureGradient p s x =
            μ • spatialLaplacian (amplitudeShearTransportVelocityField A k b) s x := by
  exact
    not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
      (ν := μ) (u := amplitudeShearTransportVelocityField A k b)
      ⟨t, EuclideanSpace.single nsCoord1 (b * t),
        spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint_ne_zero
          hA hode hk⟩

/-- The transported full-drift heat-shear family has the same vorticity as the
transported branch without the additional constant drifts. -/
theorem spatialVorticity_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearTransportFullDriftVelocityField ν a k b d c) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          Real.cos (k * (x nsCoord1 - b * t)) * k)) := by
  rw [heatShearTransportFullDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)) t x)]
  simp [spatialVorticity_heatShearTransportVelocityField,
    spatialVorticity_constantVelocityField]

end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
