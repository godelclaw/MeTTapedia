import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Momentum

/-!
# Vector Calculus R3: Vorticity

Concrete vorticity identities for linear and non-transported heat-shear fields.
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

/-- Vorticity commutes with constant scalar multiplication. -/
theorem spatialVorticity_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialVorticity (a • u) t x = a • spatialVorticity u t x := by
  ext i
  fin_cases i <;>
    simp [spatialVorticity, spatialDerivativeComponent_const_smul, mul_sub]

/-- Vorticity commutes with addition. -/
theorem spatialVorticity_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialVorticity (u + v) t x = spatialVorticity u t x + spatialVorticity v t x := by
  ext i
  fin_cases i
  · simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2, EuclideanSpace.single_apply]
    have h12 :
        spatialDerivativeComponent (u + v) t x 1 2 =
          spatialDerivativeComponent u t x 1 2 + spatialDerivativeComponent v t x 1 2 := by
      simpa [nsCoord1, nsCoord2] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord1) (comp := nsCoord2))
    have h21 :
        spatialDerivativeComponent (u + v) t x 2 1 =
          spatialDerivativeComponent u t x 2 1 + spatialDerivativeComponent v t x 2 1 := by
      simpa [nsCoord1, nsCoord2] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord2) (comp := nsCoord1))
    rw [h12, h21]
    ring
  · simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2, EuclideanSpace.single_apply]
    have h20 :
        spatialDerivativeComponent (u + v) t x 2 0 =
          spatialDerivativeComponent u t x 2 0 + spatialDerivativeComponent v t x 2 0 := by
      simpa [nsCoord0, nsCoord2] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord2) (comp := nsCoord0))
    have h02 :
        spatialDerivativeComponent (u + v) t x 0 2 =
          spatialDerivativeComponent u t x 0 2 + spatialDerivativeComponent v t x 0 2 := by
      simpa [nsCoord0, nsCoord2] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord0) (comp := nsCoord2))
    rw [h20, h02]
    ring
  · simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2, EuclideanSpace.single_apply]
    have h01 :
        spatialDerivativeComponent (u + v) t x 0 1 =
          spatialDerivativeComponent u t x 0 1 + spatialDerivativeComponent v t x 0 1 := by
      simpa [nsCoord0, nsCoord1] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord0) (comp := nsCoord1))
    have h10 :
        spatialDerivativeComponent (u + v) t x 1 0 =
          spatialDerivativeComponent u t x 1 0 + spatialDerivativeComponent v t x 1 0 := by
      simpa [nsCoord0, nsCoord1] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord1) (comp := nsCoord0))
    rw [h01, h10]
    ring

/-- Vorticity is unchanged up to sign under velocity negation. -/
theorem spatialVorticity_neg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialVorticity (-u) t x = -spatialVorticity u t x := by
  simpa using spatialVorticity_const_smul (-1 : ℝ) u t x

/-- Vorticity commutes with subtraction. -/
theorem spatialVorticity_sub
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialVorticity (u - v) t x = spatialVorticity u t x - spatialVorticity v t x := by
  rw [sub_eq_add_neg]
  rw [spatialVorticity_add hu hv.neg]
  rw [spatialVorticity_neg]
  abel

/-- Vorticity commutes with linear combinations. -/
theorem spatialVorticity_linearCombination
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (a b : ℝ)
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialVorticity (a • u + b • v) t x =
      a • spatialVorticity u t x + b • spatialVorticity v t x := by
  rw [spatialVorticity_add (hu.const_smul a) (hv.const_smul b)]
  rw [spatialVorticity_const_smul, spatialVorticity_const_smul]

/-- The vorticity of the zero field is zero. -/
theorem spatialVorticity_zero (t : NSTime) (x : NSSpace) :
    spatialVorticity (0 : NSVelocityField) t x = 0 := by
  ext i
  fin_cases i <;> simp [spatialVorticity, spatialDerivativeComponent_zero]

/-- The vorticity of a constant velocity field is zero. -/
theorem spatialVorticity_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialVorticity (constantVelocityField c) t x = 0 := by
  ext i
  fin_cases i <;>
    simp [spatialVorticity, spatialDerivativeComponent_constantVelocityField]

/-- The steady linear shear field has constant vorticity `(0, 0, -a)`. -/
theorem spatialVorticity_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (linearShearVelocityField a) t x = EuclideanSpace.single nsCoord2 (-a) := by
  ext i
  fin_cases i
  · simp [spatialVorticity, spatialDerivativeComponent, spatialFDeriv_linearShearVelocityField,
      linearShearMap, nsCoord0, nsCoord1, nsCoord2, ContinuousLinearMap.smulRight_apply]
  · simp [spatialVorticity, spatialDerivativeComponent, spatialFDeriv_linearShearVelocityField,
      linearShearMap, nsCoord0, nsCoord1, nsCoord2, ContinuousLinearMap.smulRight_apply]
  · simp [spatialVorticity, spatialDerivativeComponent, spatialFDeriv_linearShearVelocityField,
      linearShearMap, nsCoord0, nsCoord1, nsCoord2, ContinuousLinearMap.smulRight_apply]

/-- The steady field `u(t,x) = (a * x₁, 0, b)` has the same constant vorticity
`(0, 0, -a)` as pure linear shear. -/
theorem spatialVorticity_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (linearShearVerticalDriftVelocityField a b) t x =
      EuclideanSpace.single nsCoord2 (-a) := by
  rw [linearShearVerticalDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 b)) t x)]
  simp [spatialVorticity_linearShearVelocityField,
    spatialVorticity_constantVelocityField]

/-- The steady field `u(t,x) = (a * x₁, b, 0)` has the same constant vorticity
`(0, 0, -a)` as pure linear shear. -/
theorem spatialVorticity_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (linearShearHorizontalDriftVelocityField a b) t x =
      EuclideanSpace.single nsCoord2 (-a) := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
      (EuclideanSpace.single nsCoord1 b)) t x)]
  simp [spatialVorticity_linearShearVelocityField,
    spatialVorticity_constantVelocityField]

/-- The steady field `u(t,x) = (a * x₁, b, c)` has the same constant vorticity
`(0, 0, -a)` as pure linear shear. -/
theorem spatialVorticity_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (linearShearFullDriftVelocityField a b c) t x =
      EuclideanSpace.single nsCoord2 (-a) := by
  rw [linearShearFullDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  simp [spatialVorticity_linearShearHorizontalDriftVelocityField,
    spatialVorticity_constantVelocityField]

/-- The damped sinusoidal heat-shear field has vorticity in the third
component only. -/
theorem spatialVorticity_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearVelocityField ν a k) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k)) := by
  ext i
  fin_cases i <;>
  simp [spatialVorticity, spatialDerivativeComponent, spatialFDeriv_heatShearVelocityField,
      coord0Embedding_apply, nsCoord0, nsCoord1, nsCoord2,
      mul_assoc, mul_left_comm, mul_comm]

/-- The general time-amplitude shear ansatz has the same vorticity formula as
heat shear, with the sampled amplitude `A t`. -/
theorem spatialVorticity_amplitudeShearVelocityField
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (amplitudeShearVelocityField A k) t x =
      EuclideanSpace.single nsCoord2
        (-(A t * Real.cos (k * x nsCoord1) * k)) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearVelocityField A k t y = heatShearVelocityField 0 (A t) k t y := by
    intro y
    simp [amplitudeShearVelocityField, heatShearVelocityField, heatShearScalar]
  rw [spatialVorticity_congr_at hslice]
  simpa [heatShearScalar]
    using spatialVorticity_heatShearVelocityField 0 (A t) k t x

/-- The wrong-viscosity pressure residual for heat shear has curl equal to the
same viscosity mismatch times the heat-shear vorticity. -/
theorem spatialVorticity_momentumPressureResidual_heatShearVelocityField
    (μ ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (momentumPressureResidual μ (heatShearVelocityField ν a k)) t x =
      ((ν - μ) * k ^ (2 : ℕ)) •
        spatialVorticity (heatShearVelocityField ν a k) t x := by
  rw [momentumPressureResidual_heatShearVelocityField,
    spatialVorticity_const_smul]

/-- At the spacetime origin, the wrong-viscosity pressure residual has a
concrete nonzero curl component whenever the viscosity mismatch, amplitude, and
frequency are all nonzero. -/
theorem spatialVorticity_momentumPressureResidual_heatShearVelocityField_origin
    (μ ν a k : ℝ) :
    spatialVorticity (momentumPressureResidual μ (heatShearVelocityField ν a k)) 0 0 =
      EuclideanSpace.single nsCoord2 ((μ - ν) * a * k ^ (3 : ℕ)) := by
  rw [spatialVorticity_momentumPressureResidual_heatShearVelocityField,
    spatialVorticity_heatShearVelocityField]
  ext i
  fin_cases i <;>
    simp [nsCoord1, nsCoord2, mul_assoc, mul_left_comm, mul_comm]
  ring

/-- The wrong-viscosity heat-shear residual has nonzero curl at the origin under
the nondegeneracy assumptions `μ ≠ ν`, `a ≠ 0`, and `k ≠ 0`. -/
theorem spatialVorticity_momentumPressureResidual_heatShearVelocityField_origin_ne_zero
    {μ ν a k : ℝ} (hμν : μ ≠ ν) (ha : a ≠ 0) (hk : k ≠ 0) :
    spatialVorticity (momentumPressureResidual μ (heatShearVelocityField ν a k)) 0 0 ≠ 0 := by
  rw [spatialVorticity_momentumPressureResidual_heatShearVelocityField_origin]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord2) h
  have hprod : (μ - ν) * a * k ^ (3 : ℕ) = 0 := by
    simpa [nsCoord2] using hcoord
  exact
    (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hμν) ha)
      (pow_ne_zero (3 : ℕ) hk)) hprod

/-- No smooth pressure can repair a nondegenerate heat-shear profile into a
momentum equation at the wrong viscosity.  The obstruction is the curl of the
required pressure residual, so it is independent of any pressure ansatz. -/
theorem not_exists_smoothPressure_momentumEquation_heatShearVelocityField_wrongViscosity
    {μ ν a k : ℝ} (hμν : μ ≠ ν) (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ t x,
          timeVelocityDerivative (heatShearVelocityField ν a k) t x +
              spatialConvection (heatShearVelocityField ν a k) t x +
              spatialPressureGradient p t x =
            μ • spatialLaplacian (heatShearVelocityField ν a k) t x := by
  exact
    not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
      (ν := μ) (u := heatShearVelocityField ν a k)
      ⟨0, 0,
        spatialVorticity_momentumPressureResidual_heatShearVelocityField_origin_ne_zero
          hμν ha hk⟩

/-- If the scalar amplitude misses the heat ODE at a sampled time, then the
pressure residual of the general shear ansatz has a concrete nonzero curl
component at that time. -/
theorem spatialVorticity_momentumPressureResidual_amplitudeShearVelocityField_origin
    {A : NSTime → ℝ} {A' μ k : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) :
    spatialVorticity (momentumPressureResidual μ (amplitudeShearVelocityField A k)) t 0 =
      EuclideanSpace.single nsCoord2 ((A' + μ * k ^ (2 : ℕ) * A t) * k) := by
  rw [spatialVorticity_congr_at
    (u := momentumPressureResidual μ (amplitudeShearVelocityField A k))
    (v := heatShearVelocityField 0 (-(A' + μ * k ^ (2 : ℕ) * A t)) k)
    (t := t) (x := 0)
    (momentumPressureResidual_amplitudeShearVelocityField_slice
      (A := A) (A' := A') (μ := μ) (k := k) (t := t) hA)]
  rw [spatialVorticity_heatShearVelocityField]
  ext i
  fin_cases i <;>
    simp [nsCoord1, nsCoord2, mul_left_comm, mul_comm]
  ring

/-- A nonzero sampled heat-ODE defect and nonzero wave number make the
general-amplitude pressure residual visibly non-gradient by curl. -/
theorem spatialVorticity_momentumPressureResidual_amplitudeShearVelocityField_origin_ne_zero
    {A : NSTime → ℝ} {A' μ k : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t)
    (hode : A' + μ * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0) :
    spatialVorticity (momentumPressureResidual μ (amplitudeShearVelocityField A k)) t 0 ≠ 0 := by
  rw [spatialVorticity_momentumPressureResidual_amplitudeShearVelocityField_origin hA]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord2) h
  have hprod : (A' + μ * k ^ (2 : ℕ) * A t) * k = 0 := by
    simpa [nsCoord2] using hcoord
  exact (mul_ne_zero hode hk) hprod

/-- No smooth pressure can repair a general time-amplitude shear ansatz at a
time where its scalar amplitude violates the heat ODE `A' + μ k² A = 0`.
The obstruction is the curl of the pressure residual, not a restriction to a
special pressure family. -/
theorem not_exists_smoothPressure_momentumEquation_amplitudeShearVelocityField_of_heatODE_mismatch_at
    {A : NSTime → ℝ} {A' μ k : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t)
    (hode : A' + μ * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ s x,
          timeVelocityDerivative (amplitudeShearVelocityField A k) s x +
              spatialConvection (amplitudeShearVelocityField A k) s x +
              spatialPressureGradient p s x =
            μ • spatialLaplacian (amplitudeShearVelocityField A k) s x := by
  exact
    not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
      (ν := μ) (u := amplitudeShearVelocityField A k)
      ⟨t, 0,
        spatialVorticity_momentumPressureResidual_amplitudeShearVelocityField_origin_ne_zero
          hA hode hk⟩

/-- The pressure residual of the undamped unit heat-shear profile has nonzero
curl at the origin, so it is not a smooth pressure gradient. -/
theorem spatialVorticity_momentumPressureResidual_undampedUnitHeatShearVelocityField_origin_ne_zero :
    spatialVorticity (momentumPressureResidual 1 (heatShearVelocityField 0 1 1)) 0 0 ≠ 0 := by
  rw [momentumPressureResidual_undampedUnitHeatShearVelocityField,
    spatialVorticity_neg, spatialVorticity_heatShearVelocityField]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord2) h
  simp [nsCoord2] at hcoord

/-- No smooth pressure can repair the undamped unit heat-shear profile into the
unit-viscosity momentum equation.  The obstruction is the nonzero curl of the
required pressure residual, not a restriction to a special pressure ansatz. -/
theorem not_exists_smoothPressure_momentumEquation_undampedUnitHeatShearVelocityField_unitViscosity :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ t x,
          timeVelocityDerivative (heatShearVelocityField 0 1 1) t x +
              spatialConvection (heatShearVelocityField 0 1 1) t x +
              spatialPressureGradient p t x =
            (1 : ℝ) • spatialLaplacian (heatShearVelocityField 0 1 1) t x := by
  exact
    not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
      (ν := 1) (u := heatShearVelocityField 0 1 1)
      ⟨0, 0,
        spatialVorticity_momentumPressureResidual_undampedUnitHeatShearVelocityField_origin_ne_zero⟩

/-- The heat-shear family with streamwise drift has the same vorticity as pure
heat shear. -/
theorem spatialVorticity_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearStreamwiseDriftVelocityField ν a k d) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k)) := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d)) t x)]
  simp [spatialVorticity_heatShearVelocityField,
    spatialVorticity_constantVelocityField]

/-- The heat-shear family with vertical drift has the same vorticity as pure
heat shear. -/
theorem spatialVorticity_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearVerticalDriftVelocityField ν a k c) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k)) := by
  rw [heatShearVerticalDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  simp [spatialVorticity_heatShearVelocityField,
    spatialVorticity_constantVelocityField]

/-- The heat-shear family with full drift has the same vorticity as pure heat
shear. -/
theorem spatialVorticity_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearFullDriftVelocityField ν a k d c) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k)) := by
  rw [heatShearFullDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  simp [spatialVorticity_heatShearStreamwiseDriftVelocityField,
    spatialVorticity_constantVelocityField]
end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
