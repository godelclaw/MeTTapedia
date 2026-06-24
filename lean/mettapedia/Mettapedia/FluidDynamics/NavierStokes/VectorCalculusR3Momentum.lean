import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Laplacian

/-!
# Vector Calculus R3: Momentum

Coordinate derivative, convection, and momentum-equation identities for non-transported shear fields.
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

/-- A coordinate derivative commutes with constant scalar multiplication. -/
theorem spatialDerivativeComponent_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace)
    (coord comp : Fin 3) :
    spatialDerivativeComponent (a • u) t x coord comp =
      a * spatialDerivativeComponent u t x coord comp := by
  rw [spatialDerivativeComponent, spatialFDeriv]
  change (fderiv ℝ (a • fun y : NSSpace => u t y) x (EuclideanSpace.single coord (1 : ℝ))) comp = _
  rw [fderiv_const_smul_field]
  rfl

/-- A coordinate derivative commutes with addition. -/
theorem spatialDerivativeComponent_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x)
    (coord comp : Fin 3) :
    spatialDerivativeComponent (u + v) t x coord comp =
      spatialDerivativeComponent u t x coord comp +
        spatialDerivativeComponent v t x coord comp := by
  rw [spatialDerivativeComponent, spatialDerivativeComponent, spatialDerivativeComponent,
    spatialFDeriv, spatialFDeriv, spatialFDeriv]
  change (fderiv ℝ ((fun y : NSSpace => u t y) + fun y : NSSpace => v t y) x
      (EuclideanSpace.single coord (1 : ℝ))) comp = _
  rw [fderiv_add hu hv]
  rfl

/-- A coordinate derivative of the zero field is zero. -/
theorem spatialDerivativeComponent_zero
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (0 : NSVelocityField) t x coord comp = 0 := by
  simp [spatialDerivativeComponent, spatialFDeriv]

/-- Every coordinate derivative of a constant velocity field is zero. -/
theorem spatialDerivativeComponent_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (constantVelocityField c) t x coord comp = 0 := by
  simp [spatialDerivativeComponent, spatialFDeriv, constantVelocityField]

/-- The convection term of the zero field is zero. -/
theorem spatialConvection_zero
    (t : NSTime) (x : NSSpace) :
    spatialConvection (0 : NSVelocityField) t x = 0 := by
  rw [spatialConvection, spatialFDeriv_zero]
  simp

/-- The convection term is quadratic under constant velocity rescaling. -/
theorem spatialConvection_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialConvection (a • u) t x = (a ^ (2 : ℕ)) • spatialConvection u t x := by
  rw [spatialConvection, spatialFDeriv_const_smul]
  calc
    (a • spatialFDeriv u t x) (a • u t x) = a • (spatialFDeriv u t x (a • u t x)) := by
      simp
    _ = a • (a • spatialFDeriv u t x (u t x)) := by
      simp
    _ = (a ^ (2 : ℕ)) • spatialConvection u t x := by
      simp [spatialConvection, pow_two, smul_smul]

/-- The convection term expands over addition into the two self-terms plus the
two mixed directional-derivative terms. -/
theorem spatialConvection_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialConvection (u + v) t x =
      spatialConvection u t x + spatialFDeriv u t x (v t x) +
        spatialFDeriv v t x (u t x) + spatialConvection v t x := by
  rw [spatialConvection, spatialFDeriv_add hu hv]
  calc
    (spatialFDeriv u t x + spatialFDeriv v t x) (u t x + v t x) =
        spatialFDeriv u t x (u t x + v t x) +
          spatialFDeriv v t x (u t x + v t x) := by
      simp
    _ =
        (spatialFDeriv u t x (u t x) + spatialFDeriv u t x (v t x)) +
          (spatialFDeriv v t x (u t x) + spatialFDeriv v t x (v t x)) := by
      simp
    _ =
        spatialConvection u t x + spatialFDeriv u t x (v t x) +
          spatialFDeriv v t x (u t x) + spatialConvection v t x := by
      simp [spatialConvection]
      ac_rfl

/-- The convection term is unchanged under sign flip. -/
theorem spatialConvection_neg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialConvection (-u) t x = spatialConvection u t x := by
  simpa using spatialConvection_const_smul (-1 : ℝ) u t x

/-- The convection term expands over subtraction into the two self-terms minus
the two mixed directional-derivative terms. -/
theorem spatialConvection_sub
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialConvection (u - v) t x =
      spatialConvection u t x - spatialFDeriv u t x (v t x) -
        spatialFDeriv v t x (u t x) + spatialConvection v t x := by
  rw [sub_eq_add_neg]
  rw [spatialConvection_add hu hv.neg]
  rw [spatialConvection_neg]
  rw [show spatialFDeriv (-v) t x = (-1 : ℝ) • spatialFDeriv v t x by
    simpa using spatialFDeriv_const_smul (-1 : ℝ) v t x]
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The convection term of a linear combination expands into the two quadratic
self-terms plus the mixed directional-derivative terms. -/
theorem spatialConvection_linearCombination
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (a b : ℝ)
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialConvection (a • u + b • v) t x =
      (a ^ (2 : ℕ)) • spatialConvection u t x +
        (a * b) • spatialFDeriv u t x (v t x) +
        (a * b) • spatialFDeriv v t x (u t x) +
        (b ^ (2 : ℕ)) • spatialConvection v t x := by
  rw [spatialConvection_add (hu.const_smul a) (hv.const_smul b)]
  rw [spatialConvection_const_smul, spatialConvection_const_smul]
  simp [spatialFDeriv_const_smul, pow_two, smul_smul]
  ac_rfl

/-- The convection term of a constant velocity field is zero. -/
theorem spatialConvection_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialConvection (constantVelocityField c) t x = 0 := by
  rw [spatialConvection, spatialFDeriv_constantVelocityField]
  simp

/-- Constant velocity fields satisfy the exact zero-pressure momentum identity
for every viscosity. -/
theorem momentumEquation_constantVelocityField_zeroPressure
    (ν : ℝ) (c : NSSpace) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (constantVelocityField c) t x +
        spatialConvection (constantVelocityField c) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (constantVelocityField c) t x := by
  rw [timeVelocityDerivative_constantVelocityField,
    spatialConvection_constantVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_constantVelocityField]
  simp

/-- Constant velocity fields remain exact pointwise solutions after adding any
time-only pressure gauge, since such gauges have zero spatial gradient. -/
theorem momentumEquation_constantVelocityField_timeOnlyPressure
    (ν : ℝ) (c : NSSpace) (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (constantVelocityField c) t x +
        spatialConvection (constantVelocityField c) t x +
        spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => π s) t x =
      ν • spatialLaplacian (constantVelocityField c) t x := by
  rw [timeVelocityDerivative_constantVelocityField,
    spatialConvection_constantVelocityField,
    spatialPressureGradient_timeOnly,
    spatialLaplacian_constantVelocityField]
  simp

/-- The zero velocity field is the degenerate constant-field baseline for the
exact zero-pressure momentum identity. -/
theorem momentumEquation_zeroVelocityField_zeroPressure
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (0 : NSVelocityField) t x +
        spatialConvection (0 : NSVelocityField) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (0 : NSVelocityField) t x := by
  have hzero : constantVelocityField (0 : NSSpace) = (0 : NSVelocityField) := by
    funext t x
    simp [constantVelocityField]
  simpa [hzero] using momentumEquation_constantVelocityField_zeroPressure ν (0 : NSSpace) t x

/-- The zero velocity field likewise remains an exact pointwise solution after
adding any time-only pressure gauge. -/
theorem momentumEquation_zeroVelocityField_timeOnlyPressure
    (ν : ℝ) (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (0 : NSVelocityField) t x +
        spatialConvection (0 : NSVelocityField) t x +
        spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => π s) t x =
      ν • spatialLaplacian (0 : NSVelocityField) t x := by
  have hzero : constantVelocityField (0 : NSSpace) = (0 : NSVelocityField) := by
    funext t x
    simp [constantVelocityField]
  simpa [hzero] using momentumEquation_constantVelocityField_timeOnlyPressure ν (0 : NSSpace) π t x

/-- Pointwise momentum identities are stable under adding any extra pressure
field whose spatial gradient vanishes at the point in question. -/
theorem momentumEquation_addPressureOfZeroSpatialGradient
    {u : NSVelocityField} {p q : NSPressureField} {ν : ℝ} {t : NSTime} {x : NSSpace}
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : DifferentiableAt ℝ (fun y : NSSpace => q t y) x)
    (hq_zero : spatialPressureGradient q t x = 0)
    (h :
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x) :
    timeVelocityDerivative u t x + spatialConvection u t x +
        spatialPressureGradient (p + q) t x =
      ν • spatialLaplacian u t x := by
  rw [spatialPressureGradient_add hp hq, hq_zero, add_zero]
  exact h

/-- Pointwise momentum identities are in particular stable under adding an
arbitrary time-only pressure gauge. -/
theorem momentumEquation_addTimeOnlyPressure
    {u : NSVelocityField} {p : NSPressureField} {ν : ℝ} {t : NSTime} {x : NSSpace}
    (π : NSTime → ℝ)
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (h :
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x) :
    timeVelocityDerivative u t x + spatialConvection u t x +
        spatialPressureGradient (p + fun s : NSTime => fun _ : NSSpace => π s) t x =
      ν • spatialLaplacian u t x := by
  have hq : DifferentiableAt ℝ (fun y : NSSpace => (fun _ : NSSpace => π t) y) x := by
    simp
  exact momentumEquation_addPressureOfZeroSpatialGradient hp hq
    (spatialPressureGradient_timeOnly π t x) h

/-- The steady linear shear field has zero convection term. -/
theorem spatialConvection_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (linearShearVelocityField a) t x = 0 := by
  rw [spatialConvection, spatialFDeriv_linearShearVelocityField, linearShearVelocityField,
    linearShearInitialVelocity_apply]
  ext i
  fin_cases i <;> simp [linearShearMap, nsCoord0, nsCoord1, ContinuousLinearMap.smulRight_apply]

/-- The steady field `u(t,x) = (a * x₁, 0, b)` has zero convection term. -/
theorem spatialConvection_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (linearShearVerticalDriftVelocityField a b) t x = 0 := by
  rw [linearShearVerticalDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 b)) t x)]
  rw [spatialConvection_linearShearVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_linearShearVelocityField,
    spatialFDeriv_constantVelocityField]
  have hmap : linearShearMap a (EuclideanSpace.single nsCoord2 b) = 0 := by
    ext i
    fin_cases i <;>
      simp [linearShearMap, nsCoord0, nsCoord1, nsCoord2,
        ContinuousLinearMap.smulRight_apply]
  simp [hmap]

/-- The steady field `u(t,x) = (a * x₁, b, 0)` has constant convection term
`(a * b, 0, 0)`. -/
theorem spatialConvection_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (linearShearHorizontalDriftVelocityField a b) t x =
      EuclideanSpace.single nsCoord0 (a * b) := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t x)]
  rw [spatialConvection_linearShearVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_linearShearVelocityField,
    spatialFDeriv_constantVelocityField]
  have hmap :
      linearShearMap a (EuclideanSpace.single nsCoord1 b) =
        EuclideanSpace.single nsCoord0 (a * b) := by
    ext i
    fin_cases i <;>
      simp [linearShearMap, nsCoord0, nsCoord1,
        ContinuousLinearMap.smulRight_apply, mul_comm]
  simp [hmap]

/-- The steady field `u(t,x) = (a * x₁, b, c)` has the same constant
convection term `(a * b, 0, 0)` as the horizontal-drift branch. -/
theorem spatialConvection_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (linearShearFullDriftVelocityField a b c) t x =
      EuclideanSpace.single nsCoord0 (a * b) := by
  rw [linearShearFullDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  rw [spatialConvection_linearShearHorizontalDriftVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_linearShearHorizontalDriftVelocityField,
    spatialFDeriv_constantVelocityField]
  have hmap : linearShearMap a (EuclideanSpace.single nsCoord2 c) = 0 := by
    ext i
    fin_cases i <;>
      simp [linearShearMap, nsCoord0, nsCoord1, nsCoord2,
        ContinuousLinearMap.smulRight_apply]
  simp [hmap]

/-- The steady linear shear field satisfies the exact zero-pressure momentum
identity for every viscosity. -/
theorem momentumEquation_linearShearVelocityField_zeroPressure
    (ν a : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVelocityField a) t x +
        spatialConvection (linearShearVelocityField a) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (linearShearVelocityField a) t x := by
  rw [timeVelocityDerivative_linearShearVelocityField,
    spatialConvection_linearShearVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_linearShearVelocityField]
  simp

/-- The steady field `u(t,x) = (a * x₁, 0, b)` satisfies the same exact
zero-pressure momentum identity for every viscosity. -/
theorem momentumEquation_linearShearVerticalDriftVelocityField_zeroPressure
    (ν a b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVerticalDriftVelocityField a b) t x +
        spatialConvection (linearShearVerticalDriftVelocityField a b) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (linearShearVerticalDriftVelocityField a b) t x := by
  rw [timeVelocityDerivative_linearShearVerticalDriftVelocityField,
    spatialConvection_linearShearVerticalDriftVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_linearShearVerticalDriftVelocityField]
  simp

/-- The steady field `u(t,x) = (a * x₁, b, 0)` satisfies the exact momentum
identity with compensating affine pressure `p(t,x) = -(a * b) * x₀`. -/
theorem momentumEquation_linearShearHorizontalDriftVelocityField
    (ν a b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearHorizontalDriftVelocityField a b) t x +
        spatialConvection (linearShearHorizontalDriftVelocityField a b) t x +
        spatialPressureGradient (linearShearHorizontalDriftPressureField a b) t x =
      ν • spatialLaplacian (linearShearHorizontalDriftVelocityField a b) t x := by
  rw [timeVelocityDerivative_linearShearHorizontalDriftVelocityField,
    spatialConvection_linearShearHorizontalDriftVelocityField,
    spatialPressureGradient_linearShearHorizontalDriftPressureField,
    spatialLaplacian_linearShearHorizontalDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [nsCoord0]

/-- The steady field `u(t,x) = (a * x₁, b, c)` satisfies the same exact
momentum identity with affine pressure `p(t,x) = -(a * b) * x₀`. -/
theorem momentumEquation_linearShearFullDriftVelocityField
    (ν a b c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearFullDriftVelocityField a b c) t x +
        spatialConvection (linearShearFullDriftVelocityField a b c) t x +
        spatialPressureGradient (linearShearHorizontalDriftPressureField a b) t x =
      ν • spatialLaplacian (linearShearFullDriftVelocityField a b c) t x := by
  rw [timeVelocityDerivative_linearShearFullDriftVelocityField,
    spatialConvection_linearShearFullDriftVelocityField,
    spatialPressureGradient_linearShearHorizontalDriftPressureField,
    spatialLaplacian_linearShearFullDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [nsCoord0]

/-- The damped sinusoidal heat-shear field has zero convection term. -/
theorem spatialConvection_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearVelocityField ν a k) t x = 0 := by
  rw [spatialConvection, spatialFDeriv_heatShearVelocityField, heatShearVelocityField_apply]
  simp [coord0Embedding_apply, nsCoord0, nsCoord1, mul_assoc]

/-- The general time-amplitude shear ansatz has zero convection term: the
velocity is in the `x₀` direction and the profile is independent of `x₀`. -/
theorem spatialConvection_amplitudeShearVelocityField
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (amplitudeShearVelocityField A k) t x = 0 := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearVelocityField A k t y = heatShearVelocityField 0 (A t) k t y := by
    intro y
    simp [amplitudeShearVelocityField, heatShearVelocityField, heatShearScalar]
  rw [spatialConvection_congr_at hslice]
  simpa
    using spatialConvection_heatShearVelocityField 0 (A t) k t x

/-- The heat-shear family with streamwise drift also has zero convection term,
because the oscillatory part depends only on `x₁` while the added drift is in
the flow direction `x₀` and the field remains independent of `x₀`. -/
theorem spatialConvection_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearStreamwiseDriftVelocityField ν a k d) t x = 0 := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d)) t x)]
  rw [spatialConvection_heatShearVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_heatShearVelocityField,
    spatialFDeriv_constantVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, constantVelocityField, nsCoord0, nsCoord1,
      mul_left_comm, mul_comm]

/-- The heat-shear family with vertical drift also has zero convection term,
because the oscillatory part depends only on `x₁` while the drift is purely in
the `x₂` direction. -/
theorem spatialConvection_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearVerticalDriftVelocityField ν a k c) t x = 0 := by
  rw [heatShearVerticalDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  rw [spatialConvection_heatShearVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_heatShearVelocityField,
    spatialFDeriv_constantVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, constantVelocityField, nsCoord0, nsCoord1, nsCoord2,
      mul_left_comm, mul_comm]

/-- The heat-shear family with full drift also has zero convection term,
because the oscillatory part depends only on `x₁` while both added drifts are
constant and point along directions of independence. -/
theorem spatialConvection_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearFullDriftVelocityField ν a k d c) t x = 0 := by
  rw [heatShearFullDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  rw [spatialConvection_heatShearStreamwiseDriftVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_heatShearStreamwiseDriftVelocityField,
    spatialFDeriv_constantVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, constantVelocityField, nsCoord0, nsCoord1, nsCoord2,
      mul_left_comm, mul_comm]

/-- The damped sinusoidal heat-shear velocity field satisfies the exact
zero-pressure momentum identity. -/
theorem momentumEquation_heatShearVelocityField_zeroPressure
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVelocityField ν a k) t x +
        spatialConvection (heatShearVelocityField ν a k) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearVelocityField ν a k) t x := by
  rw [timeVelocityDerivative_heatShearVelocityField,
    spatialConvection_heatShearVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- If a heat-shear field is evolved with viscosity `ν` but tested against a
momentum equation with viscosity `μ`, the required pressure residual is exactly
the viscosity mismatch times the heat profile. -/
theorem momentumPressureResidual_heatShearVelocityField
    (μ ν a k : ℝ) :
    momentumPressureResidual μ (heatShearVelocityField ν a k) =
      ((ν - μ) * k ^ (2 : ℕ)) • heatShearVelocityField ν a k := by
  funext t x
  ext i
  fin_cases i <;>
    simp [momentumPressureResidual, timeVelocityDerivative_heatShearVelocityField,
      spatialConvection_heatShearVelocityField, spatialLaplacian_heatShearVelocityField,
      heatShearVelocityField_apply, coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]
  ring

/-- On a fixed time slice, the pressure residual of a general amplitude shear
is exactly the sine shear with amplitude equal to the scalar heat-ODE defect
`-(A' + μ k² A(t))`. -/
theorem momentumPressureResidual_amplitudeShearVelocityField_slice
    {A : NSTime → ℝ} {A' μ k : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) :
    ∀ y : NSSpace,
      momentumPressureResidual μ (amplitudeShearVelocityField A k) t y =
        heatShearVelocityField 0 (-(A' + μ * k ^ (2 : ℕ) * A t)) k t y := by
  intro y
  ext i
  fin_cases i <;>
    simp [momentumPressureResidual,
      timeVelocityDerivative_amplitudeShearVelocityField hA,
      spatialConvection_amplitudeShearVelocityField,
      spatialLaplacian_amplitudeShearVelocityField,
      heatShearVelocityField_apply, coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_left_comm, mul_comm]
  ring

/-- At unit viscosity, the undamped unit heat-shear profile leaves exactly the
negative profile as the pressure residual.  This is the minimal concrete
positive-viscosity mismatch: the velocity is smooth and divergence-free, but it
has not been given the heat decay required by the viscous term. -/
theorem momentumPressureResidual_undampedUnitHeatShearVelocityField :
    momentumPressureResidual 1 (heatShearVelocityField 0 1 1) =
      -heatShearVelocityField 0 1 1 := by
  funext t x
  ext i
  fin_cases i <;>
    simp [momentumPressureResidual, timeVelocityDerivative_heatShearVelocityField,
      spatialConvection_heatShearVelocityField, spatialLaplacian_heatShearVelocityField,
      heatShearVelocityField_apply, coord0Embedding_apply, nsCoord0, nsCoord1]

/-- The heat-shear family with streamwise drift satisfies the same exact
zero-pressure momentum identity. -/
theorem momentumEquation_heatShearStreamwiseDriftVelocityField_zeroPressure
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearStreamwiseDriftVelocityField ν a k d) t x +
        spatialConvection (heatShearStreamwiseDriftVelocityField ν a k d) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearStreamwiseDriftVelocityField ν a k d) t x := by
  rw [timeVelocityDerivative_heatShearStreamwiseDriftVelocityField,
    spatialConvection_heatShearStreamwiseDriftVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearStreamwiseDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- The heat-shear family with vertical drift satisfies the same exact
zero-pressure momentum identity. -/
theorem momentumEquation_heatShearVerticalDriftVelocityField_zeroPressure
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVerticalDriftVelocityField ν a k c) t x +
        spatialConvection (heatShearVerticalDriftVelocityField ν a k c) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearVerticalDriftVelocityField ν a k c) t x := by
  rw [timeVelocityDerivative_heatShearVerticalDriftVelocityField,
    spatialConvection_heatShearVerticalDriftVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearVerticalDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- The heat-shear family with full drift satisfies the same exact
zero-pressure momentum identity. -/
theorem momentumEquation_heatShearFullDriftVelocityField_zeroPressure
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearFullDriftVelocityField ν a k d c) t x +
        spatialConvection (heatShearFullDriftVelocityField ν a k d c) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearFullDriftVelocityField ν a k d c) t x := by
  rw [timeVelocityDerivative_heatShearFullDriftVelocityField,
    spatialConvection_heatShearFullDriftVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearFullDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]
end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
