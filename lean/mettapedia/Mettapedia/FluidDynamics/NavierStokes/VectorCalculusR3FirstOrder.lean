import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Smoothness

/-!
# Vector Calculus R3: FirstOrder

First-order spatial, temporal, divergence, and pressure-gradient identities.
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

/-- The spatial pressure gradient only depends on the pressure field on the
fixed time slice. -/
theorem spatialPressureGradient_congr_at
    {p q : NSPressureField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, p t y = q t y) :
    spatialPressureGradient p t x = spatialPressureGradient q t x := by
  unfold spatialPressureGradient
  have hf : (fun y : NSSpace => p t y) = fun y : NSSpace => q t y := funext h
  rw [hf]

/-- The spatial Fréchet derivative commutes with constant scalar multiplication. -/
theorem spatialFDeriv_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (a • u) t x = a • spatialFDeriv u t x := by
  rw [spatialFDeriv, spatialFDeriv]
  change fderiv ℝ (a • fun y : NSSpace => u t y) x = a • fderiv ℝ (fun y : NSSpace => u t y) x
  rw [fderiv_const_smul_field]
  rfl

/-- The spatial Fréchet derivative commutes with addition. -/
theorem spatialFDeriv_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialFDeriv (u + v) t x = spatialFDeriv u t x + spatialFDeriv v t x := by
  rw [spatialFDeriv, spatialFDeriv, spatialFDeriv]
  change fderiv ℝ ((fun y : NSSpace => u t y) + fun y : NSSpace => v t y) x = _
  rw [fderiv_add hu hv]

/-- The spatial Fréchet derivative of the zero field is zero. -/
theorem spatialFDeriv_zero (t : NSTime) (x : NSSpace) :
    spatialFDeriv (0 : NSVelocityField) t x = 0 := by
  simp [spatialFDeriv]

/-- The spatial Fréchet derivative of a constant velocity field is zero. -/
theorem spatialFDeriv_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (constantVelocityField c) t x = 0 := by
  simp [spatialFDeriv, constantVelocityField]

/-- The spatial Fréchet derivative of the steady linear shear field is the
same linear shear map at every space-time point. -/
theorem spatialFDeriv_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (linearShearVelocityField a) t x = linearShearMap a := by
  unfold spatialFDeriv linearShearVelocityField
  change fderiv ℝ (linearShearInitialVelocity a) x = linearShearMap a
  rw [linearShearInitialVelocity]
  exact (linearShearMap a).fderiv (x := x)

/-- The spatial Fréchet derivative of the steady field `u(t,x) = (a * x₁, 0, b)`
is the same linear shear map at every space-time point. -/
theorem spatialFDeriv_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (linearShearVerticalDriftVelocityField a b) t x = linearShearMap a := by
  rw [linearShearVerticalDriftVelocityField]
  rw [spatialFDeriv_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
      (EuclideanSpace.single nsCoord2 b)) t x)]
  simp [spatialFDeriv_linearShearVelocityField, spatialFDeriv_constantVelocityField]

/-- The spatial Fréchet derivative of the steady field `u(t,x) = (a * x₁, b, 0)`
is the same linear shear map at every space-time point. -/
theorem spatialFDeriv_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (linearShearHorizontalDriftVelocityField a b) t x = linearShearMap a := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [spatialFDeriv_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t x)]
  simp [spatialFDeriv_linearShearVelocityField, spatialFDeriv_constantVelocityField]

/-- The spatial Fréchet derivative of the damped sinusoidal heat-shear field is
supported on the `x₁` direction and the first velocity component. -/
theorem spatialFDeriv_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (heatShearVelocityField ν a k) t x =
      coord0Embedding.comp
        (((a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) : ℝ) •
          (Real.cos (k * x nsCoord1) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  have hcoord : HasFDerivAt (fun y : NSSpace => k * y nsCoord1)
      ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)) x := by
    refine
      ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).hasFDerivAt.const_smul k).congr_of_eventuallyEq ?_
    filter_upwards with y
    simp [smul_eq_mul]
  have hsin : HasFDerivAt (fun y : NSSpace => Real.sin (k * y nsCoord1))
      (Real.cos (k * x nsCoord1) •
        ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))) x := by
    simpa using hcoord.sin
  have hscalar : HasFDerivAt
      (fun y : NSSpace => A * Real.sin (k * y nsCoord1))
      ((A : ℝ) •
        (Real.cos (k * x nsCoord1) •
          ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))) x := by
    refine (hsin.const_smul A).congr_of_eventuallyEq ?_
    filter_upwards with y
    simp [smul_eq_mul]
  have hvec : HasFDerivAt
      (fun y : NSSpace => coord0Embedding (A * Real.sin (k * y nsCoord1)))
      (coord0Embedding.comp
        ((A : ℝ) •
          (Real.cos (k * x nsCoord1) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) x := by
    exact coord0Embedding.hasFDerivAt.comp x hscalar
  unfold spatialFDeriv
  simpa [heatShearVelocityField, heatShearScalar, A, mul_assoc] using hvec.fderiv

/-- The spatial Fréchet derivative of the general time-amplitude shear ansatz
has the same slice formula as heat shear, with the sampled amplitude `A t`. -/
theorem spatialFDeriv_amplitudeShearVelocityField
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (amplitudeShearVelocityField A k) t x =
      coord0Embedding.comp
        (((A t : ℝ) •
          (Real.cos (k * x nsCoord1) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearVelocityField A k t y = heatShearVelocityField 0 (A t) k t y := by
    intro y
    simp [amplitudeShearVelocityField, heatShearVelocityField, heatShearScalar]
  rw [spatialFDeriv_congr_at hslice]
  simpa [heatShearScalar]
    using spatialFDeriv_heatShearVelocityField 0 (A t) k t x

/-- The heat-shear family with streamwise drift has the same spatial Fréchet
derivative as pure heat shear. -/
theorem spatialFDeriv_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (heatShearStreamwiseDriftVelocityField ν a k d) t x =
      coord0Embedding.comp
        (((a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) : ℝ) •
          (Real.cos (k * x nsCoord1) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [spatialFDeriv_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d)) t x)]
  simp [spatialFDeriv_heatShearVelocityField, spatialFDeriv_constantVelocityField]

/-- The time derivative commutes with constant scalar multiplication. -/
theorem timeVelocityDerivative_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (a • u) t x = a • timeVelocityDerivative u t x := by
  rw [timeVelocityDerivative, timeVelocityDerivative, timeFDeriv, timeFDeriv]
  change fderiv ℝ (a • fun s : NSTime => u s x) t (1 : ℝ) =
      a • fderiv ℝ (fun s : NSTime => u s x) t (1 : ℝ)
  rw [fderiv_const_smul_field]
  rfl

/-- The time derivative commutes with addition. -/
theorem timeVelocityDerivative_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun s : NSTime => u s x) t)
    (hv : DifferentiableAt ℝ (fun s : NSTime => v s x) t) :
    timeVelocityDerivative (u + v) t x =
      timeVelocityDerivative u t x + timeVelocityDerivative v t x := by
  rw [timeVelocityDerivative, timeVelocityDerivative, timeVelocityDerivative, timeFDeriv, timeFDeriv,
    timeFDeriv]
  change fderiv ℝ ((fun s : NSTime => u s x) + fun s : NSTime => v s x) t (1 : ℝ) = _
  rw [fderiv_add hu hv]
  simp

/-- The time derivative of the zero field is zero. -/
theorem timeVelocityDerivative_zero (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (0 : NSVelocityField) t x = 0 := by
  simp [timeVelocityDerivative, timeFDeriv]

/-- The time derivative of a constant velocity field is zero. -/
theorem timeVelocityDerivative_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (constantVelocityField c) t x = 0 := by
  simp [timeVelocityDerivative, timeFDeriv, constantVelocityField]

/-- The time-independent seed has zero time derivative. -/
theorem timeVelocityDerivative_timeIndependentVelocity
    (u₀ : NSInitialVelocity) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0 := by
  simp [timeVelocityDerivative, timeFDeriv, timeIndependentVelocity]

/-- The steady linear shear field has zero time derivative. -/
theorem timeVelocityDerivative_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVelocityField a) t x = 0 := by
  simp [linearShearVelocityField, timeVelocityDerivative, timeFDeriv]

/-- The steady field `u(t,x) = (a * x₁, 0, b)` has zero time derivative. -/
theorem timeVelocityDerivative_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVerticalDriftVelocityField a b) t x = 0 := by
  rw [linearShearVerticalDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_linearShearVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · dsimp [linearShearVelocityField]
    exact differentiableAt_const ((linearShearInitialVelocity a) x)
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord2 b : NSSpace)

/-- The steady field `u(t,x) = (a * x₁, b, 0)` has zero time derivative. -/
theorem timeVelocityDerivative_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearHorizontalDriftVelocityField a b) t x = 0 := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_linearShearVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · dsimp [linearShearVelocityField]
    exact differentiableAt_const ((linearShearInitialVelocity a) x)
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord1 b : NSSpace)

/-- The steady field `u(t,x) = (a * x₁, b, c)` has zero time derivative. -/
theorem timeVelocityDerivative_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearFullDriftVelocityField a b c) t x = 0 := by
  rw [linearShearFullDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_linearShearHorizontalDriftVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · dsimp [linearShearHorizontalDriftVelocityField]
    exact differentiableAt_const ((linearShearHorizontalDriftInitialVelocity a b) x)
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord2 c : NSSpace)

/-- The damped sinusoidal heat-shear field has the expected heat-decay time
derivative. -/
theorem timeVelocityDerivative_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVelocityField ν a k) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  let S : ℝ := Real.sin (k * x nsCoord1)
  have hexp : HasDerivAt
      (fun s : ℝ => Real.exp (-(ν * k ^ (2 : ℕ)) * s))
      (Real.exp (-(ν * k ^ (2 : ℕ)) * t) * (-(ν * k ^ (2 : ℕ)))) t := by
    simpa [smul_eq_mul, mul_assoc] using
      (((hasDerivAt_id' t).const_mul (-(ν * k ^ (2 : ℕ)))).exp)
  have hscalar : HasDerivAt
      (fun s : ℝ => a * Real.exp (-(ν * k ^ (2 : ℕ)) * s) * S)
      (-(ν * k ^ (2 : ℕ)) *
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * S)) t := by
    simpa [S, mul_assoc, mul_left_comm, mul_comm] using
      hexp.mul_const (a * S)
  have hvec := coord0Embedding.hasFDerivAt.comp t hscalar.hasFDerivAt
  have hvec' : HasFDerivAt
      (fun s : NSTime =>
        coord0Embedding
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * s) * S))
      (coord0Embedding.comp
        (ContinuousLinearMap.toSpanSingleton ℝ
          (-(ν * k ^ (2 : ℕ)) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * S)))) t := by
    refine hvec.congr_of_eventuallyEq ?_
    filter_upwards with s
    rfl
  have happly :=
    congrArg (fun L : ℝ →L[ℝ] NSSpace => L (1 : ℝ)) hvec'.fderiv
  simpa [timeVelocityDerivative, timeFDeriv, heatShearVelocityField, heatShearScalar,
    coord0Embedding_apply, ContinuousLinearMap.toSpanSingleton_apply,
    S, ContinuousLinearMap.comp_apply, mul_assoc, mul_left_comm, mul_comm] using happly

/-- The time derivative of the general time-amplitude shear ansatz is exactly
the sampled scalar amplitude derivative times the fixed sine mode. -/
theorem timeVelocityDerivative_amplitudeShearVelocityField
    {A : NSTime → ℝ} {A' : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) (k : ℝ) (x : NSSpace) :
    timeVelocityDerivative (amplitudeShearVelocityField A k) t x =
      coord0Embedding (A' * Real.sin (k * x nsCoord1)) := by
  let S : ℝ := Real.sin (k * x nsCoord1)
  have hscalar : HasDerivAt (fun s : ℝ => A s * S) (A' * S) t := by
    simpa [S, mul_assoc, mul_left_comm, mul_comm] using hA.mul_const S
  have hvec := coord0Embedding.hasFDerivAt.comp t hscalar.hasFDerivAt
  have hvec' : HasFDerivAt
      (fun s : NSTime => coord0Embedding (A s * S))
      (coord0Embedding.comp (ContinuousLinearMap.toSpanSingleton ℝ (A' * S))) t := by
    refine hvec.congr_of_eventuallyEq ?_
    filter_upwards with s
    rfl
  have happly :=
    congrArg (fun L : ℝ →L[ℝ] NSSpace => L (1 : ℝ)) hvec'.fderiv
  simpa [timeVelocityDerivative, timeFDeriv, amplitudeShearVelocityField,
    coord0Embedding_apply, ContinuousLinearMap.toSpanSingleton_apply,
    S, ContinuousLinearMap.comp_apply, mul_assoc, mul_left_comm, mul_comm] using happly

/-- The heat-shear family with streamwise drift has the same time derivative as
pure heat shear. -/
theorem timeVelocityDerivative_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearStreamwiseDriftVelocityField ν a k d) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_heatShearVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_timeSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord0 d : NSSpace)

/-- The heat-shear family with vertical drift has the same time derivative as
pure heat shear. -/
theorem timeVelocityDerivative_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVerticalDriftVelocityField ν a k c) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearVerticalDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_heatShearVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_timeSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord2 c : NSSpace)

/-- The heat-shear family with full drift has the same time derivative as pure
heat shear. -/
theorem timeVelocityDerivative_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearFullDriftVelocityField ν a k d c) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearFullDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_heatShearStreamwiseDriftVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_timeSlice
      (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d) t x
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord2 c : NSSpace)

/-- Spatial divergence commutes with constant scalar multiplication. -/
theorem spatialDivergence_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialDivergence (a • u) t x = a * spatialDivergence u t x := by
  rw [spatialDivergence, spatialFDeriv]
  change ∑ i : Fin 3,
      (fderiv ℝ (a • fun y : NSSpace => u t y) x (EuclideanSpace.single i (1 : ℝ))) i = _
  rw [fderiv_const_smul_field]
  simp
  rw [← Finset.mul_sum]
  rfl

/-- Spatial divergence commutes with addition. -/
theorem spatialDivergence_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialDivergence (u + v) t x =
      spatialDivergence u t x + spatialDivergence v t x := by
  rw [spatialDivergence, spatialDivergence, spatialDivergence, spatialFDeriv, spatialFDeriv, spatialFDeriv]
  change ∑ i : Fin 3,
      (fderiv ℝ ((fun y : NSSpace => u t y) + fun y : NSSpace => v t y) x
        (EuclideanSpace.single i (1 : ℝ))) i = _
  rw [fderiv_add hu hv]
  simp [Finset.sum_add_distrib]

/-- Spatial divergence of the zero field is zero. -/
theorem spatialDivergence_zero (t : NSTime) (x : NSSpace) :
    spatialDivergence (0 : NSVelocityField) t x = 0 := by
  simp [spatialDivergence, spatialFDeriv]

/-- Spatial divergence of a constant velocity field is zero. -/
theorem spatialDivergence_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialDivergence (constantVelocityField c) t x = 0 := by
  simp [spatialDivergence, spatialFDeriv, constantVelocityField]

/-- Spatial divergence of the time-independent seed is exactly the divergence
of the initial datum. -/
theorem spatialDivergence_timeIndependentVelocity
    (u₀ : NSInitialVelocity) (t : NSTime) (x : NSSpace) :
    spatialDivergence (timeIndependentVelocity u₀) t x =
      initialSpatialDivergence u₀ x :=
  rfl

/-- Spatial divergence of the steady linear shear field is zero. -/
theorem spatialDivergence_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (linearShearVelocityField a) t x = 0 := by
  rw [spatialDivergence, spatialFDeriv_linearShearVelocityField, Fin.sum_univ_three]
  simp [linearShearMap, nsCoord0, nsCoord1, ContinuousLinearMap.smulRight_apply]

/-- The steady field `u(t,x) = (a * x₁, 0, b)` is divergence free. -/
theorem spatialDivergence_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (linearShearVerticalDriftVelocityField a b) t x = 0 := by
  rw [linearShearVerticalDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_linearShearVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 b)) t x

/-- The steady field `u(t,x) = (a * x₁, b, 0)` is divergence free. -/
theorem spatialDivergence_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (linearShearHorizontalDriftVelocityField a b) t x = 0 := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_linearShearVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t x

/-- The steady field `u(t,x) = (a * x₁, b, c)` is divergence free. -/
theorem spatialDivergence_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (linearShearFullDriftVelocityField a b c) t x = 0 := by
  rw [linearShearFullDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_linearShearHorizontalDriftVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x

/-- The damped sinusoidal heat-shear field is divergence free. -/
theorem spatialDivergence_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearVelocityField ν a k) t x = 0 := by
  rw [spatialDivergence, spatialFDeriv_heatShearVelocityField, Fin.sum_univ_three]
  simp [coord0Embedding_apply, nsCoord0, nsCoord1]

/-- The general time-amplitude shear ansatz is divergence free on each time
slice. -/
theorem spatialDivergence_amplitudeShearVelocityField
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (amplitudeShearVelocityField A k) t x = 0 := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearVelocityField A k t y = heatShearVelocityField 0 (A t) k t y := by
    intro y
    simp [amplitudeShearVelocityField, heatShearVelocityField, heatShearScalar]
  rw [spatialDivergence_congr_at hslice]
  simpa
    using spatialDivergence_heatShearVelocityField 0 (A t) k t x

/-- The heat-shear family with streamwise drift is divergence free. -/
theorem spatialDivergence_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearStreamwiseDriftVelocityField ν a k d) t x = 0 := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_heatShearVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d)) t x

/-- The heat-shear family with vertical drift is divergence free. -/
theorem spatialDivergence_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearVerticalDriftVelocityField ν a k c) t x = 0 := by
  rw [heatShearVerticalDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_heatShearVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x

/-- The heat-shear family with full drift is spatially divergence free. -/
theorem spatialDivergence_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearFullDriftVelocityField ν a k d c) t x = 0 := by
  rw [heatShearFullDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_heatShearStreamwiseDriftVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x

/-- Divergence of initial data commutes with constant scalar multiplication. -/
theorem initialSpatialDivergence_const_smul
    (a : ℝ) (u₀ : NSInitialVelocity) (x : NSSpace) :
    initialSpatialDivergence (a • u₀) x = a * initialSpatialDivergence u₀ x := by
  rw [initialSpatialDivergence]
  rw [fderiv_const_smul_field]
  simp
  rw [← Finset.mul_sum]
  rfl

/-- Divergence of initial data commutes with addition. -/
theorem initialSpatialDivergence_add
    {u₀ v₀ : NSInitialVelocity} {x : NSSpace}
    (hu : DifferentiableAt ℝ u₀ x) (hv : DifferentiableAt ℝ v₀ x) :
    initialSpatialDivergence (u₀ + v₀) x =
      initialSpatialDivergence u₀ x + initialSpatialDivergence v₀ x := by
  rw [initialSpatialDivergence, initialSpatialDivergence, initialSpatialDivergence]
  rw [fderiv_add hu hv]
  simp [Finset.sum_add_distrib]

/-- Divergence of zero initial data is zero. -/
theorem initialSpatialDivergence_zero (x : NSSpace) :
    initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
  simp [initialSpatialDivergence]

/-- Divergence of constant initial velocity data is zero. -/
theorem initialSpatialDivergence_constantInitialVelocity
    (c : NSSpace) (x : NSSpace) :
    initialSpatialDivergence (constantInitialVelocity c) x = 0 := by
  unfold initialSpatialDivergence constantInitialVelocity
  simp [fderiv_const_apply]

/-- Divergence of the concrete linear shear initial data is zero. -/
theorem initialSpatialDivergence_linearShearInitialVelocity
    (a : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearInitialVelocity a) x = 0 := by
  have hf :
      fderiv ℝ (linearShearInitialVelocity a) x = linearShearMap a := by
    simp [linearShearInitialVelocity, linearShearMap]
  rw [initialSpatialDivergence, hf, Fin.sum_univ_three]
  simp [linearShearMap, nsCoord0, nsCoord1, ContinuousLinearMap.smulRight_apply]

/-- Divergence of the initial data `x ↦ (a * x₁, 0, b)` is zero. -/
theorem initialSpatialDivergence_linearShearVerticalDriftInitialVelocity
    (a b : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearVerticalDriftInitialVelocity a b) x = 0 := by
  rw [linearShearVerticalDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_linearShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_linearShearInitialVelocity a).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 b)).contDiffAt (x := x)).differentiableAt (by simp)

/-- Divergence of the initial data `x ↦ (a * x₁, b, 0)` is zero. -/
theorem initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity
    (a b : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearHorizontalDriftInitialVelocity a b) x = 0 := by
  rw [linearShearHorizontalDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_linearShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_linearShearInitialVelocity a).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord1 b)).contDiffAt (x := x)).differentiableAt (by simp)

/-- Divergence of the initial data `x ↦ (a * x₁, b, c)` is zero. -/
theorem initialSpatialDivergence_linearShearFullDriftInitialVelocity
    (a b c : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearFullDriftInitialVelocity a b c) x = 0 := by
  rw [linearShearFullDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 c)).contDiffAt (x := x)).differentiableAt (by simp)

/-- The damped sinusoidal initial datum is divergence free. -/
theorem initialSpatialDivergence_heatShearInitialVelocity
    (a k : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearInitialVelocity a k) x = 0 := by
  have hslice :
      (fun y : NSSpace => heatShearInitialVelocity a k y) =
        fun y : NSSpace => heatShearVelocityField 0 a k 0 y := by
    funext y
    simp [heatShearVelocityField, heatShearInitialVelocity, heatShearScalar,
      heatShearInitialScalar]
  simpa [initialSpatialDivergence, spatialDivergence, spatialFDeriv, hslice] using
    (spatialDivergence_heatShearVelocityField (ν := 0) a k 0 x : _)

/-- The heat-shear datum with streamwise drift is divergence free. -/
theorem initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity
    (a k d : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearStreamwiseDriftInitialVelocity a k d) x = 0 := by
  rw [heatShearStreamwiseDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearInitialVelocity a k).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord0 d)).contDiffAt (x := x)).differentiableAt (by simp)

/-- The heat-shear datum with vertical drift is divergence free. -/
theorem initialSpatialDivergence_heatShearVerticalDriftInitialVelocity
    (a k c : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearVerticalDriftInitialVelocity a k c) x = 0 := by
  rw [heatShearVerticalDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearInitialVelocity a k).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 c)).contDiffAt (x := x)).differentiableAt (by simp)

/-- The heat-shear datum with full drift is divergence free. -/
theorem initialSpatialDivergence_heatShearFullDriftInitialVelocity
    (a k d c : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearFullDriftInitialVelocity a k d c) x = 0 := by
  rw [heatShearFullDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 c)).contDiffAt (x := x)).differentiableAt (by simp)

/-- Pressure gradient commutes with addition. -/
theorem spatialPressureGradient_add
    {p q : NSPressureField} {t : NSTime} {x : NSSpace}
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : DifferentiableAt ℝ (fun y : NSSpace => q t y) x) :
    spatialPressureGradient (p + q) t x =
      spatialPressureGradient p t x + spatialPressureGradient q t x := by
  unfold spatialPressureGradient
  change gradient ((fun y : NSSpace => p t y) + fun y : NSSpace => q t y) x = _
  rw [gradient, fderiv_add hp hq]
  simp [gradient]

/-- Pressure gradient commutes with constant scalar multiplication. -/
theorem spatialPressureGradient_const_smul
    (a : ℝ) (p : NSPressureField) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (a • p) t x = a • spatialPressureGradient p t x := by
  unfold spatialPressureGradient
  change gradient (a • fun y : NSSpace => p t y) x = _
  rw [gradient, fderiv_const_smul_field]
  simp [gradient]

/-- Pressure gradient commutes with sign flip. -/
theorem spatialPressureGradient_neg
    (p : NSPressureField) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (-p) t x = -spatialPressureGradient p t x := by
  simpa using spatialPressureGradient_const_smul (-1 : ℝ) p t x

/-- Pressure gradient commutes with subtraction. -/
theorem spatialPressureGradient_sub
    {p q : NSPressureField} {t : NSTime} {x : NSSpace}
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : DifferentiableAt ℝ (fun y : NSSpace => q t y) x) :
    spatialPressureGradient (p - q) t x =
      spatialPressureGradient p t x - spatialPressureGradient q t x := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [spatialPressureGradient_add (p := p) (q := -q) hp hq.neg]
  rw [spatialPressureGradient_neg]

/-- Pressure gradient commutes with real linear combinations. -/
theorem spatialPressureGradient_linearCombination
    {p q : NSPressureField} {t : NSTime} {x : NSSpace}
    (a b : ℝ)
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : DifferentiableAt ℝ (fun y : NSSpace => q t y) x) :
    spatialPressureGradient (a • p + b • q) t x =
      a • spatialPressureGradient p t x + b • spatialPressureGradient q t x := by
  rw [spatialPressureGradient_add (hp.const_smul a) (hq.const_smul b)]
  rw [spatialPressureGradient_const_smul, spatialPressureGradient_const_smul]

/-- Pressure gradient of the zero field is zero. -/
theorem spatialPressureGradient_zero (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (0 : NSPressureField) t x = 0 := by
  simp [spatialPressureGradient]

/-- Pressure gradient of a spatially constant pressure field is zero. -/
theorem spatialPressureGradient_const
    (c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun _ : NSTime => fun _ : NSSpace => c) t x = 0 := by
  unfold spatialPressureGradient
  simp

/-- Pressure gradient of a time-only pressure field is zero on every spatial
slice. -/
theorem spatialPressureGradient_timeOnly
    (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => π s) t x = 0 := by
  unfold spatialPressureGradient
  simp

/-- Any affine combination of a spatially constant pressure and a time-only
pressure is still time-only, hence has zero spatial gradient on every slice. -/
theorem spatialPressureGradient_affineConstantTimeOnly
    (a b c : ℝ) (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
      (a • (fun _ : NSTime => fun _ : NSSpace => c) +
        b • (fun s : NSTime => fun _ : NSSpace => π s)) t x = 0 := by
  change
    spatialPressureGradient
      (fun s : NSTime => fun _ : NSSpace => a • c + b • π s) t x = 0
  simpa [smul_eq_mul] using
    spatialPressureGradient_timeOnly (fun s : NSTime => a • c + b • π s) t x

/-- The spatial gradient of the coordinate-linear pressure field
`p(t,x) = c * x₀` is the constant vector `c e₀`. -/
theorem spatialPressureGradient_coord0Linear
    (c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => c * y nsCoord0) t x =
      EuclideanSpace.single nsCoord0 c := by
  have hdual :
      (InnerProductSpace.toDual ℝ NSSpace) (EuclideanSpace.single nsCoord0 c) =
        c • (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ) := by
    ext y
    rw [InnerProductSpace.toDual_apply_apply]
    simp [EuclideanSpace.inner_single_left, nsCoord0]
  unfold spatialPressureGradient
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  rw [hdual]
  refine
    (((EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ).hasFDerivAt.const_smul c).congr_of_eventuallyEq ?_)
  filter_upwards with y
  simp [smul_eq_mul]

/-- The compensating pressure field `p(t,x) = -(a * b) * x₀` has constant
spatial gradient `-(a * b) e₀`. -/
theorem spatialPressureGradient_linearShearHorizontalDriftPressureField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (linearShearHorizontalDriftPressureField a b) t x =
      EuclideanSpace.single nsCoord0 (-(a * b)) := by
  rw [spatialPressureGradient_congr_at
    (p := linearShearHorizontalDriftPressureField a b)
    (q := fun _ : NSTime => fun y : NSSpace => (-(a * b)) * y nsCoord0)
    (t := t) (x := x)]
  · exact
    spatialPressureGradient_coord0Linear (-(a * b)) t x
  · intro y
    change -(a * b * y nsCoord0) = (-(a * b)) * y nsCoord0
    ring
end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
