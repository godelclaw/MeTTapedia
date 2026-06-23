import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeBoundedEnergyCore

/-!
# Navier-Stokes finite-mode anti-profile witnesses

Concrete bump and anti-profile constructions showing how the two-mode
Schwartz residual expansions behave in cancellation and nonzero-profile cases.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Unit smooth bump at the origin of physical space.  This supplies a concrete
nonzero compactly supported smooth profile, hence a Schwartz profile. -/
def nsUnitBumpScalar : ContDiffBump (0 : NSSpace) := default

/-- A compactly supported smooth first-coordinate bump. -/
def nsUnitBumpVectorFun : NSSpace → NSSpace :=
  fun x => nsUnitBumpScalar x • EuclideanSpace.single nsCoord0 (1 : ℝ)

/-- A concrete nonzero Schwartz velocity profile, obtained from a compactly
supported bump. -/
def nsUnitBumpSchwartzVelocity : NSSchwartzInitialVelocity :=
  ((nsUnitBumpScalar.hasCompactSupport.smul_right :
      HasCompactSupport nsUnitBumpVectorFun).toSchwartzMap <| by
    simpa [nsUnitBumpVectorFun] using
      (nsUnitBumpScalar.contDiff.smul
        (contDiff_const :
          ContDiff ℝ ∞ fun _ : NSSpace => EuclideanSpace.single nsCoord0 (1 : ℝ))))

/-- The concrete bump profile is nonzero at the origin. -/
theorem nsUnitBumpSchwartzVelocity_nonzero_at_origin :
    nsUnitBumpSchwartzVelocity (0 : NSSpace) ≠ 0 := by
  have hbump : nsUnitBumpScalar (0 : NSSpace) = 1 := by
    exact nsUnitBumpScalar.one_of_mem_closedBall
      (Metric.mem_closedBall_self nsUnitBumpScalar.rIn_pos.le)
  have hvalue : nsUnitBumpSchwartzVelocity (0 : NSSpace) =
      EuclideanSpace.single nsCoord0 (1 : ℝ) := by
    simp [nsUnitBumpSchwartzVelocity, hbump]
  intro hzero
  have hcoord : (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 = 1 := by
    simp [nsCoord0]
  have : (0 : NSSpace) nsCoord0 = 1 := by
    rw [← hcoord, ← hvalue, hzero]
  norm_num at this

/-- The concrete bump profile is nonzero. -/
theorem nsUnitBumpSchwartzVelocity_nonzero :
    ∃ x : NSSpace, nsUnitBumpSchwartzVelocity x ≠ 0 :=
  ⟨0, nsUnitBumpSchwartzVelocity_nonzero_at_origin⟩

/-- Equal constant amplitudes applied to a profile and its negative cancel as
a two-mode space-time velocity field. -/
theorem oneOneAntiProfileSchwartzVelocity_zero
    (f : NSSchwartzInitialVelocity) :
    twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f) =
      (0 : NSVelocityField) := by
  funext t x
  simp [twoModeSchwartzVelocity]

/-- Equal constant amplitudes applied to a profile and its negative cancel on
the initial slice. -/
theorem oneOneAntiProfileSchwartzInitialVelocity_zero
    (f : NSSchwartzInitialVelocity) :
    twoModeSchwartzInitialVelocity 1 1 f (-f) =
      (0 : NSInitialVelocity) := by
  funext x
  simp [twoModeSchwartzInitialVelocity]

/-- Equal time-dependent amplitudes applied to a profile and its negative
cancel as a two-mode space-time velocity field. -/
theorem equalAmplitudeAntiProfileSchwartzVelocity_zero
    (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) :
    twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) := by
  funext t x
  simp [twoModeSchwartzVelocity]

/-- Equal scalar amplitudes applied to a profile and its negative cancel on
the initial slice. -/
theorem equalAmplitudeAntiProfileSchwartzInitialVelocity_zero
    (a0 : ℝ) (f : NSSchwartzInitialVelocity) :
    twoModeSchwartzInitialVelocity a0 a0 f (-f) =
      (0 : NSInitialVelocity) := by
  funext x
  simp [twoModeSchwartzInitialVelocity]

/-- For a nonzero profile, an anti-profile two-mode velocity is identically
zero exactly when the two scalar amplitudes are pointwise equal.  This makes
the cancellation boundary exact: unequal amplitudes cannot hide inside the
`f, -f` ansatz as another zero-flow repair. -/
theorem antiProfileSchwartzVelocity_eq_zero_iff_equalAmplitude
    (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (hf : ∃ x : NSSpace, f x ≠ 0) :
    twoModeSchwartzVelocity a b f (-f) = (0 : NSVelocityField) ↔
      ∀ t, a t = b t := by
  constructor
  · intro hzero t
    rcases hf with ⟨x, hx⟩
    have hpoint : a t • f x + b t • (-(f x)) = 0 := by
      have htx := congrFun (congrFun hzero t) x
      simpa [twoModeSchwartzVelocity] using htx
    have hscale : (a t - b t) • f x = 0 := by
      calc
        (a t - b t) • f x = a t • f x - b t • f x := by
          rw [sub_smul]
        _ = a t • f x + -(b t • f x) := by
          rw [sub_eq_add_neg]
        _ = a t • f x + b t • (-(f x)) := by
          simp
        _ = 0 := hpoint
    have hsub : a t - b t = 0 := by
      rcases smul_eq_zero.mp hscale with hcoeff | hprofile
      · exact hcoeff
      · exact False.elim (hx hprofile)
    exact sub_eq_zero.mp hsub
  · intro heq
    funext t x
    simp [twoModeSchwartzVelocity, heq t]

/-- For a nonzero profile, an anti-profile initial slice is zero exactly when
the two initial scalar amplitudes are equal. -/
theorem antiProfileSchwartzInitialVelocity_eq_zero_iff_equalAmplitude
    (a0 b0 : ℝ) (f : NSSchwartzInitialVelocity)
    (hf : ∃ x : NSSpace, f x ≠ 0) :
    twoModeSchwartzInitialVelocity a0 b0 f (-f) = (0 : NSInitialVelocity) ↔
      a0 = b0 := by
  constructor
  · intro hzero
    rcases hf with ⟨x, hx⟩
    have hpoint : a0 • f x + b0 • (-(f x)) = 0 := by
      have hxzero := congrFun hzero x
      simpa [twoModeSchwartzInitialVelocity] using hxzero
    have hscale : (a0 - b0) • f x = 0 := by
      calc
        (a0 - b0) • f x = a0 • f x - b0 • f x := by
          rw [sub_smul]
        _ = a0 • f x + -(b0 • f x) := by
          rw [sub_eq_add_neg]
        _ = a0 • f x + b0 • (-(f x)) := by
          simp
        _ = 0 := hpoint
    have hsub : a0 - b0 = 0 := by
      rcases smul_eq_zero.mp hscale with hcoeff | hprofile
      · exact hcoeff
      · exact False.elim (hx hprofile)
    exact sub_eq_zero.mp hsub
  · intro heq
    funext x
    simp [twoModeSchwartzInitialVelocity, heq]

/-- If the scalar amplitudes differ somewhere and the profile is nonzero, the
anti-profile two-mode velocity is nonzero somewhere. -/
theorem exists_antiProfileSchwartzVelocity_ne_zero_of_exists_amplitude_ne
    (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (hf : ∃ x : NSSpace, f x ≠ 0)
    (hab : ∃ t, a t ≠ b t) :
    ∃ t x, twoModeSchwartzVelocity a b f (-f) t x ≠ 0 := by
  by_contra hnone
  have hzero : twoModeSchwartzVelocity a b f (-f) = (0 : NSVelocityField) := by
    funext t x
    by_contra htx
    exact hnone ⟨t, x, htx⟩
  have heq := (antiProfileSchwartzVelocity_eq_zero_iff_equalAmplitude a b f hf).mp hzero
  rcases hab with ⟨t, ht⟩
  exact ht (heq t)

/-- A profile paired with its negative satisfies the full positive-viscosity
momentum equation against any time-only pressure gauge in the affine-plus-
Schwartz pressure class.  The cancellation is recorded explicitly, so this is a
residual-closure baseline rather than a non-cancelling finite-mode flow. -/
theorem momentumEquation_oneOneAntiProfileSchwartzVelocity_affineTimeOnlyPressure_of_posViscosity
    {ν : ℝ} (_hν : 0 < ν) (π : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x +
          spatialPressureGradient
            (affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x := by
  intro t x
  simpa [oneOneAntiProfileSchwartzVelocity_zero f,
    affineAddScalarSchwartzPressure_zero_timeOnly π q] using
    momentumEquation_zeroVelocityField_timeOnlyPressure ν π t x

/-- Equal time-dependent amplitudes applied to a profile and its negative
satisfy the momentum equation against any time-only affine-plus-Schwartz
pressure gauge.  The pressure may be nonzero as a function of time, but the
velocity field is still the zero flow. -/
theorem momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineTimeOnlyPressure
    (a : NSTime → ℝ) (ν : ℝ) (π : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
          spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
          spatialPressureGradient
            (affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  intro t x
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  simpa [hvel, affineAddScalarSchwartzPressure_zero_timeOnly π q] using
    momentumEquation_zeroVelocityField_timeOnlyPressure ν π t x

/-- A zero equal-amplitude anti-profile cannot satisfy the momentum equation
against a pure spatial-affine pressure unless that affine coefficient is
identically zero.  This rules out repairing the cancellation branch by inserting
a nonzero spatial affine pressure gradient. -/
theorem momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_spatialAffinePressure_implies_zeroAffineCoeff
    (a : NSTime → ℝ) (ν : ℝ) (c : NSTime → NSSpace) (π : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hME :
      ∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient
              (affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q) t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) :
    ∀ t, c t = 0 := by
  intro t
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  have hlap : spatialLaplacian (0 : NSVelocityField) t (0 : NSSpace) = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t (0 : NSSpace)
  simpa [hvel, timeVelocityDerivative_zero, spatialConvection_zero,
    hlap,
    spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine c π q t
      (0 : NSSpace)] using hME t (0 : NSSpace)

/-- Contrapositive form of the spatial-affine pressure obstruction: if the
affine pressure coefficient is nonzero at some time, the equal-amplitude
anti-profile zero flow cannot satisfy the Navier-Stokes momentum equation with
that pure spatial-affine pressure. -/
theorem not_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_spatialAffinePressure_of_exists_nonzeroAffineCoeff
    (a : NSTime → ℝ) (ν : ℝ) (c : NSTime → NSSpace) (π : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ∃ t, c t ≠ 0) :
    ¬
      (∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient
              (affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q) t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) := by
  intro hME
  rcases hc with ⟨t, ht⟩
  exact ht
    (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_spatialAffinePressure_implies_zeroAffineCoeff
      a ν c π f q hME t)

/-- Expanded residual closure for the anti-profile construction, with positive
viscosity and a time-only affine-plus-Schwartz pressure. -/
theorem explicitClosure_oneOneAntiProfileSchwartzVelocity_affineTimeOnlyPressure_of_posViscosity
    {ν : ℝ} (hν : 0 < ν) (π : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    ∀ t x,
        spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x ((-f) x) +
            spatialFDeriv
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x (f x) +
            spatialConvection
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x +
          spatialPressureGradient
            (affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q) t x =
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x) := by
  intro t x
  have hmom :=
    momentumEquation_oneOneAntiProfileSchwartzVelocity_affineTimeOnlyPressure_of_posViscosity
      hν π f q t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const f (-f) t x,
    spatialConvection_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f) t x,
    spatialLaplacian_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f) t x] at hmom
  simpa using hmom

/-- Equal time-dependent amplitudes applied to a profile and its negative
satisfy the momentum equation against the zero time-indexed Schwartz pressure
slice for every viscosity.  The result is still a zero-flow cancellation
baseline, but it removes the artificial unit-amplitude restriction. -/
theorem momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
    (a : NSTime → ℝ) (ν : ℝ) (f : NSSchwartzInitialVelocity) :
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
          spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
          spatialPressureGradient
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  intro t x
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  simpa [hvel] using momentumEquation_zeroVelocityField_zeroPressure ν t x

/-- Expanded pressure-slice residual closure for the equal-amplitude
anti-profile construction.  This is a generalized cancellation baseline: the
time derivative, convection, and Laplacian expansions all cancel because the
actual velocity field is identically zero. -/
theorem explicitClosure_equalAmplitudeAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a)
    (ν : ℝ) (f : NSSchwartzInitialVelocity) :
    ∀ t x,
      deriv a t • f x + deriv a t • (-f) x +
            ((a t ^ (2 : ℕ)) •
                spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              (a t * a t) •
                spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x ((-f) x) +
              (a t * a t) •
                spatialFDeriv
                  (timeIndependentVelocity
                    (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
                  t x (f x) +
              (a t ^ (2 : ℕ)) •
                spatialConvection
                  (timeIndependentVelocity
                    (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
                  t x) +
          spatialPressureGradient
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) t x =
        (ν : ℝ) •
          (a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            a t • spatialLaplacian
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x) := by
  intro t x
  have hmom :=
    momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
      a ν f t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := a) (b := a) ha ha f (-f) t x,
    spatialConvection_twoModeSchwartzVelocity a a f (-f) t x,
    spatialLaplacian_twoModeSchwartzVelocity a a f (-f) t x] at hmom
  simpa using hmom

/-- Expanded residual closure for the anti-profile construction with zero
pressure. -/
theorem explicitClosure_oneOneAntiProfileSchwartzVelocity_zeroPressure_of_posViscosity
    {ν : ℝ} (hν : 0 < ν) (f : NSSchwartzInitialVelocity) :
    ∀ t x,
        spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x ((-f) x) +
            spatialFDeriv
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x (f x) +
            spatialConvection
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x) := by
  intro t x
  have hclosure :=
    explicitClosure_oneOneAntiProfileSchwartzVelocity_affineTimeOnlyPressure_of_posViscosity
      hν (fun _ : NSTime => 0) f (0 : 𝓢(NSSpace, ℝ)) t x
  have hp :
      affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
          (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) =
        (0 : NSPressureField) := by
    funext s y
    simp [affineAddScalarSchwartzPressure]
  simpa [hp] using hclosure

/-- Expanded residual closure for the anti-profile construction with the zero
time-indexed Schwartz pressure slice.  This is the pressure-slice version of
the cancellation baseline above. -/
theorem explicitClosure_oneOneAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
    (ν : ℝ) (f : NSSchwartzInitialVelocity) :
    ∀ t x,
        spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x ((-f) x) +
            spatialFDeriv
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x (f x) +
            spatialConvection
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x +
          spatialPressureGradient
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) t x =
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x) := by
  intro t x
  have hmom :
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x +
          spatialPressureGradient
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x := by
    simpa [oneOneAntiProfileSchwartzVelocity_zero f] using
      momentumEquation_zeroVelocityField_zeroPressure ν t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const f (-f) t x,
    spatialConvection_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f) t x,
    spatialLaplacian_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f) t x] at hmom
  simpa using hmom

/-- There are nonzero Schwartz profiles and an explicit pressure field
(`p = 0`) satisfying the expanded full-viscous residual closure for every
positive viscosity.  The two profile contributions cancel in the resulting
two-mode velocity, so this theorem is a concrete closure sanity check for the
residual expansion. -/
theorem exists_nonzeroSchwartzProfiles_pressure_explicitClosure_fullViscousNS_of_posViscosity
    {ν : ℝ} (hν : 0 < ν) :
    ∃ f g : NSSchwartzInitialVelocity, ∃ p : NSPressureField,
      (∃ x : NSSpace, f x ≠ 0) ∧
      (∃ x : NSSpace, g x ≠ 0) ∧
      (∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
              spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
              spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x +
            spatialPressureGradient p t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) := by
  refine ⟨nsUnitBumpSchwartzVelocity, -nsUnitBumpSchwartzVelocity, 0, ?_, ?_, ?_⟩
  · exact nsUnitBumpSchwartzVelocity_nonzero
  · rcases nsUnitBumpSchwartzVelocity_nonzero with ⟨x, hx⟩
    exact ⟨x, by simpa using neg_ne_zero.mpr hx⟩
  · simpa using
      explicitClosure_oneOneAntiProfileSchwartzVelocity_zeroPressure_of_posViscosity
        hν nsUnitBumpSchwartzVelocity
end NavierStokes
end FluidDynamics
end Mettapedia
