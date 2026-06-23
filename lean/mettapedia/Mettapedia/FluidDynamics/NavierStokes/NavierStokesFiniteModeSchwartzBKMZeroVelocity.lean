import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMSchwartzPressure

/-!
# Navier-Stokes Finite-Mode Schwartz BKM: ZeroVelocity

Zero-velocity BKM-data classification for initial data, time-only pressure, and spatial-affine pressure.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- BKM-data form of the zero-flow initial-data classification.  If a
finite-time witness is zero velocity after packaging it with a BKM envelope and
integral budget, then the initial velocity data must itself be zero. -/
theorem BKMData_zeroVelocity_implies_initialVelocity_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    u0 = 0 := by
  rcases hData with ⟨W, hWzero, _hWpress, _Ω, _Bint, _hEnv, _hInt⟩
  funext x
  have hinit := W.initial_condition x
  rw [hWzero] at hinit
  simpa using hinit.symm

/-- BKM-layer form of the zero-flow initial-data obstruction.  A nonzero
initial velocity cannot be paired with zero velocity by adding BKM envelope
data. -/
theorem not_exists_BKMData_zeroVelocity_of_initialVelocity_ne_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hu0 : u0 ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  exact hu0 (BKMData_zeroVelocity_implies_initialVelocity_zero hData)

/-- BKM-data form of the zero-flow pressure classification.  If a finite-time
witness is zero velocity after packaging it with a BKM envelope and integral
budget, then its pressure has zero spatial gradient throughout the certified
slab. -/
theorem BKMData_zeroVelocity_implies_spatialPressureGradient_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  rcases hData with ⟨W, hWzero, hWpress, _Ω, _Bint, _hEnv, _hInt⟩
  intro t x ht0 htT
  have hmom := W.momentum_equation_on t x ht0 htT
  have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t x
  simpa [hWzero, hWpress, timeVelocityDerivative_zero, spatialConvection_zero,
    hlap] using hmom

/-- Combined BKM-data classification for the zero-flow branch.  Such a package
can only be attached to zero initial velocity data and pressure with zero
spatial gradient throughout the certified slab. -/
theorem BKMData_zeroVelocity_implies_initialVelocity_zero_and_spatialPressureGradient_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    u0 = 0 ∧
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    ⟨BKMData_zeroVelocity_implies_initialVelocity_zero hData,
      BKMData_zeroVelocity_implies_spatialPressureGradient_zero hData⟩

/-- Exact zero-flow BKM-data classification.  For a smooth pressure field, a
zero-velocity BKM package exists exactly when the initial data are zero and the
pressure has zero spatial gradient throughout the certified slab.  Thus the
BKM envelope and integral-budget layer adds no extra escape hatch to the
finite-time zero-flow witness surface. -/
theorem BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  constructor
  · intro hData
    exact
      BKMData_zeroVelocity_implies_initialVelocity_zero_and_spatialPressureGradient_zero
        hData
  · rintro ⟨hu0, hgrad⟩
    subst hu0
    rcases
        (zeroVelocity_finiteTimeWitness_iff_spatialPressureGradient_zero
          (ν := ν) (T := T) p hp).2 hgrad with
      ⟨W, hWzero, hWpress⟩
    refine
      ⟨W, hWzero, hWpress, (fun _ : NSTime => 0), 0, ?_,
        integrableVorticityEnvelopeOn_zero T⟩
    simpa [hWzero] using (vorticityEnvelopeOn_zero T)

/-- Time-only pressure is the exact surviving zero-flow BKM gauge.  For every
smooth time-only pressure, zero-velocity BKM data exists exactly for zero
initial velocity data. -/
theorem BKMData_zeroVelocity_timeOnlyPressure_iff_initialVelocity_zero
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 := by
  constructor
  · intro hData
    exact
      ((BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν)
        (T := T)
        (u0 := u0)
        (p := fun t : NSTime => fun _ : NSSpace => π t)
        (smoothSpaceTimePressure_timeOnly hπ)).1 hData).1
  · intro hu0
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν)
        (T := T)
        (u0 := u0)
        (p := fun t : NSTime => fun _ : NSSpace => π t)
        (smoothSpaceTimePressure_timeOnly hπ)).2
        ⟨hu0, by
          intro t x _ht0 _htT
          exact spatialPressureGradient_timeOnly π t x⟩

/-- Positive BKM-data witness for the zero-flow branch with arbitrary smooth
time-only pressure.  This is the constructive half of the exact time-gauge
classification. -/
theorem BKMData_zeroVelocity_timeOnlyPressure
    {ν T : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    (BKMData_zeroVelocity_timeOnlyPressure_iff_initialVelocity_zero
      (ν := ν)
      (T := T)
      (u0 := (0 : NSInitialVelocity))
      π hπ).2 rfl

/-- Nonzero initial data remain impossible even for the surviving time-only
pressure gauge. -/
theorem not_exists_BKMData_zeroVelocity_timeOnlyPressure_of_initialVelocity_ne_zero
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π)
    (hu0 : u0 ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  exact hu0
    ((BKMData_zeroVelocity_timeOnlyPressure_iff_initialVelocity_zero
      (ν := ν) (T := T) (u0 := u0) π hπ).1 hData)

/-- BKM-layer form of the zero-flow pressure-gradient obstruction.  Even after
adding a vorticity envelope and an integral budget, a zero-flow finite-time
witness cannot carry any pressure field with a nonzero spatial gradient on the
certified slab. -/
theorem not_exists_BKMData_zeroVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases hfail with ⟨t, x, ht0, htT, hgrad⟩
  exact hgrad
    (BKMData_zeroVelocity_implies_spatialPressureGradient_zero hData t x ht0 htT)

/-- Combined BKM-layer zero-flow obstruction.  A proposed zero-velocity BKM
package is impossible as soon as either its initial velocity is nonzero or its
pressure has a nonzero spatial gradient somewhere on the certified slab. -/
theorem not_exists_BKMData_zeroVelocity_of_initialVelocity_ne_zero_or_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hfail :
      u0 ≠ 0 ∨
        ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases
      BKMData_zeroVelocity_implies_initialVelocity_zero_and_spatialPressureGradient_zero
        hData with
    ⟨hu0zero, hgradzero⟩
  cases hfail with
  | inl hu0 =>
      exact hu0 hu0zero
  | inr hgrad =>
      rcases hgrad with ⟨t, x, ht0, htT, hne⟩
      exact hne (hgradzero t x ht0 htT)

/-- Exact zero-flow BKM-data classification for the spatial-affine pressure
subclass.  A pressure of the form `⟪c t, x⟫ + π t` can appear in a zero-flow
BKM package exactly when the initial velocity is zero and the affine
coefficient `c` vanishes throughout the certified slab. -/
theorem BKMData_zeroVelocity_spatialAffinePressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧ ∀ t, 0 ≤ t → t ≤ T → c t = 0 := by
  have hp :
      smoothSpaceTimePressure
        (affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q) :=
    smoothSpaceTimePressure_affineAddScalarSchwartzPressure
      hc hπ (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ))) q
  constructor
  · intro hData
    rcases
        (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
          (ν := ν)
          (T := T)
          (u0 := u0)
          (p := affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q)
          hp).1 hData with
      ⟨hu0, hgrad⟩
    refine ⟨hu0, ?_⟩
    intro t ht0 htT
    simpa [spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine
      c π q t (0 : NSSpace)] using hgrad t (0 : NSSpace) ht0 htT
  · rintro ⟨hu0, hczero⟩
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν)
        (T := T)
        (u0 := u0)
        (p := affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q)
        hp).2
        ⟨hu0, by
          intro t x ht0 htT
          simpa [spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine
            c π q t x] using hczero t ht0 htT⟩

/-- Constructive zero-flow BKM data for the spatial-affine pressure subclass
when the affine coefficient vanishes on the certified slab. -/
theorem BKMData_zeroVelocity_spatialAffinePressure_of_affineCoeff_zeroOn
    {ν T : ℝ}
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π)
    (hczero : ∀ t, 0 ≤ t → t ≤ T → c t = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    (BKMData_zeroVelocity_spatialAffinePressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn
      (ν := ν)
      (T := T)
      (u0 := (0 : NSInitialVelocity))
      c π q hc hπ).2
      ⟨rfl, hczero⟩

/-- Combined spatial-affine zero-flow obstruction.  A proposed zero-velocity
BKM package in this pressure subclass is impossible as soon as either the
initial velocity is nonzero or the affine pressure coefficient is nonzero at
one certified slab time. -/
theorem not_exists_BKMData_zeroVelocity_spatialAffinePressure_of_initialVelocity_ne_zero_or_exists_nonzeroAffineCoeffOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π)
    (hfail :
      u0 ≠ 0 ∨ ∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases
      (BKMData_zeroVelocity_spatialAffinePressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn
        (ν := ν) (T := T) (u0 := u0) c π q hc hπ).1 hData with
    ⟨hu0zero, hczero⟩
  cases hfail with
  | inl hu0 =>
      exact hu0 hu0zero
  | inr hcz =>
      rcases hcz with ⟨t, ht0, htT, hct⟩
      exact hct (hczero t ht0 htT)

/-- BKM-layer form of the spatial-affine pressure obstruction.  Even after
adding a vorticity envelope and an integral budget, a zero-flow finite-time
witness with pure spatial-affine pressure forces the affine pressure
coefficient to vanish on the certified slab. -/
theorem not_exists_BKMData_zeroVelocity_spatialAffinePressure_of_exists_nonzeroAffineCoeffOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases hc with ⟨t, ht0, htT, hct⟩
  rcases hData with ⟨W, hWzero, hWpress, _Ω, _Bint, _hEnv, _hInt⟩
  exact hct
    (W.zeroVelocity_spatialAffinePressure_implies_zeroAffineCoeffOn
      c π q hWzero hWpress t ht0 htT)
end NavierStokes
end FluidDynamics
end Mettapedia
