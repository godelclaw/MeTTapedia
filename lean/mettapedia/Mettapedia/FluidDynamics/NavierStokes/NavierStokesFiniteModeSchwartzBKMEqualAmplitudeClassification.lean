import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMZeroOutput
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMEqualAmplitudeMomentum

/-!
# Navier-Stokes Finite-Mode Schwartz BKM: EqualAmplitudeClassification

Equal-amplitude anti-profile BKM-data and finite-energy continuation clause classifications.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Abstract BKM-data normalization for the equal-amplitude anti-profile
velocity over zero initial data.  The cancelled two-mode velocity carries
exactly the same BKM-data packages as the zero velocity, for any pressure
field. -/
theorem BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  constructor
  · rintro ⟨W, hWvel, hWpress, Ω, Bint, hEnv, hInt⟩
    refine ⟨W, ?_, hWpress, Ω, Bint, hEnv, hInt⟩
    calc
      W.velocity = twoModeSchwartzVelocity a a f (-f) := hWvel
      _ = (0 : NSVelocityField) := equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  · rintro ⟨W, hWzero, hWpress, Ω, Bint, hEnv, hInt⟩
    refine ⟨W, ?_, hWpress, Ω, Bint, hEnv, hInt⟩
    calc
      W.velocity = (0 : NSVelocityField) := hWzero
      _ = twoModeSchwartzVelocity a a f (-f) :=
        (equalAmplitudeAntiProfileSchwartzVelocity_zero a f).symm

/-- Abstract BKM-data normalization over the syntactic equal-amplitude
anti-profile initial datum.  After both the initial slice and velocity cancel,
this witness surface is exactly the zero-initial, zero-velocity BKM-data
surface for the same pressure field. -/
theorem BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVelocity
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  rw [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f]
  exact BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity a f p

/-- Exact zero-budget normal form for BKM data over the syntactic
equal-amplitude anti-profile initial datum.  On this cancelled branch, allowing
an arbitrary BKM envelope and integral budget is equivalent to using the same
finite-time witness with the identically zero envelope and zero budget. -/
theorem BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVorticityEnvelope_zeroBudget
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  constructor
  · rintro ⟨W, hWvel, hWpress, _Ω, _Bint, _hEnv, _hInt⟩
    rcases
        ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_has_zero_vorticityEnvelope
          a f W hWvel with
      ⟨hZeroEnv, hZeroInt⟩
    exact ⟨W, hWvel, hWpress, hZeroEnv, hZeroInt⟩
  · rintro ⟨W, hWvel, hWpress, hZeroEnv, hZeroInt⟩
    exact ⟨W, hWvel, hWpress, (fun _ : NSTime => 0), 0, hZeroEnv, hZeroInt⟩

/-- Exact arbitrary-pressure BKM-data classification for the cancelled
equal-amplitude anti-profile velocity over zero initial data.  For a smooth
pressure field, the only surviving pressure information is the zero spatial
gradient condition on the certified slab. -/
theorem BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  rw [BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity a f p]
  constructor
  · intro hData
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) hp).1 hData |>.2
  · intro hgrad
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) hp).2
        ⟨rfl, hgrad⟩

/-- Exact arbitrary-pressure BKM-data classification over the syntactic
equal-amplitude anti-profile initial datum.  The cancelled initial slice and
velocity reduce the package to the same pressure-gradient boundary as the
zero-flow branch. -/
theorem BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  rw [BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVelocity a f p]
  constructor
  · intro hData
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) hp).1 hData |>.2
  · intro hgrad
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) hp).2
        ⟨rfl, hgrad⟩

/-- Arbitrary-pressure no-go for BKM data on the cancelled equal-amplitude
anti-profile velocity.  Any nonzero pressure gradient on the certified slab
rules out the structured BKM-data package, independently of the pressure
ansatz. -/
theorem not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  intro hData
  exact
    (not_exists_BKMData_zeroVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) (p := p) hfail)
      ((BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity
        a f p).1 hData)

/-- Arbitrary-pressure no-go over the syntactic anti-profile initial datum.
Changing the pressure family cannot repair the cancelled branch unless the
pressure is spatially constant on the certified slab. -/
theorem not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  intro hData
  exact
    (not_exists_BKMData_zeroVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) (p := p) hfail)
      ((BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVelocity
        a f p).1 hData)

/-- Clause/data separation for arbitrary pressure fields on the cancelled
equal-amplitude anti-profile branch.  The repaired finite-energy BKM clause is
inhabited at the zero datum, but any pressure with a nonzero spatial gradient
on the certified slab cannot be packaged as matching BKM data for the cancelled
two-mode velocity. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_zero_and_not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = p ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ⟨ExplicitFiniteEnergyBKMContinuationClause_zero ν T,
      not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
        a f hfail⟩

/-- Syntactic initial-datum version of the arbitrary-pressure clause/data
separation.  A repaired finite-energy BKM clause remains available for the
cancelled anti-profile initial datum, but a pressure with nonzero slabwise
spatial gradient cannot be the matching BKM-data pressure. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = p ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  constructor
  · simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
      (ExplicitFiniteEnergyBKMContinuationClause_zero ν T)
  · exact
      not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_of_exists_spatialPressureGradient_ne_zero
        a f hfail

/-- Exact repaired-clause/BKM-data boundary for arbitrary smooth pressures on
the cancelled equal-amplitude anti-profile branch over zero initial data.  The
finite-energy BKM clause is always inhabited at the zero datum, so the
remaining obstruction to matching BKM data is precisely the spatial pressure
gradient on the certified slab. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_zero_and_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  constructor
  · rintro ⟨_hClause, hData⟩
    exact
      (BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
        (ν := ν) (T := T) a f hp).1 hData
  · intro hgrad
    exact
      ⟨ExplicitFiniteEnergyBKMContinuationClause_zero ν T,
        (BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
          (ν := ν) (T := T) a f hp).2 hgrad⟩

/-- Syntactic initial-datum version of the exact repaired-clause/BKM-data
boundary.  The equal-amplitude anti-profile initial datum reduces to zero, so
the combined clause-and-data package exists exactly when the pressure is
spatially constant on the certified slab. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  constructor
  · rintro ⟨_hClause, hData⟩
    exact
      (BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
        (ν := ν) (T := T) a f hp).1 hData
  · intro hgrad
    exact
      ⟨by
          simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
            (ExplicitFiniteEnergyBKMContinuationClause_zero ν T),
        (BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
          (ν := ν) (T := T) a f hp).2 hgrad⟩

/-- Arbitrary-pressure constructor-input separation for the repaired
finite-energy BKM clause over the syntactic anti-profile initial datum.  The
repaired clause is inhabited, but the pointwise momentum equation for the
cancelled anti-profile velocity is impossible for any pressure with a nonzero
spatial gradient. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hbad : ∃ t, ∃ x, spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  constructor
  · simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
      (ExplicitFiniteEnergyBKMContinuationClause_zero ν T)
  · intro hME
    rcases hbad with ⟨t, x, hgrad⟩
    exact hgrad
      ((momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
        a ν f p).1 hME t x)

/-- Exact arbitrary-pressure constructor-input boundary for the repaired
finite-energy BKM clause over the syntactic anti-profile initial datum.  Since
the repaired clause is inhabited after the anti-profile initial slice cancels,
the conjunction with the raw pointwise momentum equation is exactly the
zero-pressure-gradient condition. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  constructor
  · rintro ⟨_hClause, hME⟩
    exact
      (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
        a ν f p).1 hME
  · intro hgrad
    exact
      ⟨by
          simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
            (ExplicitFiniteEnergyBKMContinuationClause_zero ν T),
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
          a ν f p).2 hgrad⟩

/-- Exact arbitrary-pressure clause/data/constructor boundary for the
cancelled equal-amplitude anti-profile branch.  Adding the BKM-data witness
does not weaken the raw constructor requirement: the repaired finite-energy
BKM clause, matching BKM data, and pointwise momentum equation coexist exactly
when the arbitrary pressure has zero spatial gradient everywhere. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_and_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ∧
      ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  constructor
  · rintro ⟨_hClause, _hData, hME⟩
    exact
      (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
        a ν f p).1 hME
  · intro hgrad
    refine ⟨?_, ?_, ?_⟩
    · simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
        (ExplicitFiniteEnergyBKMContinuationClause_zero ν T)
    · exact
        (BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
          (ν := ν) (T := T) a f hp).2
          (by
            intro t x _ht0 _htT
            exact hgrad t x)
    · exact
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
          a ν f p).2 hgrad

/-- BKM-data classification for the equal-amplitude anti-profile branch with
the full affine-plus-localized Schwartz pressure class.  Even after adding the
BKM witness and envelope layer, this branch is exactly the zero-flow pressure
classification: the affine coefficient vanishes on the certified slab, and any
nonzero localized amplitude on that slab forces the fixed Schwartz pressure
gradient to vanish everywhere. -/
theorem BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  rw [BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity
    a f (affineAddScalarSchwartzPressure c π ρ q)]
  constructor
  · intro hData
    rcases
        (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
          (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity))
          c π ρ q hc hπ hρ).1 hData with
      ⟨_hInitial, hcZero, hgradZero⟩
    exact ⟨hcZero, hgradZero⟩
  · rintro ⟨hcZero, hgradZero⟩
    exact
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity))
        c π ρ q hc hπ hρ).2
        ⟨rfl, hcZero, hgradZero⟩

/-- Same exact classification over the syntactic equal-amplitude anti-profile
initial datum.  Because that initial slice is definitionally the zero datum
after the anti-profile cancellation lemma, the BKM-data surface is still exactly
the zero-flow affine-plus-localized pressure classification. -/
theorem BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  rw [BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVelocity
    a f (affineAddScalarSchwartzPressure c π ρ q)]
  constructor
  · intro hData
    rcases
        (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
          (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity))
          c π ρ q hc hπ hρ).1 hData with
      ⟨_hInitial, hcZero, hgradZero⟩
    exact ⟨hcZero, hgradZero⟩
  · rintro ⟨hcZero, hgradZero⟩
    exact
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity))
        c π ρ q hc hπ hρ).2
        ⟨rfl, hcZero, hgradZero⟩

/-- Exact repaired-clause/BKM-data boundary for the full affine-plus-localized
Schwartz pressure class over the cancelled equal-amplitude anti-profile branch.
The repaired finite-energy BKM clause contributes no pressure information at
the zero datum, so the combined clause-and-data package is classified by the
same collapsed affine-plus-localized pressure conditions as BKM data itself. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_zero_and_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  constructor
  · rintro ⟨_hClause, hData⟩
    exact
      (BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        (ν := ν) (T := T) a c π ρ f q hc hπ hρ).1 hData
  · intro hPressure
    exact
      ⟨ExplicitFiniteEnergyBKMContinuationClause_zero ν T,
        (BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
          (ν := ν) (T := T) a c π ρ f q hc hπ hρ).2 hPressure⟩

/-- Exact repaired-clause/BKM-data boundary for the syntactic anti-profile
initial datum and the full affine-plus-localized Schwartz pressure class.  The
initial slice cancels to zero, so the paired repaired clause and matching
BKM-data package exists exactly under the same collapsed pressure conditions. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  constructor
  · rintro ⟨_hClause, hData⟩
    exact
      (BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        (ν := ν) (T := T) a c π ρ f q hc hπ hρ).1 hData
  · intro hPressure
    exact
      ⟨by
          simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
            (ExplicitFiniteEnergyBKMContinuationClause_zero ν T),
        (BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
          (ν := ν) (T := T) a c π ρ f q hc hπ hρ).2 hPressure⟩

/-- Negative form of the full affine-plus-localized anti-profile BKM
classification.  A nonzero affine spatial coefficient on the certified slab,
or an active localized pressure amplitude paired with a nonzero fixed Schwartz
pressure gradient, rules out BKM data for the cancelled two-mode branch. -/
theorem not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  intro hData
  rcases
      (BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        a c π ρ f q hc hπ hρ).1 hData with
    ⟨hcZero, hgradZeroOfActive⟩
  rcases hbad with ⟨t, ht0, htT, hct⟩ | ⟨hactive, s, x, hgrad⟩
  · exact hct (hcZero t ht0 htT)
  · exact hgrad (hgradZeroOfActive hactive s x)

/-- Negative form over the syntactic anti-profile initial datum.  This is the
same obstruction as the zero-datum BKM-data no-go, but phrased on the exact
witness type a repaired finite-mode route would try to cite. -/
theorem not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  intro hData
  rcases
      (BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        a c π ρ f q hc hπ hρ).1 hData with
    ⟨hcZero, hgradZeroOfActive⟩
  rcases hbad with ⟨t, ht0, htT, hct⟩ | ⟨hactive, s, x, hgrad⟩
  · exact hct (hcZero t ht0 htT)
  · exact hgrad (hgradZeroOfActive hactive s x)

/-- Clause-level separation for the repaired BKM surface.  Even when the bare
finite-energy BKM continuation clause is inhabited at the zero datum, a bad
affine-plus-localized pressure still cannot be packaged as structured BKM data
for the equal-amplitude anti-profile branch. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_zero_and_not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ⟨ExplicitFiniteEnergyBKMContinuationClause_zero ν T,
      not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
        a c π ρ f q hc hπ hρ hbad⟩

/-- Same data-level separation, phrased over the syntactic anti-profile initial
datum.  The repaired BKM clause may be inhabited for the cancelled finite-mode
initial datum, but the matching structured BKM-data package with a bad
affine-plus-localized pressure is still impossible. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  constructor
  · simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
      (ExplicitFiniteEnergyBKMContinuationClause_zero ν T)
  · intro hData
    exact
      not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
        a c π ρ f q hc hπ hρ hbad hData

/-- Constructor-input separation for the repaired finite-mode BKM clause.  The
generic clause theorem may still inhabit the cancelled initial datum, but the
full pointwise momentum equation needed to use the proposed anti-profile
velocity and bad affine-plus-localized pressure is impossible. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_or_active_schwartzPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hbad :
      (∃ t, c t ≠ 0) ∨
        ((∃ t, ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  constructor
  · simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
      (ExplicitFiniteEnergyBKMContinuationClause_zero ν T)
  · intro heq
    rcases
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zero_and_schwartzPressureGradient_zero_if_nonzeroAmplitude
          a ν c π ρ f q).1 heq with
      ⟨hcZero, hgradZeroOfActive⟩
    rcases hbad with ⟨t, hct⟩ | ⟨hactive, s, x, hgrad⟩
    · exact hct (hcZero t)
    · exact hgrad (hgradZeroOfActive hactive s x)
end NavierStokes
end FluidDynamics
end Mettapedia
