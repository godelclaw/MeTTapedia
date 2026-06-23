import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionZero

/-!
# Concrete Navier-Stokes Witness Construction

This file keeps the witness-construction surface honest.  It records the
direct zero-data global witness, and it classifies the boxed steady seed route:
the seed becomes a finite-time witness exactly when the stationary momentum
balance is supplied on the slab.  Thus the boxed seed is not a local existence
theorem for general data; the missing step is an evolved solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff

section ConcreteWitnessConstruction

/-- For a finite-energy smooth divergence-free initial datum, the
time-independent seed supplies every finite-time witness field except the
momentum equation and the pressure.  This isolates the exact analytic work
needed before a compatibility seed can be upgraded to a local solution. -/
theorem timeIndependentVelocity_nonMomentumFiniteTimeFields
    {u₀ : NSInitialVelocity} (T : ℝ)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (henergy : finiteInitialKineticEnergy u₀) :
    smoothSpaceTimeVelocity (timeIndependentVelocity u₀) ∧
      (∀ t x, spatialDivergence (timeIndependentVelocity u₀) t x = 0) ∧
      (∀ t x, timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0) ∧
      MatchesInitialVelocity u₀ (timeIndependentVelocity u₀) ∧
      boundedKineticEnergyUpTo (timeIndependentVelocity u₀) T := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_timeIndependentVelocity hsmooth
  · intro t x
    calc
      spatialDivergence (timeIndependentVelocity u₀) t x =
          initialSpatialDivergence u₀ x := by
            exact spatialDivergence_timeIndependentVelocity u₀ t x
      _ = 0 := hdiv x
  · exact timeVelocityDerivative_timeIndependentVelocity u₀
  · exact MatchesInitialVelocity_timeIndependentVelocity u₀
  · exact boundedKineticEnergyUpTo_timeIndependentVelocity henergy

/-- A time-independent seed gives a finite-time Navier-Stokes witness with a
fixed pressure field exactly when that seed and pressure satisfy the stationary
momentum balance throughout the slab.  This is the general version of the boxed
steady-seed obstruction: compatibility data are not local existence data unless
the momentum equation is also supplied. -/
theorem timeIndependentVelocity_finiteTimeWitness_iff_stationaryMomentum
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (T : ℝ) (p : NSPressureField)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (henergy : finiteInitialKineticEnergy u₀)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (timeIndependentVelocity u₀) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (timeIndependentVelocity u₀) t x) := by
  constructor
  · rintro ⟨W, hWvel, hWpress⟩ t x ht0 htT
    have hmom := W.momentum_equation_on t x ht0 htT
    rw [hWvel, hWpress] at hmom
    have htime :
        timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0 := by
      exact timeVelocityDerivative_timeIndependentVelocity u₀ t x
    simpa [htime] using hmom
  · intro hstationary
    rcases timeIndependentVelocity_nonMomentumFiniteTimeFields
        (u₀ := u₀) T hsmooth hdiv henergy with
      ⟨hvel, hinc, htime, hinit, hbd⟩
    let W : ExplicitFiniteTimeRegularityWitness ν u₀ T :=
      { velocity := timeIndependentVelocity u₀
        pressure := p
        smooth_velocity := hvel
        smooth_pressure := hp
        momentum_equation_on := by
          intro t x ht0 htT
          simpa [htime t x] using hstationary t x ht0 htT
        incompressible_on := by
          intro t x _ht0 _htT
          exact hinc t x
        initial_condition := hinit
        bounded_energy_on := hbd }
    exact ⟨W, rfl, rfl⟩

/-- On a nonnegative slab, a time-independent seed with fixed pressure gives a
finite-time witness exactly when the datum has finite kinetic energy and the
stationary momentum balance holds.  This folds the previously external
bounded-energy side condition into the witness-existence statement itself. -/
theorem timeIndependentVelocity_finiteTimeWitness_iff_finiteInitialKineticEnergy_and_stationaryMomentum
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) (p : NSPressureField)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) ↔
      finiteInitialKineticEnergy u₀ ∧
        (∀ t x, 0 ≤ t → t ≤ T →
          spatialConvection (timeIndependentVelocity u₀) t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian (timeIndependentVelocity u₀) t x) := by
  constructor
  · intro hW
    refine ⟨?_, ?_⟩
    · rcases hW with ⟨W, hWvel, hWpress⟩
      exact W.finiteInitialKineticEnergy hT
    · rcases hW with ⟨W, hWvel, hWpress⟩
      intro t x ht0 htT
      have hmom := W.momentum_equation_on t x ht0 htT
      rw [hWvel, hWpress] at hmom
      have htime :
          timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0 := by
        exact timeVelocityDerivative_timeIndependentVelocity u₀ t x
      simpa [htime] using hmom
  · rintro ⟨henergy, hstationary⟩
    exact
      (timeIndependentVelocity_finiteTimeWitness_iff_stationaryMomentum
        T p hsmooth hdiv henergy hp).2 hstationary

/-- Any finite-time witness whose velocity is a time-independent seed and
whose pressure is the fixed pressure field forces the stationary momentum
balance on the whole slab.  This is the forward audit direction separated from
the construction-side hypotheses of the iff theorem. -/
theorem timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    (hW : ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) :
    ∀ t x, 0 ≤ t → t ≤ T →
      spatialConvection (timeIndependentVelocity u₀) t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian (timeIndependentVelocity u₀) t x := by
  rcases hW with ⟨W, hWvel, hWpress⟩
  intro t x ht0 htT
  have hmom := W.momentum_equation_on t x ht0 htT
  rw [hWvel, hWpress] at hmom
  have htime :
      timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0 := by
    exact timeVelocityDerivative_timeIndependentVelocity u₀ t x
  simpa [htime] using hmom

/-- Time-zero form of the exact time-independent seed audit.  On a nonnegative
slab, exact finite-time use of a time-independent seed must already solve the
stationary momentum balance at the initial slice. -/
theorem timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum_zero_time
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    (hT : 0 ≤ T)
    (hW : ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) :
    ∀ x,
      spatialConvection (timeIndependentVelocity u₀) 0 x +
          spatialPressureGradient p 0 x =
        ν • spatialLaplacian (timeIndependentVelocity u₀) 0 x := by
  intro x
  exact
    timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum
      hW 0 x le_rfl hT

/-- A single failed stationary momentum equation at one point of the slab rules
out any finite-time witness whose velocity is the corresponding
time-independent seed and whose pressure is the fixed pressure field.  Unlike
the iff theorem above, this negative audit does not need smoothness or
finite-energy hypotheses: those would be carried by the putative witness
itself. -/
theorem not_exists_timeIndependentVelocity_finiteTimeWitness_of_stationaryMomentum_failure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (timeIndependentVelocity u₀) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (timeIndependentVelocity u₀) t x) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p := by
  intro hW
  exact hfail
    (timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum
      hW t x ht0 htT)

end ConcreteWitnessConstruction

end NavierStokes
end FluidDynamics
end Mettapedia
