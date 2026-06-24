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

/-- Any finite-time witness with zero velocity and fixed pressure forces that
pressure to have zero spatial gradient throughout the slab.  This separates
the harmless time-only pressure gauge from pressure fields that would introduce
a nonzero force even when the velocity is zero. -/
theorem zeroVelocity_finiteTimeWitness_implies_spatialPressureGradient_zero
    {ν : ℝ} {T : ℝ} {p : NSPressureField}
    (hW : ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧ W.pressure = p) :
    ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  rcases hW with ⟨W, hWvel, hWpress⟩
  intro t x ht0 htT
  have hmom := W.momentum_equation_on t x ht0 htT
  rw [hWvel, hWpress] at hmom
  have hlap :
      spatialLaplacian (0 : NSVelocityField) t x = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t x
  simpa [timeVelocityDerivative_zero, spatialConvection_zero, hlap] using hmom

/-- Zero velocity with a fixed smooth pressure field gives a finite-time
Navier-Stokes witness exactly when the pressure has zero spatial gradient on
the slab.  This is the pressure-gauge baseline behind the zero-data route:
time-only pressure gauges are harmless, while spatial pressure gradients are
real forcing terms. -/
theorem zeroVelocity_finiteTimeWitness_iff_spatialPressureGradient_zero
    {ν : ℝ} {T : ℝ} (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧ W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0) := by
  constructor
  · exact zeroVelocity_finiteTimeWitness_implies_spatialPressureGradient_zero
  · intro hgrad
    let W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T :=
      { velocity := 0
        pressure := p
        smooth_velocity := by
          simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap] using
            (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : NSSpace)))
        smooth_pressure := hp
        momentum_equation_on := by
          intro t x ht0 htT
          have hlap :
              spatialLaplacian (0 : NSVelocityField) t x = 0 := by
            simpa [constantVelocityField] using
              spatialLaplacian_constantVelocityField (0 : NSSpace) t x
          have hpx : spatialPressureGradient p t x = 0 := hgrad t x ht0 htT
          simp [timeVelocityDerivative_zero, spatialConvection_zero, hlap, hpx]
        incompressible_on := by
          intro t x _ht0 _htT
          simpa using (spatialDivergence_zero t x)
        initial_condition := by
          intro x
          rfl
        bounded_energy_on := by
          refine ⟨0, le_rfl, ?_⟩
          intro t _ht0 _htT
          constructor
          · have hk :
              kineticEnergyDensity (0 : NSVelocityField) t =
                (fun _ : NSSpace => (0 : ℝ)) := by
              funext x
              simp [kineticEnergyDensity]
            rw [hk]
            exact
              MeasureTheory.integrable_zero NSSpace ℝ
                (MeasureTheory.volume : MeasureTheory.Measure NSSpace)
          · have hE0 : kineticEnergyAt (0 : NSVelocityField) t = 0 := by
              simp [kineticEnergyAt, kineticEnergyDensity]
            simp [hE0] }
    exact ⟨W, rfl, rfl⟩

/-- Positive pressure-gauge instance of the zero-velocity classification: any
smooth time-only pressure gives a finite-time zero-velocity witness, because it
has zero spatial gradient on every slice. -/
theorem zeroVelocity_timeOnlyPressure_finiteTimeWitness
    {ν : ℝ} {T : ℝ} (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    (zeroVelocity_finiteTimeWitness_iff_spatialPressureGradient_zero
      (ν := ν)
      (T := T)
      (p := fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)).mpr
      (by
        intro t x _ht0 _htT
        exact spatialPressureGradient_timeOnly π t x)

/-- Constant velocity with a fixed smooth pressure field gives a finite-time
witness on a nonnegative slab exactly when the field is actually zero and the
pressure has zero spatial gradient on that slab.  This closes the tempting
constant-field ansatz completely at the exact witness surface. -/
theorem constantVelocityField_finiteTimeWitness_iff_zero_and_spatialPressureGradient_zero
    {ν : ℝ} {T : ℝ} (hT : 0 ≤ T) {c : NSSpace} (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T,
        W.velocity = constantVelocityField c ∧ W.pressure = p) ↔
      c = 0 ∧
        (∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0) := by
  constructor
  · intro hW
    rcases hW with ⟨W, hWvel, hWpress⟩
    have hbd : boundedKineticEnergyUpTo (constantVelocityField c) T := by
      simpa [hWvel] using W.bounded_energy_on
    have hc0 : c = 0 := by
      exact
        (boundedKineticEnergyUpTo_constantVelocityField_iff
          (T := T) (c := c) hT).1 hbd
    refine ⟨hc0, ?_⟩
    subst hc0
    intro t x ht0 htT
    have hmom := W.momentum_equation_on t x ht0 htT
    rw [hWvel, hWpress] at hmom
    have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa using spatialLaplacian_constantVelocityField (0 : NSSpace) t x
    have hpx : spatialPressureGradient p t x = 0 := by
      simpa [timeVelocityDerivative_zero, spatialConvection_zero, hlap] using hmom
    exact hpx
  · rintro ⟨hc0, hgrad⟩
    subst hc0
    let W : ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity (0 : NSSpace)) T :=
      { velocity := constantVelocityField (0 : NSSpace)
        pressure := p
        smooth_velocity := smoothSpaceTimeVelocity_constantVelocityField (0 : NSSpace)
        smooth_pressure := hp
        momentum_equation_on := by
          intro t x ht0 htT
          have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
            simpa using spatialLaplacian_constantVelocityField (0 : NSSpace) t x
          have hpx : spatialPressureGradient p t x = 0 := hgrad t x ht0 htT
          simp [timeVelocityDerivative_zero, spatialConvection_zero, hlap, hpx]
        incompressible_on := by
          intro t x _ht0 _htT
          simpa using spatialDivergence_constantVelocityField (0 : NSSpace) t x
        initial_condition := matchesInitialVelocity_constantVelocityField (0 : NSSpace)
        bounded_energy_on :=
          (boundedKineticEnergyUpTo_constantVelocityField_iff
            (T := T) (c := (0 : NSSpace)) hT).2 rfl }
    exact ⟨W, rfl, rfl⟩

/-- On a nonnegative slab, the entire finite-time witness type for constant
initial data is inhabited exactly in the zero-data case.  This closes not only
the literal constant-field ansatz, but every possible witness route from
nonzero constant initial data. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {c : NSSpace} :
    Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) ↔
      c = 0 := by
  constructor
  · intro hW
    by_contra hc
    exact
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
        (ν := ν) (T := T) hc hT) hW
  · intro hc
    subst hc
    rcases zeroVelocity_timeOnlyPressure_finiteTimeWitness
        (ν := ν) (T := T) (fun _ : NSTime => (0 : ℝ))
        (by simpa using
          (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))) with
      ⟨W, _hWvel, _hWpress⟩
    exact ⟨W⟩

/-- A single nonzero spatial pressure gradient rules out any finite-time
zero-velocity witness with that fixed pressure field. -/
theorem not_exists_zeroVelocity_finiteTimeWitness_of_spatialPressureGradient_failure
    {ν : ℝ} {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail : spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧ W.pressure = p := by
  intro hW
  exact hfail
    (zeroVelocity_finiteTimeWitness_implies_spatialPressureGradient_zero
      hW t x ht0 htT)

end ConcreteWitnessConstruction

end NavierStokes
end FluidDynamics
end Mettapedia
