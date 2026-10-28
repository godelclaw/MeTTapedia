import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionTimeIndependent

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

/-- For a fixed pressure field, the boxed steady seed gives a finite-time
witness with that exact velocity and pressure if and only if the stationary
momentum balance holds on the slab.  This is a classification theorem, not a
local-existence theorem: for general boxed data the balance is precisely the
hard missing equation. -/
theorem boxedPartialPeriodizationSteadySeed_finiteTimeWitness_iff_stationaryMomentum
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  let P := boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν
  have henergy : finiteInitialKineticEnergy P.initialVelocity := by
    simpa [P, boxedPartialPeriodizationNavierStokesProblemData,
      FiniteEnergyAdmissibleNavierStokesProblemData.toNavierStokesProblemData] using
      (boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData N L u₀ hν).finite_initial_energy
  simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using
    (timeIndependentVelocity_finiteTimeWitness_iff_stationaryMomentum
      (ν := ν)
      (u₀ := P.initialVelocity)
      (T := T)
      (p := p)
      P.smooth_initial
      P.divergence_free_initial
      henergy
      hp)

/-- Any smooth pressure gauge with zero spatial gradient leaves the boxed
steady-seed witness criterion unchanged: the exact finite-time witness
condition is still the zero-pressure stationary momentum balance on the slab. -/
theorem
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  constructor
  · intro hW t x ht0 htT
    have hstat :=
      (boxedPartialPeriodizationSteadySeed_finiteTimeWitness_iff_stationaryMomentum
        hν N L u₀ T p hp).1 hW t x ht0 htT
    simpa [hp_zero t x] using hstat
  · intro hstat
    refine
      (boxedPartialPeriodizationSteadySeed_finiteTimeWitness_iff_stationaryMomentum
        hν N L u₀ T p hp).2 ?_
    intro t x ht0 htT
    simpa [hp_zero t x] using hstat t x ht0 htT

/-- A smooth time-only pressure gauge does not change the boxed steady-seed
stationary audit: because its spatial gradient vanishes identically, the exact
finite-time witness condition is still the zero-pressure stationary momentum
balance on the slab. -/
theorem boxedPartialPeriodizationSteadySeed_timeOnlyPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t)) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  exact
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Boxed-periodization instance of the forward audit: if the steady boxed seed
is the exact finite-time witness velocity with fixed pressure, then the
stationary momentum balance holds on the whole slab. -/
theorem boxedPartialPeriodizationSteadySeed_finiteTimeWitness_implies_stationaryMomentum
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    (hW :
      ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) :
    ∀ t x, 0 ≤ t → t ≤ T →
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
  let P := boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν
  simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using
    (timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum
      (ν := ν)
      (u₀ := P.initialVelocity)
      (T := T)
      (p := p)
      (by simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using hW))

/-- Time-zero boxed-periodization audit: exact finite-time use of the steady
boxed seed on a nonnegative slab must solve the stationary momentum balance at
the initial slice. -/
theorem boxedPartialPeriodizationSteadySeed_finiteTimeWitness_implies_stationaryMomentum_zero_time
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    (hT : 0 ≤ T)
    (hW :
      ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) :
    ∀ x,
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) 0 x +
          spatialPressureGradient p 0 x =
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) 0 x := by
  intro x
  exact
    boxedPartialPeriodizationSteadySeed_finiteTimeWitness_implies_stationaryMomentum
      hν N L u₀ hW 0 x le_rfl hT

/-- Boxed-periodization instance of the pointwise stationary-residual audit:
if the steady boxed seed and fixed pressure fail the stationary momentum
equation anywhere on the slab, that exact seed cannot be the finite-time
witness. -/
theorem not_exists_boxedPartialPeriodizationSteadySeed_finiteTimeWitness_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p := by
  let P := boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν
  simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using
    (not_exists_timeIndependentVelocity_finiteTimeWitness_of_stationaryMomentum_failure
      (ν := ν)
      (u₀ := P.initialVelocity)
      (T := T)
      (p := p)
      (t := t)
      (x := x)
      ht0
      htT
      (by simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using hfail))

/-- A smooth zero-spatial-gradient pressure gauge cannot rescue a boxed steady
seed whose zero-pressure stationary residual already fails somewhere on the
slab. -/
theorem
    not_exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField} {t : NSTime} {x : NSSpace}
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p := by
  have hfail' :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
    simpa [hp_zero t x] using hfail
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_finiteTimeWitness_of_stationaryMomentum_failure
      hν N L u₀ ht0 htT
      (p := p)
      hfail'

/-- In particular, a smooth time-only pressure gauge cannot rescue a boxed
steady seed whose zero-pressure stationary residual already fails somewhere on
the slab. -/
theorem
    not_exists_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_finiteTimeWitness_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (π : NSTime → ℝ)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_of_stationaryMomentum_failure
      hν N L u₀
      (p := fun t : NSTime => fun _ : NSSpace => π t)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      ht0 htT hfail

/-- Candidate-level obstruction for the boxed-periodization steady seed with a
smooth time-only pressure gauge: all non-momentum finite-time witness fields are
available, but if the zero-pressure stationary residual fails anywhere on the
slab then that exact velocity/pressure pair cannot be an honest finite-time
witness. -/
theorem
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumFiniteTimeFields_without_exactWitness
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    (smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      smoothSpaceTimePressure (fun t : NSTime => fun _ : NSSpace => π t) ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      boundedKineticEnergyUpTo
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) T) ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
          W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
            W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) := by
  refine ⟨?_, ?_⟩
  · rcases boxedPartialPeriodizationSteadySeed_nonMomentumFiniteTimeFields hν N L u₀ T with
      ⟨hsmooth, _hzero, hdiv, hinit, henergy⟩
    exact ⟨hsmooth, smoothSpaceTimePressure_timeOnly hπ, hdiv, hinit, henergy⟩
  · exact
      not_exists_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_finiteTimeWitness_of_stationaryMomentum_failure
        hν N L u₀ π ht0 htT hfail


end ConcreteWitnessConstruction

end NavierStokes
end FluidDynamics
end Mettapedia
