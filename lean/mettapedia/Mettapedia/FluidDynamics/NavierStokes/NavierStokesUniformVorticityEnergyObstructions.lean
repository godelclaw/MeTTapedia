import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationSurface

/-!
# Uniform-Vorticity Finite-Energy Obstructions

This module contains the generic finite-energy consequences of bounded
kinetic energy and the constant-field obstruction family for the concrete
uniform-vorticity continuation surface.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- A global bounded-energy witness immediately restricts to a bounded-energy
witness on every finite time slab. -/
theorem boundedKineticEnergy_implies_boundedKineticEnergyUpTo
    {u : NSVelocityField} {T : ℝ}
    (h : boundedKineticEnergy u) :
    boundedKineticEnergyUpTo u T := by
  rcases h with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht0 htT
  exact hbound t

/-- Matching the initial condition identifies the explicit initial kinetic
energy density with the time-zero kinetic-energy density of the space-time
field. -/
theorem initialKineticEnergyDensity_eq_of_matchesInitialVelocity
    {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hinit : MatchesInitialVelocity u₀ u) :
    initialKineticEnergyDensity u₀ = kineticEnergyDensity u 0 := by
  funext x
  simp [initialKineticEnergyDensity, kineticEnergyDensity, hinit x]

/-- On a nonnegative slab, any bounded-energy witness already forces finite
initial kinetic energy for the prescribed datum. -/
theorem finiteInitialKineticEnergy_of_matchesInitialVelocity_of_boundedKineticEnergyUpTo
    {u₀ : NSInitialVelocity} {u : NSVelocityField} {T : ℝ}
    (hinit : MatchesInitialVelocity u₀ u)
    (hE : boundedKineticEnergyUpTo u T)
    (hT : 0 ≤ T) :
    finiteInitialKineticEnergy u₀ := by
  rcases hE with ⟨C, hC, hbound⟩
  have hInt0 : MeasureTheory.Integrable (kineticEnergyDensity u 0) := (hbound 0 le_rfl hT).1
  rw [finiteInitialKineticEnergy, initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit]
  exact hInt0

/-- The global bounded-energy predicate also forces finite initial kinetic
energy for the prescribed datum. -/
theorem finiteInitialKineticEnergy_of_matchesInitialVelocity_of_boundedKineticEnergy
    {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hinit : MatchesInitialVelocity u₀ u)
    (hE : boundedKineticEnergy u) :
    finiteInitialKineticEnergy u₀ := by
  rcases hE with ⟨C, hC, hbound⟩
  have hInt0 : MeasureTheory.Integrable (kineticEnergyDensity u 0) := (hbound 0).1
  rw [finiteInitialKineticEnergy, initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit]
  exact hInt0

/-- Contrapositively, non-finite-energy initial data rule out the slab
bounded-energy slot for every matched velocity field on a nonnegative slab. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_of_not_finiteInitialKineticEnergy
    {u₀ : NSInitialVelocity} {u : NSVelocityField} {T : ℝ}
    (hfinite : ¬ finiteInitialKineticEnergy u₀)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity u₀ u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  exact hfinite
    (finiteInitialKineticEnergy_of_matchesInitialVelocity_of_boundedKineticEnergyUpTo
      hinit hE hT)

/-- The same contrapositive obstruction rules out the global bounded-energy
predicate for every matched velocity field. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_of_not_finiteInitialKineticEnergy
    {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hfinite : ¬ finiteInitialKineticEnergy u₀)
    (hinit : MatchesInitialVelocity u₀ u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  exact hfinite
    (finiteInitialKineticEnergy_of_matchesInitialVelocity_of_boundedKineticEnergy
      hinit hE)

/-- Therefore every explicit finite-time regularity witness on a nonnegative
slab carries finite initial kinetic energy. -/
theorem ExplicitFiniteTimeRegularityWitness.finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hT : 0 ≤ T) :
    finiteInitialKineticEnergy u₀ := by
  exact
    finiteInitialKineticEnergy_of_matchesInitialVelocity_of_boundedKineticEnergyUpTo
      W.initial_condition W.bounded_energy_on hT

/-- Conversely, if the initial datum fails the finite-energy input condition,
then the explicit finite-time witness type is empty on every nonnegative slab.
-/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hfinite : ¬ finiteInitialKineticEnergy u₀)
    (hT : 0 ≤ T) :
    ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν u₀ T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact hfinite (W.finiteInitialKineticEnergy hT)

/-- If the time-zero kinetic-energy density of a space-time field is not
integrable on `ℝ^3`, then no nonnegative slab can satisfy the bounded-energy
slot. -/
theorem not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
    {u : NSVelocityField} {T : ℝ}
    (hzero : ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0))
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact hzero ((hbound 0 le_rfl hT).1)

/-- The same time-zero nonintegrability obstruction rules out the global
bounded-energy predicate. -/
theorem not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
    {u : NSVelocityField}
    (hzero : ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0)) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact hzero ((hbound 0).1)

/-- Kinetic-energy density of a constant velocity field is a positive constant
function on space. -/
theorem kineticEnergyDensity_constantVelocityField
    (c : NSSpace) (t : NSTime) :
    kineticEnergyDensity (constantVelocityField c) t = fun _ : NSSpace => ‖c‖ ^ (2 : ℕ) := by
  funext x
  simp [kineticEnergyDensity, constantVelocityField]

/-- A nonzero constant velocity field is not spatially integrable on `ℝ^3`
with respect to the kinetic-energy density. -/
theorem not_integrable_kineticEnergyDensity_constantVelocityField
    {c : NSSpace} (hc : c ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity (constantVelocityField c) t) := by
  have hconst : (‖c‖ ^ (2 : ℕ) : ℝ) ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  have hnotfinite :
      ¬ MeasureTheory.IsFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    rw [MeasureTheory.not_isFiniteMeasure_iff]
    exact MeasureTheory.measure_univ_of_isAddLeftInvariant
      (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
  intro hInt
  have hfinite :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    rw [kineticEnergyDensity_constantVelocityField c t] at hInt
    exact (MeasureTheory.integrable_const_iff_isFiniteMeasure hconst).mp hInt
  exact hnotfinite hfinite

/-- Therefore a nonzero constant velocity field never satisfies the concrete
global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_constantVelocityField
    {c : NSSpace} (hc : c ≠ 0) :
    ¬ boundedKineticEnergy (constantVelocityField c) := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := constantVelocityField c)
      (not_integrable_kineticEnergyDensity_constantVelocityField hc 0)

/-- On every nonnegative slab, a nonzero constant velocity field also fails the
finite-time bounded-energy predicate.  This records the honest obstruction that
blocks the tempting constant-field witness ansatz on `ℝ^3`. -/
theorem not_boundedKineticEnergyUpTo_constantVelocityField
    {c : NSSpace} {T : ℝ}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (constantVelocityField c) T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := constantVelocityField c)
      (not_integrable_kineticEnergyDensity_constantVelocityField hc 0)
      hT

/-- If a velocity field matches nonzero constant initial data at time `0`, then
its initial kinetic-energy density agrees with the constant-field one. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_constantInitialVelocity
    {u : NSVelocityField} {c : NSSpace}
    (hinit : MatchesInitialVelocity (constantInitialVelocity c) u) :
    kineticEnergyDensity u 0 = kineticEnergyDensity (constantVelocityField c) 0 := by
  funext x
  simp [kineticEnergyDensity, constantVelocityField, constantInitialVelocity, hinit x]

/-- Therefore any velocity field matching nonzero constant initial data already
fails the integrability requirement at time `0`. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_constantInitialVelocity
    {u : NSVelocityField} {c : NSSpace}
    (hc : c ≠ 0)
    (hinit : MatchesInitialVelocity (constantInitialVelocity c) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntConst :
      MeasureTheory.Integrable (kineticEnergyDensity (constantVelocityField c) 0) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_constantInitialVelocity hinit] using hInt
  exact not_integrable_kineticEnergyDensity_constantVelocityField hc 0 hIntConst

/-- Hence any nonnegative finite-time slab witness with nonzero constant initial
data is blocked by the bounded-energy slot, regardless of later dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_constantInitialVelocity
    {u : NSVelocityField} {c : NSSpace} {T : ℝ}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (constantInitialVelocity c) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_constantInitialVelocity
        hc hinit)
      hT

/-- The same obstruction rules out the global bounded-energy predicate for any
velocity field with nonzero constant initial data. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_constantInitialVelocity
    {u : NSVelocityField} {c : NSSpace}
    (hc : c ≠ 0)
    (hinit : MatchesInitialVelocity (constantInitialVelocity c) u) :
    ¬ boundedKineticEnergy u := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_constantInitialVelocity
        hc hinit)

/-- Nonzero constant initial data are therefore not finite-energy admissible on
`ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_constantInitialVelocity
    {c : NSSpace}
    (hc : c ≠ 0) :
    ¬ finiteInitialKineticEnergy (constantInitialVelocity c) := by
  intro hE
  have hIntConst :
      MeasureTheory.Integrable (kineticEnergyDensity (constantVelocityField c) 0) := by
    simpa [finiteInitialKineticEnergy, initialKineticEnergyDensity,
      constantVelocityField, constantInitialVelocity] using hE
  exact not_integrable_kineticEnergyDensity_constantVelocityField hc 0 hIntConst

/-- Constant initial data have finite whole-space kinetic energy exactly in the
zero-data case. -/
theorem finiteInitialKineticEnergy_constantInitialVelocity_iff
    {c : NSSpace} :
    finiteInitialKineticEnergy (constantInitialVelocity c) ↔ c = 0 := by
  constructor
  · intro hE
    by_contra hc
    exact not_finiteInitialKineticEnergy_constantInitialVelocity hc hE
  · intro hc
    subst hc
    have hzeroDensity :
        initialKineticEnergyDensity (constantInitialVelocity (0 : NSSpace)) =
          (fun _ : NSSpace => (0 : ℝ)) := by
      funext x
      simp [initialKineticEnergyDensity, constantInitialVelocity]
    rw [finiteInitialKineticEnergy, hzeroDensity]
    exact
      MeasureTheory.integrable_zero NSSpace ℝ
        (MeasureTheory.volume : MeasureTheory.Measure NSSpace)

/-- Therefore the repaired structured whole-space input domain contains no
problem datum whose initial velocity is a nonzero constant field. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_constantInitialVelocity
    {c : NSSpace}
    (hc : c ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = constantInitialVelocity c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := constantInitialVelocity c)
      (not_finiteInitialKineticEnergy_constantInitialVelocity hc)

/-- Therefore the explicit finite-time witness type is uninhabited on any
nonnegative slab for nonzero constant initial data. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_constantInitialVelocity
      (u := W.velocity) hc hT W.initial_condition W.bounded_energy_on


end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
