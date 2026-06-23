import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessCore

/-!
# Streamwise Drift Heat-Shear Exactness

This module contains the streamwise constant-drift heat-shear exactness and obstruction surfaces.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The damped sinusoidal heat-shear field with constant streamwise drift is
likewise an honest exact candidate on the global explicit theorem surface; the
only missing slot is bounded kinetic energy on `ℝ^3`. -/
theorem heatShearStreamwiseDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k d : ℝ} (hd : d ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨heatShearStreamwiseDriftVelocityField ν a k d, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simpa using momentumEquation_heatShearStreamwiseDriftVelocityField_zeroPressure ν a k d t x
  · intro t x
    simpa using spatialDivergence_heatShearStreamwiseDriftVelocityField ν a k d t x
  · exact matchesInitialVelocity_heatShearStreamwiseDriftVelocityField ν a k d
  · exact not_boundedKineticEnergy_heatShearStreamwiseDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) hd

/-- Heat shear with constant streamwise drift therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem heatShearStreamwiseDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k d : ℝ} (hd : d ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact heatShearStreamwiseDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) (d := d) hd
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
        (u := u) hd hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
heat-shear initial data with nonzero constant streamwise drift. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearStreamwiseDriftInitialVelocity
    {ν : ℝ} {a k d : ℝ}
    (hd : d ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν
      (heatShearStreamwiseDriftInitialVelocity a k d) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
      (u := u) hd hinit hbd

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for heat-shear initial data with nonzero constant streamwise
drift on `ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
    {ν : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (heatShearStreamwiseDriftInitialVelocity a k d) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearStreamwiseDriftInitialVelocity a k d) :=
    smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d
  have hdiv : ∀ x, initialSpatialDivergence (heatShearStreamwiseDriftInitialVelocity a k d) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity a k d x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearStreamwiseDriftInitialVelocity hd
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- The same witness-level obstruction applies to the heat-shear datum with
nonzero constant streamwise drift on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity
    {ν T : ℝ} {a k d : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (heatShearStreamwiseDriftInitialVelocity a k d) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity hd)
      hT

/-- On every nonnegative slab with nonnegative viscosity, the heat-shear field
with constant streamwise drift is an exact smooth incompressible candidate with
explicit slab vorticity bound `|a * k|`; bounded kinetic energy is the only
missing witness slot. -/
theorem heatShearStreamwiseDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a k d : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨heatShearStreamwiseDriftVelocityField ν a k d, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simpa using momentumEquation_heatShearStreamwiseDriftVelocityField_zeroPressure ν a k d t x
  · intro t x ht0 htT
    simpa using spatialDivergence_heatShearStreamwiseDriftVelocityField ν a k d t x
  · exact matchesInitialVelocity_heatShearStreamwiseDriftVelocityField ν a k d
  · exact uniformVorticityBoundUpTo_heatShearStreamwiseDriftVelocityField ν a k d T hν
  · exact not_boundedKineticEnergyUpTo_heatShearStreamwiseDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) hd hT

/-- Heat shear with constant streamwise drift exposes the same exact gap on the
explicit uniform-vorticity surface: there is an exact smooth incompressible
candidate with a uniform slab vorticity bound, but the finite-time witness
type is still empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearStreamwiseDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a k d : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearStreamwiseDriftInitialVelocity a k d) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearStreamwiseDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT

/-- The repaired explicit regularity clause is likewise vacuous on heat-shear
data with nonzero constant streamwise drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
    {ν : ℝ} {a k d : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity hd)

/-- The repaired explicit regularity clause can therefore also be true on
heat-shear data with nonzero constant streamwise drift while the unrepaired
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
    {ν : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (a := a) (k := k) (d := d) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      hν hd

/-- The structured fully concrete clause also rejects heat-shear initial data
with nonzero constant streamwise drift. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearStreamwiseDriftInitialVelocity
    {ν : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearStreamwiseDriftInitialVelocity a k d
          smooth_initial := smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity a k d x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearStreamwiseDriftInitialVelocity hd
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
        hν
        (smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity a k d x)).mp hClause)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for heat-shear initial data with nonzero constant streamwise drift
because the finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity
    {ν T : ℝ} {a k d : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (heatShearStreamwiseDriftInitialVelocity a k d) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
heat-shear data with nonzero constant streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      hν hd

/-- The repaired uniform-vorticity continuation clause is also vacuous on
heat-shear data with nonzero constant streamwise drift because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity
    {ν T : ℝ} {a k d : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearStreamwiseDriftInitialVelocity a k d) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity hd)

/-- The repaired uniform-vorticity clause can therefore also be true on
heat-shear data with nonzero constant streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      hν hd


end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
