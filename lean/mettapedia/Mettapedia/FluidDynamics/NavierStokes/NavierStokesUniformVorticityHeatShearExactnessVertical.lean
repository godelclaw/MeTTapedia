import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessCore

/-!
# Vertical Drift Heat-Shear Exactness

This module contains the vertical constant-drift heat-shear exactness and obstruction surfaces.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The damped sinusoidal heat-shear field with constant vertical drift is
likewise an honest exact candidate on the global explicit theorem surface; the
only missing slot is bounded kinetic energy on `ℝ^3`. -/
theorem heatShearVerticalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k c : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨heatShearVerticalDriftVelocityField ν a k c, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearVerticalDriftVelocityField ν a k c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simpa using momentumEquation_heatShearVerticalDriftVelocityField_zeroPressure ν a k c t x
  · intro t x
    simpa using spatialDivergence_heatShearVerticalDriftVelocityField ν a k c t x
  · exact matchesInitialVelocity_heatShearVerticalDriftVelocityField ν a k c
  · exact not_boundedKineticEnergy_heatShearVerticalDriftVelocityField
      (ν := ν) (a := a) (k := k) (c := c) ha hk

/-- Heat shear with constant vertical drift therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem heatShearVerticalDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k c : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVerticalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) (c := c) ha hk
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
        (u := u) ha hk hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
nontrivial heat-shear initial data with vertical drift. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity
    {ν : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν
      (heatShearVerticalDriftInitialVelocity a k c) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
      (u := u) ha hk hinit hbd

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for nontrivial heat-shear initial data with vertical drift on
`ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
    {ν : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (heatShearVerticalDriftInitialVelocity a k c) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearVerticalDriftInitialVelocity a k c) :=
    smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity a k c
  have hdiv : ∀ x, initialSpatialDivergence (heatShearVerticalDriftInitialVelocity a k c) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity a k c x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity ha hk
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- The same witness-level obstruction applies to the nontrivial heat-shear
datum with vertical drift on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (heatShearVerticalDriftInitialVelocity a k c) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity ha hk)
      hT

/-- On every nonnegative slab with nonnegative viscosity, the heat-shear field
with constant vertical drift is an exact smooth incompressible candidate with
explicit slab vorticity bound `|a * k|`; bounded kinetic energy is the only
missing witness slot. -/
theorem heatShearVerticalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T -> spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨heatShearVerticalDriftVelocityField ν a k c, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearVerticalDriftVelocityField ν a k c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simpa using momentumEquation_heatShearVerticalDriftVelocityField_zeroPressure ν a k c t x
  · intro t x ht0 htT
    simpa using spatialDivergence_heatShearVerticalDriftVelocityField ν a k c t x
  · exact matchesInitialVelocity_heatShearVerticalDriftVelocityField ν a k c
  · exact uniformVorticityBoundUpTo_heatShearVerticalDriftVelocityField ν a k c T hν
  · exact not_boundedKineticEnergyUpTo_heatShearVerticalDriftVelocityField
      (ν := ν) (a := a) (k := k) (c := c) ha hk hT

/-- Heat shear with constant vertical drift exposes the same exact gap on the
explicit uniform-vorticity surface: there is an exact smooth incompressible
candidate with a uniform slab vorticity bound, but the finite-time witness
type is still empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearVerticalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearVerticalDriftInitialVelocity a k c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVerticalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT

/-- The repaired explicit regularity clause is likewise vacuous on nontrivial
heat-shear data with vertical drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
    {ν : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearVerticalDriftInitialVelocity a k c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity ha hk)

/-- The repaired explicit regularity clause can therefore also be true on
nontrivial heat-shear data with vertical drift while the unrepaired concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity_without_regularity
    {ν : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (a := a) (k := k) (c := c) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      hν ha hk

/-- The structured fully concrete clause also rejects nontrivial heat-shear
initial data with vertical drift. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearVerticalDriftInitialVelocity
    {ν : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearVerticalDriftInitialVelocity a k c
          smooth_initial := smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity a k c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity a k c x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity ha hk
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearVerticalDriftInitialVelocity a k c)
        hν
        (smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity a k c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity a k c x)).mp hClause)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for nontrivial heat-shear initial data with vertical drift
because the finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (heatShearVerticalDriftInitialVelocity a k c) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
nontrivial heat-shear data with vertical drift while the concrete regularity
clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (heatShearVerticalDriftInitialVelocity a k c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      hν ha hk

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nontrivial heat-shear data with vertical drift because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearVerticalDriftInitialVelocity a k c) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity ha hk)

/-- The repaired uniform-vorticity clause can therefore also be true on
nontrivial heat-shear data with vertical drift while the concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearVerticalDriftInitialVelocity a k c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      hν ha hk

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
