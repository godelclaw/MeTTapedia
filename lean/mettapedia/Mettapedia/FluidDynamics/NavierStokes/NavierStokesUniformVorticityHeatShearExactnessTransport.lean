import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessStreamwise
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessVertical
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessFull

/-!
# Transported Heat-Shear Exactness for Uniform-Vorticity Continuation

This module contains the transported and transported-full-drift heat-shear
exactness surfaces.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The transported heat-shear field is likewise an honest exact candidate on
the global explicit theorem surface; with nonzero transport speed, bounded
kinetic energy is the only missing witness slot. -/
theorem heatShearTransportVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k b : ℝ} (hb : b ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨heatShearTransportVelocityField ν a k b, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simpa using momentumEquation_heatShearTransportVelocityField_zeroPressure ν a k b t x
  · intro t x
    simpa using spatialDivergence_heatShearTransportVelocityField ν a k b t x
  · exact matchesInitialVelocity_heatShearTransportVelocityField ν a k b
  · exact not_boundedKineticEnergy_heatShearTransportVelocityField
      (ν := ν) (a := a) (k := k) (b := b) hb

/-- Transported heat shear therefore exhibits the same exact mismatch on the
global explicit theorem surface: an honest smooth PDE-side candidate exists,
but the explicit global-output proposition is still false because bounded
kinetic energy fails. -/
theorem heatShearTransportInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k b : ℝ} (hb : b ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) (b := b) hb
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportInitialVelocity
        (u := u) hb hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
transported heat-shear initial data whenever the transport speed is nonzero. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportInitialVelocity
    {ν : ℝ} {a k b : ℝ}
    (hb : b ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν
      (heatShearTransportInitialVelocity a k b) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportInitialVelocity
      (u := u) hb hinit hbd

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for transported heat-shear initial data on `ℝ^3` whenever the
transport speed is nonzero. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
    {ν : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (heatShearTransportInitialVelocity a k b) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearTransportInitialVelocity a k b) :=
    smoothInitialVelocityData_heatShearTransportInitialVelocity a k b
  have hdiv : ∀ x, initialSpatialDivergence (heatShearTransportInitialVelocity a k b) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearTransportInitialVelocity a k b x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportInitialVelocity hb
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- The same witness-level obstruction applies to transported heat-shear data
on every nonnegative slab whenever the transport speed is nonzero. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity
    {ν T : ℝ} {a k b : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportInitialVelocity a k b) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity hb)
      hT

/-- On every nonnegative slab with nonnegative viscosity, the transported
heat-shear field is an exact smooth incompressible candidate with explicit slab
vorticity bound `|a * k|`; bounded kinetic energy is the only missing witness
slot. -/
theorem heatShearTransportVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a k b : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨heatShearTransportVelocityField ν a k b, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simpa using momentumEquation_heatShearTransportVelocityField_zeroPressure ν a k b t x
  · intro t x ht0 htT
    simpa using spatialDivergence_heatShearTransportVelocityField ν a k b t x
  · exact matchesInitialVelocity_heatShearTransportVelocityField ν a k b
  · exact uniformVorticityBoundUpTo_heatShearTransportVelocityField ν a k b T hν
  · exact not_boundedKineticEnergyUpTo_heatShearTransportVelocityField
      (ν := ν) (a := a) (k := k) (b := b) hb hT

/-- Transported heat shear exposes the same exact gap on the explicit
uniform-vorticity surface: there is an exact smooth incompressible candidate
with a uniform slab vorticity bound, but the finite-time witness type is still
empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearTransportInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a k b : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportInitialVelocity a k b) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT

/-- The repaired explicit regularity clause is likewise vacuous on transported
heat-shear data with nonzero transport speed because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportInitialVelocity
    {ν : ℝ} {a k b : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearTransportInitialVelocity a k b) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity hb)

/-- The repaired explicit regularity clause can therefore also be true on
transported heat-shear data with nonzero transport speed while the unrepaired
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportInitialVelocity_without_regularity
    {ν : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportInitialVelocity
      (ν := ν) (a := a) (k := k) (b := b) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
      hν hb

/-- The structured fully concrete clause also rejects transported heat-shear
initial data with nonzero transport speed. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearTransportInitialVelocity
    {ν : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportInitialVelocity a k b
          smooth_initial := smoothInitialVelocityData_heatShearTransportInitialVelocity a k b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportInitialVelocity a k b x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportInitialVelocity hb
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearTransportInitialVelocity a k b)
        hν
        (smoothInitialVelocityData_heatShearTransportInitialVelocity a k b)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearTransportInitialVelocity a k b x)).mp
        hClause)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for transported heat-shear initial data with nonzero transport
speed because the finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearTransportInitialVelocity
    {ν T : ℝ} {a k b : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (heatShearTransportInitialVelocity a k b) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
transported heat-shear data with nonzero transport speed while the concrete
regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearTransportInitialVelocity_without_regularity
    {ν T : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (heatShearTransportInitialVelocity a k b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
      hν hb

/-- The repaired uniform-vorticity continuation clause is also vacuous on
transported heat-shear data with nonzero transport speed because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportInitialVelocity
    {ν T : ℝ} {a k b : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearTransportInitialVelocity a k b) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity hb)

/-- The repaired uniform-vorticity clause can therefore also be true on
transported heat-shear data with nonzero transport speed while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportInitialVelocity_without_regularity
    {ν T : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearTransportInitialVelocity a k b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
      hν hb

/-- The transported full-drift heat-shear field is likewise an honest exact
candidate on the global explicit theorem surface; with nonzero transport
speed, bounded kinetic energy is the only missing witness slot. -/
theorem heatShearTransportFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k b d c : ℝ} (hb : b ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨heatShearTransportFullDriftVelocityField ν a k b d c, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearTransportFullDriftVelocityField ν a k b d c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simpa using momentumEquation_heatShearTransportFullDriftVelocityField_zeroPressure ν a k b d c t x
  · intro t x
    simpa using spatialDivergence_heatShearTransportFullDriftVelocityField ν a k b d c t x
  · exact matchesInitialVelocity_heatShearTransportFullDriftVelocityField ν a k b d c
  · exact not_boundedKineticEnergy_heatShearTransportFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb

/-- Transported full-drift heat shear therefore exposes the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem heatShearTransportFullDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k b d c : ℝ} (hb : b ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
        (u := u) hb hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
transported full-drift heat-shear initial data whenever the transport speed is
nonzero. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity
    {ν : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν
      (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
      (u := u) hb hinit hbd

/-- The fully explicit global-output surface is exact on the transported
full-drift heat-shear family: it is inhabited precisely when the transport
speed vanishes and the remaining full-drift datum degenerates. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity_iff
    {ν : ℝ} {a k b d c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearTransportFullDriftInitialVelocity a k b d c) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  constructor
  · intro hOut
    have hb : b = 0 := by
      by_contra hb
      exact not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity hb hOut
    subst hb
    have hfull :
        d = 0 ∧ c = 0 ∧ a * k = 0 := by
      exact
        (ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff
          (ν := ν) (a := a) (k := k) (d := d) (c := c)).1
          (by
            simpa [heatShearTransportFullDriftInitialVelocity_zero_transport] using hOut)
    exact ⟨rfl, hfull.1, hfull.2.1, hfull.2.2⟩
  · rintro ⟨hb, hd, hc, hak⟩
    subst hb
    simpa [heatShearTransportFullDriftInitialVelocity_zero_transport] using
      ((ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff
        (ν := ν) (a := a) (k := k) (d := d) (c := c)).2
        ⟨hd, hc, hak⟩)

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for transported full-drift heat-shear initial data on `ℝ^3`
whenever the transport speed is nonzero. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
    {ν : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearTransportFullDriftInitialVelocity a k b d c) :=
    smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
  have hdiv : ∀ x, initialSpatialDivergence (heatShearTransportFullDriftInitialVelocity a k b d c) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity hb
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- At positive viscosity, the explicit concrete regularity clause is exact on
the transported full-drift heat-shear family. -/
theorem ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k b d c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity a k b d c) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  constructor
  · intro hClause
    have hsmooth :
        smoothInitialVelocityData (heatShearTransportFullDriftInitialVelocity a k b d c) :=
      smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
    have hdiv :
        ∀ x, initialSpatialDivergence (heatShearTransportFullDriftInitialVelocity a k b d c) x = 0 := by
      intro x
      simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x
    exact
      (ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity_iff
        (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c)).1
        (hClause hν hsmooth hdiv)
  · intro hcond
    exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitConcreteNavierStokesRegularityClause
        ((ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity_iff
          (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c)).2 hcond)

/-- The same witness-level obstruction applies to transported full-drift
heat-shear data on every nonnegative slab whenever the transport speed is
nonzero. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity
    {ν T : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportFullDriftInitialVelocity a k b d c) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)
      hT

/-- On every nonnegative slab with nonnegative viscosity, the transported
full-drift heat-shear field is an exact smooth incompressible candidate with
explicit slab vorticity bound `|a * k|`; bounded kinetic energy is the only
missing witness slot. -/
theorem heatShearTransportFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a k b d c : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨heatShearTransportFullDriftVelocityField ν a k b d c, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearTransportFullDriftVelocityField ν a k b d c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simpa using momentumEquation_heatShearTransportFullDriftVelocityField_zeroPressure ν a k b d c t x
  · intro t x ht0 htT
    simpa using spatialDivergence_heatShearTransportFullDriftVelocityField ν a k b d c t x
  · exact matchesInitialVelocity_heatShearTransportFullDriftVelocityField ν a k b d c
  · exact uniformVorticityBoundUpTo_heatShearTransportFullDriftVelocityField ν a k b d c T hν
  · exact not_boundedKineticEnergyUpTo_heatShearTransportFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT

/-- Transported full-drift heat shear exposes the same exact gap on the
explicit uniform-vorticity surface: there is an exact smooth incompressible
candidate with a uniform slab vorticity bound, but the finite-time witness
type is still empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearTransportFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a k b d c : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportFullDriftInitialVelocity a k b d c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT

/-- The repaired explicit regularity clause is likewise vacuous on transported
full-drift heat-shear data with nonzero transport speed because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
    {ν : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)

/-- The repaired explicit regularity clause can therefore also be true on
transported full-drift heat-shear data with nonzero transport speed while the
unrepaired concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_without_regularity
    {ν : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      hν hb

/-- The structured fully concrete clause also rejects transported full-drift
heat-shear initial data with nonzero transport speed. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearTransportFullDriftInitialVelocity
    {ν : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportFullDriftInitialVelocity a k b d c
          smooth_initial := smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity hb
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
        hν
        (smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x)).mp
        hClause)

/-- The structured fully concrete clause is exact on the transported
full-drift heat-shear family. -/
theorem concreteNavierStokesGlobalRegularityClause_heatShearTransportFullDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k b d c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportFullDriftInitialVelocity a k b d c
          smooth_initial := smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x } ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  constructor
  · intro hClause
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
        hν
        (smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x)).mp
          hClause
        |> (ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity_iff
              (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c)).1
  · intro hcond
    exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
        hν
        (smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x)
        ((ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity_iff
          (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c)).2 hcond)

/-- The fully explicit global-output surface is exact on the transported
heat-shear family. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportInitialVelocity_iff
    {ν : ℝ} {a k b : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearTransportInitialVelocity a k b) ↔
      b = 0 ∧ a * k = 0 := by
  simpa [heatShearTransportFullDriftInitialVelocity_zero_drifts] using
    (ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity_iff
      (ν := ν) (a := a) (k := k) (b := b) (d := 0) (c := 0))

/-- At positive viscosity, the explicit concrete regularity clause is exact on
the transported heat-shear family. -/
theorem ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k b : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity a k b) ↔
      b = 0 ∧ a * k = 0 := by
  simpa [heatShearTransportFullDriftInitialVelocity_zero_drifts] using
    (ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_iff
      (ν := ν) hν (a := a) (k := k) (b := b) (d := 0) (c := 0))

/-- The structured fully concrete clause is exact on the transported
heat-shear family. -/
theorem concreteNavierStokesGlobalRegularityClause_heatShearTransportInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k b : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportInitialVelocity a k b
          smooth_initial := smoothInitialVelocityData_heatShearTransportInitialVelocity a k b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportInitialVelocity a k b x } ↔
      b = 0 ∧ a * k = 0 := by
  constructor
  · intro hClause
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearTransportInitialVelocity a k b)
        hν
        (smoothInitialVelocityData_heatShearTransportInitialVelocity a k b)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearTransportInitialVelocity a k b x)).mp
          hClause
        |> (ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportInitialVelocity_iff
              (ν := ν) (a := a) (k := k) (b := b)).1
  · intro hcond
    exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
        hν
        (smoothInitialVelocityData_heatShearTransportInitialVelocity a k b)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearTransportInitialVelocity a k b x)
        ((ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportInitialVelocity_iff
          (ν := ν) (a := a) (k := k) (b := b)).2 hcond)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for transported full-drift heat-shear initial data with nonzero
transport speed because the finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity
    {ν T : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (heatShearTransportFullDriftInitialVelocity a k b d c) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
transported full-drift heat-shear data with nonzero transport speed while the
concrete regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      hν hb

/-- The repaired uniform-vorticity continuation clause is also vacuous on
transported full-drift heat-shear data with nonzero transport speed because
the repaired finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity
    {ν T : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearTransportFullDriftInitialVelocity a k b d c) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)

/-- The repaired uniform-vorticity clause can therefore also be true on
transported full-drift heat-shear data with nonzero transport speed while the
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      hν hb

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
