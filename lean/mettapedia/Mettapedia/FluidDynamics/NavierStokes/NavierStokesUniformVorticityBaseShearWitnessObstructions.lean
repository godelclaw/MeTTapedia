import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityBounds
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityEnergyObstructions
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearEnergyCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearFullDriftEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearStreamwiseDriftEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearVerticalDriftEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearEnergyTransport
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityLinearShearCandidates

/-!
# Base Shear Witness Obstructions for Uniform-Vorticity Continuation

This module contains the reusable finite-time witness obstructions and base
heat/linear-shear candidate-without-witness surfaces for uniform-vorticity
continuation.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The damped sinusoidal heat-shear field is likewise an honest exact
candidate on the global explicit theorem surface; the only missing slot is
bounded kinetic energy on `ℝ^3`. -/
theorem heatShearVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      ¬ boundedKineticEnergy u := by
    refine ⟨heatShearVelocityField ν a k, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact smoothSpaceTimeVelocity_heatShearVelocityField ν a k
    · exact smoothSpaceTimePressure_const (0 : ℝ)
    · intro t x
      simpa using momentumEquation_heatShearVelocityField_zeroPressure ν a k t x
    · intro t x
      simpa using spatialDivergence_heatShearVelocityField ν a k t x
    · exact matchesInitialVelocity_heatShearVelocityField ν a k
    · exact not_boundedKineticEnergy_heatShearVelocityField
        (ν := ν) (a := a) (k := k) ha hk

/-- The damped sinusoidal heat-shear field therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem heatShearInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) ha hk
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearInitialVelocity
        (u := u) ha hk hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
nontrivial heat-shear initial data, independent of any later pressure field. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearInitialVelocity
    {ν : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (heatShearInitialVelocity a k) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearInitialVelocity
      (u := u) ha hk hinit hbd

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for nontrivial heat-shear initial data on `ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity
    {ν : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity a k) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearInitialVelocity a k) :=
    smoothInitialVelocityData_heatShearInitialVelocity a k
  have hdiv : ∀ x, initialSpatialDivergence (heatShearInitialVelocity a k) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearInitialVelocity a k x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearInitialVelocity ha hk
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- Therefore the explicit finite-time witness type is uninhabited on any
nonnegative slab for nonzero linear shear initial data. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity
    {ν T : ℝ} {a : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity a) T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearInitialVelocity
      (u := W.velocity) ha hT W.initial_condition W.bounded_energy_on

/-- The same witness-level obstruction applies to the affine shear datum
`x ↦ (a * x₁, 0, b)` on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (linearShearVerticalDriftInitialVelocity a b) T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
      (u := W.velocity) ha hT W.initial_condition W.bounded_energy_on

/-- The same witness-level obstruction applies to the affine shear datum
`x ↦ (a * x₁, b, 0)` on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
      (u := W.velocity) ha hT W.initial_condition W.bounded_energy_on

/-- The same witness-level obstruction applies to the affine shear datum
`x ↦ (a * x₁, b, c)` on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity
    {ν T : ℝ} {a b c : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (linearShearFullDriftInitialVelocity a b c) T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
      (u := W.velocity) ha hT W.initial_condition W.bounded_energy_on

/-- On every nonnegative slab with nonnegative viscosity, the heat-shear field
is an exact smooth incompressible candidate with explicit slab vorticity bound
`|a * k|`; bounded kinetic energy is the only missing witness slot. -/
theorem heatShearVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
    refine ⟨heatShearVelocityField ν a k, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact smoothSpaceTimeVelocity_heatShearVelocityField ν a k
    · exact smoothSpaceTimePressure_const (0 : ℝ)
    · intro t x ht0 htT
      simpa using momentumEquation_heatShearVelocityField_zeroPressure ν a k t x
    · intro t x ht0 htT
      simpa using spatialDivergence_heatShearVelocityField ν a k t x
    · exact matchesInitialVelocity_heatShearVelocityField ν a k
    · exact uniformVorticityBoundUpTo_heatShearVelocityField ν a k T hν
    · exact not_boundedKineticEnergyUpTo_heatShearVelocityField
        (ν := ν) (a := a) (k := k) ha hk hT

/-- The same witness-level obstruction applies to the nontrivial heat-shear
datum on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity
    {ν T : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (heatShearInitialVelocity a k) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearInitialVelocity a k)
      (not_finiteInitialKineticEnergy_heatShearInitialVelocity ha hk)
      hT

/-- Heat shear exposes the same exact gap on the explicit uniform-vorticity
surface: there is an exact smooth incompressible candidate with a uniform slab
vorticity bound, but the finite-time witness type is still empty because
bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (heatShearInitialVelocity a k) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) ha hk hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk hT

/-- Linear shear exposes the exact gap on the explicit uniform-vorticity
surface: there is an exact smooth incompressible candidate with a uniform slab
vorticity bound, but the concrete finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity a) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) ha hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity
      (ν := ν) (T := T) ha hT

/-- The same explicit uniform-vorticity gap persists for the affine shear datum
`x ↦ (a * x₁, 0, b)`: an exact smooth incompressible candidate with uniform slab
vorticity bound exists, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearVerticalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearVerticalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVerticalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- The same explicit uniform-vorticity gap persists for the affine shear datum
`x ↦ (a * x₁, b, 0)`: an exact smooth incompressible candidate with uniform slab
vorticity bound exists, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- The same horizontal affine-shear gap persists after adding any smooth
slice-wise zero-spatial-gradient pressure gauge to the explicit slab
candidate. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact
      linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) (a := a) (b := b) ha hT q hq hq_zero
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- Time-only special case of the horizontal affine-shear pressure-gauge gap on
the explicit uniform-vorticity continuation surface. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addTimeOnlyPressure
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
      (ν := ν) (T := T) (a := a) (b := b) ha hT
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The same explicit uniform-vorticity gap persists for the affine shear datum
`x ↦ (a * x₁, b, c)`: an exact smooth incompressible candidate with uniform slab
vorticity bound exists, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a b c : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearFullDriftInitialVelocity a b c) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT


end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
