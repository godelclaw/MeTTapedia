import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityBounds
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityConstantCandidates
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityEnergyObstructions
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityLinearShearEnergy
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Basic
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3LocalOperators
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Smoothness
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3FirstOrder
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3PressureObstructions
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Laplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Momentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Vorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportProfiles
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportDerivatives
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportLaplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportMomentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportVorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3VorticityNorms

/-!
# Linear-Shear Candidate Obstructions for Uniform-Vorticity Continuation

This module contains the reusable finite-energy-data exclusions, finite-time
bounded-energy obstructions, and explicit candidate mismatch lemmas for
linear-shear initial data and constant-drift variants.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Therefore the repaired structured whole-space input domain contains no
problem datum whose initial velocity is a nonzero linear shear field. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearInitialVelocity
    {a : ℝ}
    (ha : a ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearInitialVelocity a } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearInitialVelocity a)
      (not_finiteInitialKineticEnergy_linearShearInitialVelocity ha)

/-- The same repaired structured whole-space input domain contains no problem
datum whose initial velocity is the nonzero affine shear profile
`x ↦ (a * x₁, 0, b)`. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearVerticalDriftInitialVelocity
    {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearVerticalDriftInitialVelocity a b } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The same repaired structured whole-space input domain contains no problem
datum whose initial velocity is the nonzero affine shear profile
`x ↦ (a * x₁, b, 0)`. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearHorizontalDriftInitialVelocity
    {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearHorizontalDriftInitialVelocity a b } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The same repaired structured whole-space input domain contains no problem
datum whose initial velocity is the nonzero affine shear profile
`x ↦ (a * x₁, b, c)`. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearFullDriftInitialVelocity
    {a b c : ℝ}
    (ha : a ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearFullDriftInitialVelocity a b c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity
        (a := a) (b := b) (c := c) ha)

/-- Hence any nonnegative finite-time slab witness with nonzero linear shear
initial data is blocked by the bounded-energy slot, regardless of later
dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearInitialVelocity
    {u : NSVelocityField} {a : ℝ} {T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (linearShearInitialVelocity a) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearInitialVelocity
        ha hinit)
      hT

/-- The same time-zero obstruction blocks any nonnegative finite-time slab
witness matching the initial data `x ↦ (a * x₁, 0, b)`. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ} {T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
        ha hinit)
      hT

/-- The same time-zero obstruction blocks any nonnegative finite-time slab
witness matching the initial data `x ↦ (a * x₁, b, 0)`. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ} {T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
        ha hinit)
      hT

/-- The same time-zero obstruction blocks any nonnegative finite-time slab
witness matching the initial data `x ↦ (a * x₁, b, c)`. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
    {u : NSVelocityField} {a b c : ℝ} {T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
        ha hinit)
      hT

/-- The steady linear shear field is an exact smooth incompressible NS
candidate on every nonnegative slab with a uniform vorticity bound; the only
missing finite-time witness slot is bounded kinetic energy. -/
theorem linearShearVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨linearShearVelocityField a, 0, |a|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearVelocityField a
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simp [timeVelocityDerivative_linearShearVelocityField,
      spatialConvection_linearShearVelocityField,
      spatialPressureGradient_zero,
      spatialLaplacian_linearShearVelocityField]
  · intro t x ht0 htT
    exact spatialDivergence_linearShearVelocityField a t x
  · exact matchesInitialVelocity_linearShearVelocityField a
  · exact uniformVorticityBoundUpTo_linearShearVelocityField a T
  · exact not_boundedKineticEnergyUpTo_linearShearVelocityField
      (a := a) ha hT

/-- The steady field `u(t,x) = (a * x₁, 0, b)` is also an exact smooth
incompressible NS candidate on every nonnegative slab with the same uniform
vorticity bound `|a|`; the only missing finite-time witness slot is again
bounded kinetic energy. -/
theorem linearShearVerticalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨linearShearVerticalDriftVelocityField a b, 0, |a|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearVerticalDriftVelocityField a b
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simp [timeVelocityDerivative_linearShearVerticalDriftVelocityField,
      spatialConvection_linearShearVerticalDriftVelocityField,
      spatialPressureGradient_zero,
      spatialLaplacian_linearShearVerticalDriftVelocityField]
  · intro t x ht0 htT
    exact spatialDivergence_linearShearVerticalDriftVelocityField a b t x
  · exact matchesInitialVelocity_linearShearVerticalDriftVelocityField a b
  · exact uniformVorticityBoundUpTo_linearShearVerticalDriftVelocityField a b T
  · exact not_boundedKineticEnergyUpTo_linearShearVerticalDriftVelocityField
      (a := a) (b := b) ha hT

/-- The steady field `u(t,x) = (a * x₁, b, 0)` is also an exact smooth
incompressible NS candidate on every nonnegative slab with the same uniform
vorticity bound `|a|`; the only missing finite-time witness slot is again
bounded kinetic energy.  Here the nonzero convection is cancelled by the
explicit affine pressure field. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine
    ⟨linearShearHorizontalDriftVelocityField a b,
      linearShearHorizontalDriftPressureField a b, |a|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b
  · exact smoothSpaceTimePressure_linearShearHorizontalDriftPressureField a b
  · intro t x ht0 htT
    rw [timeVelocityDerivative_linearShearHorizontalDriftVelocityField,
      spatialConvection_linearShearHorizontalDriftVelocityField,
      spatialPressureGradient_linearShearHorizontalDriftPressureField,
      spatialLaplacian_linearShearHorizontalDriftVelocityField]
    ext i
    fin_cases i <;> simp [nsCoord0]
  · intro t x ht0 htT
    exact spatialDivergence_linearShearHorizontalDriftVelocityField a b t x
  · exact matchesInitialVelocity_linearShearHorizontalDriftVelocityField a b
  · exact uniformVorticityBoundUpTo_linearShearHorizontalDriftVelocityField a b T
  · exact not_boundedKineticEnergyUpTo_linearShearHorizontalDriftVelocityField
      (a := a) (b := b) ha hT

/-- The same affine-shear slab candidate remains valid after adding any smooth
slice-wise zero-spatial-gradient pressure gauge.  The bounded-energy slot on
`ℝ^3` is still the only missing witness component. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
        (ν := ν) (T := T) (a := a) (b := b) ha hT)
      q hq hq_zero

/-- Time-only special case of the horizontal affine-shear pressure-gauge
transport on the uniform-vorticity candidate surface. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addTimeOnlyPressure
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
      (ν := ν) (T := T) (a := a) (b := b) ha hT
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The steady field `u(t,x) = (a * x₁, b, c)` is also an exact smooth
incompressible NS candidate on every nonnegative slab with the same uniform
vorticity bound `|a|`; the only missing finite-time witness slot is again
bounded kinetic energy.  The vertical drift does not change the same affine
pressure cancellation already needed for the horizontal branch. -/
theorem linearShearFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a b c : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine
    ⟨linearShearFullDriftVelocityField a b c,
      linearShearHorizontalDriftPressureField a b, |a|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearFullDriftVelocityField a b c
  · exact smoothSpaceTimePressure_linearShearHorizontalDriftPressureField a b
  · intro t x ht0 htT
    rw [timeVelocityDerivative_linearShearFullDriftVelocityField,
      spatialConvection_linearShearFullDriftVelocityField,
      spatialPressureGradient_linearShearHorizontalDriftPressureField,
      spatialLaplacian_linearShearFullDriftVelocityField]
    ext i
    fin_cases i <;> simp [nsCoord0]
  · intro t x ht0 htT
    exact spatialDivergence_linearShearFullDriftVelocityField a b c t x
  · exact matchesInitialVelocity_linearShearFullDriftVelocityField a b c
  · exact uniformVorticityBoundUpTo_linearShearFullDriftVelocityField a b c T
  · exact not_boundedKineticEnergyUpTo_linearShearFullDriftVelocityField
      (a := a) (b := b) (c := c) ha hT

/-- The same obstruction rules out the global bounded-energy predicate for any
velocity field with nonzero linear shear initial data. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearInitialVelocity
    {u : NSVelocityField} {a : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearInitialVelocity a) u) :
    ¬ boundedKineticEnergy u := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearInitialVelocity
        ha hinit)

/-- The same global bounded-energy obstruction holds for the affine shear
datum `x ↦ (a * x₁, 0, b)`. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u) :
    ¬ boundedKineticEnergy u := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
        ha hinit)

/-- The same global bounded-energy obstruction holds for the affine shear
datum `x ↦ (a * x₁, b, 0)`. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u) :
    ¬ boundedKineticEnergy u := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
        ha hinit)

/-- The same global bounded-energy obstruction holds for the affine shear
datum `x ↦ (a * x₁, b, c)`. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
    {u : NSVelocityField} {a b c : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u) :
    ¬ boundedKineticEnergy u := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
        ha hinit)

/-- The steady linear shear field is already a full exact candidate on the
global explicit theorem surface; the only missing slot is bounded kinetic
energy. -/
theorem linearShearVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a : ℝ} (ha : a ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨linearShearVelocityField a, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearVelocityField a
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simp [timeVelocityDerivative_linearShearVelocityField,
      spatialConvection_linearShearVelocityField,
      spatialPressureGradient_zero,
      spatialLaplacian_linearShearVelocityField]
  · intro t x
    exact spatialDivergence_linearShearVelocityField a t x
  · exact matchesInitialVelocity_linearShearVelocityField a
  · exact not_boundedKineticEnergy_linearShearVelocityField
      (a := a) ha

/-- Linear shear therefore exhibits the exact mismatch on the global explicit
theorem surface: an honest smooth PDE-side candidate exists, but the explicit
global-output proposition is still false because bounded kinetic energy fails. -/
theorem linearShearInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a : ℝ} (ha : a ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) ha
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearInitialVelocity
        (u := u) ha hinit hbd

/-- The steady affine shear field `u(t,x) = (a * x₁, 0, b)` is likewise a full
exact candidate on the global explicit theorem surface; bounded kinetic energy
is again the only missing slot. -/
theorem linearShearVerticalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a b : ℝ} (ha : a ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨linearShearVerticalDriftVelocityField a b, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearVerticalDriftVelocityField a b
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simp [timeVelocityDerivative_linearShearVerticalDriftVelocityField,
      spatialConvection_linearShearVerticalDriftVelocityField,
      spatialPressureGradient_zero,
      spatialLaplacian_linearShearVerticalDriftVelocityField]
  · intro t x
    exact spatialDivergence_linearShearVerticalDriftVelocityField a b t x
  · exact matchesInitialVelocity_linearShearVerticalDriftVelocityField a b
  · exact not_boundedKineticEnergy_linearShearVerticalDriftVelocityField
      (a := a) (b := b) ha

/-- Affine shear therefore exhibits the same exact mismatch on the global
explicit theorem surface: an honest smooth PDE-side candidate exists, but the
explicit global-output proposition is still false because bounded kinetic
energy fails. -/
theorem linearShearVerticalDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a b : ℝ} (ha : a ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVerticalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (b := b) ha
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
        (u := u) ha hinit hbd

/-- The steady affine shear field `u(t,x) = (a * x₁, b, 0)` is likewise a full
exact candidate on the global explicit theorem surface; bounded kinetic energy
is again the only missing slot.  The pressure field is now essential rather
than zero. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a b : ℝ} (ha : a ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      ¬ boundedKineticEnergy u := by
  refine
    ⟨linearShearHorizontalDriftVelocityField a b,
      linearShearHorizontalDriftPressureField a b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b
  · exact smoothSpaceTimePressure_linearShearHorizontalDriftPressureField a b
  · intro t x
    rw [timeVelocityDerivative_linearShearHorizontalDriftVelocityField,
      spatialConvection_linearShearHorizontalDriftVelocityField,
      spatialPressureGradient_linearShearHorizontalDriftPressureField,
      spatialLaplacian_linearShearHorizontalDriftVelocityField]
    ext i
    fin_cases i <;> simp [nsCoord0]
  · intro t x
    exact spatialDivergence_linearShearHorizontalDriftVelocityField a b t x
  · exact matchesInitialVelocity_linearShearHorizontalDriftVelocityField a b
  · exact not_boundedKineticEnergy_linearShearHorizontalDriftVelocityField
      (a := a) (b := b) ha

/-- Affine shear with horizontal drift therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a b : ℝ} (ha : a ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact linearShearHorizontalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (b := b) ha
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
        (u := u) ha hinit hbd

/-- The steady affine shear field `u(t,x) = (a * x₁, b, c)` is likewise a full
exact candidate on the global explicit theorem surface; bounded kinetic energy
is again the only missing slot, and the same affine pressure already balances
the nonzero convection. -/
theorem linearShearFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a b c : ℝ} (ha : a ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      ¬ boundedKineticEnergy u := by
  refine
    ⟨linearShearFullDriftVelocityField a b c,
      linearShearHorizontalDriftPressureField a b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearFullDriftVelocityField a b c
  · exact smoothSpaceTimePressure_linearShearHorizontalDriftPressureField a b
  · intro t x
    rw [timeVelocityDerivative_linearShearFullDriftVelocityField,
      spatialConvection_linearShearFullDriftVelocityField,
      spatialPressureGradient_linearShearHorizontalDriftPressureField,
      spatialLaplacian_linearShearFullDriftVelocityField]
    ext i
    fin_cases i <;> simp [nsCoord0]
  · intro t x
    exact spatialDivergence_linearShearFullDriftVelocityField a b c t x
  · exact matchesInitialVelocity_linearShearFullDriftVelocityField a b c
  · exact not_boundedKineticEnergy_linearShearFullDriftVelocityField
      (a := a) (b := b) (c := c) ha

/-- Affine shear with full constant drift therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem linearShearFullDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a b c : ℝ} (ha : a ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact linearShearFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (b := b) (c := c) ha
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
        (u := u) ha hinit hbd


end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
